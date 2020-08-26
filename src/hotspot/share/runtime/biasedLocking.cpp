/*
 * Copyright (c) 2005, 2018, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 *
 */

#include "precompiled.hpp"
#include "jfr/jfrEvents.hpp"
#include "jfr/support/jfrThreadId.hpp"
#include "logging/log.hpp"
#include "memory/resourceArea.hpp"
#include "oops/klass.inline.hpp"
#include "oops/markOop.hpp"
#include "oops/oop.inline.hpp"
#include "runtime/atomic.hpp"
#include "runtime/basicLock.hpp"
#include "runtime/biasedLocking.hpp"
#include "runtime/handles.inline.hpp"
#include "runtime/task.hpp"
#include "runtime/threadSMR.hpp"
#include "runtime/vframe.hpp"
#include "runtime/vmThread.hpp"
#include "runtime/vmOperations.hpp"


static bool _biased_locking_enabled = false;
BiasedLockingCounters BiasedLocking::_counters;

static GrowableArray<Handle>*  _preserved_oop_stack  = NULL;
static GrowableArray<markOop>* _preserved_mark_stack = NULL;

static void enable_biased_locking(InstanceKlass* k) {
  k->set_prototype_header(markOopDesc::biased_locking_prototype());
}

class VM_EnableBiasedLocking: public VM_Operation {
 private:
  bool _is_cheap_allocated;
 public:
  VM_EnableBiasedLocking(bool is_cheap_allocated) { _is_cheap_allocated = is_cheap_allocated; }
  VMOp_Type type() const          { return VMOp_EnableBiasedLocking; }
  Mode evaluation_mode() const    { return _is_cheap_allocated ? _async_safepoint : _safepoint; }
  bool is_cheap_allocated() const { return _is_cheap_allocated; }

  void doit() {
    // Iterate the class loader data dictionaries enabling biased locking for all
    // currently loaded classes.
    ClassLoaderDataGraph::dictionary_classes_do(enable_biased_locking);
    // Indicate that future instances should enable it as well
    _biased_locking_enabled = true;

    log_info(biasedlocking)("Biased locking enabled");
  }

  bool allow_nested_vm_operations() const        { return false; }
};


// One-shot PeriodicTask subclass for enabling biased locking
class EnableBiasedLockingTask : public PeriodicTask {
 public:
  EnableBiasedLockingTask(size_t interval_time) : PeriodicTask(interval_time) {}

  virtual void task() {
    // Use async VM operation to avoid blocking the Watcher thread.
    // VM Thread will free C heap storage.
    VM_EnableBiasedLocking *op = new VM_EnableBiasedLocking(true);
    VMThread::execute(op);

    // Reclaim our storage and disenroll ourself
    delete this;
  }
};


void BiasedLocking::init() {
  // If biased locking is enabled, schedule a task to fire a few
  // seconds into the run which turns on biased locking for all
  // currently loaded classes as well as future ones. This is a
  // workaround for startup time regressions due to a large number of
  // safepoints being taken during VM startup for bias revocation.
  // Ideally we would have a lower cost for individual bias revocation
  // and not need a mechanism like this.
  if (UseBiasedLocking) {
    if (BiasedLockingStartupDelay > 0) {
      EnableBiasedLockingTask* task = new EnableBiasedLockingTask(BiasedLockingStartupDelay);
      task->enroll();
    } else {
      VM_EnableBiasedLocking op(false);
      VMThread::execute(&op);
    }
  }
}


bool BiasedLocking::enabled() {
  return _biased_locking_enabled;
}

// Returns MonitorInfos for all objects locked on this thread in youngest to oldest order
static GrowableArray<MonitorInfo*>* get_or_compute_monitor_info(JavaThread* thread) {
  GrowableArray<MonitorInfo*>* info = thread->cached_monitor_info();
  if (info != NULL) {
    return info;
  }

  info = new GrowableArray<MonitorInfo*>();

  // It's possible for the thread to not have any Java frames on it,
  // i.e., if it's the main thread and it's already returned from main()
  if (thread->has_last_Java_frame()) {
    RegisterMap rm(thread);
    for (javaVFrame* vf = thread->last_java_vframe(&rm); vf != NULL; vf = vf->java_sender()) {
      GrowableArray<MonitorInfo*> *monitors = vf->monitors();
      if (monitors != NULL) {
        int len = monitors->length();
        // Walk monitors youngest to oldest
        for (int i = len - 1; i >= 0; i--) {
          MonitorInfo* mon_info = monitors->at(i);
          if (mon_info->eliminated()) continue;
          oop owner = mon_info->owner();
          if (owner != NULL) {
            info->append(mon_info);
          }
        }
      }
    }
  }

  thread->set_cached_monitor_info(info);
  return info;
}

// allow_rebias: 是否允许重偏向. VM_RevokeBias::doit_prologue以及BiasedLocking::revoke_and_rebias都传入了false
// After the call, *biased_locker will be set to obj->mark()->biased_locker() if biased_locker != NULL,
// AND it is a living thread. Otherwise it will not be updated, (i.e. the caller is responsible for initialization).
static BiasedLocking::Condition revoke_bias(oop obj, bool allow_rebias, bool is_bulk, JavaThread* requesting_thread, JavaThread** biased_locker) {
  //  获取对象头
  markOop mark = obj->mark();
  //  不是可偏向状态，返回
  if (!mark->has_bias_pattern()) {
    if (log_is_enabled(Info, biasedlocking)) {
      ResourceMark rm;
      log_info(biasedlocking)("  (Skipping revocation of object " INTPTR_FORMAT
                              ", mark " INTPTR_FORMAT ", type %s"
                              ", requesting thread " INTPTR_FORMAT
                              " because it's no longer biased)",
                              p2i((void *)obj), (intptr_t) mark,
                              obj->klass()->external_name(),
                              (intptr_t) requesting_thread);
    }
    return BiasedLocking::NOT_BIASED;
  }

  uint age = mark->age();
  //新建匿名偏向模式(可偏向)的头：分代年龄为age、可偏向(101)状态
  markOop   biased_prototype = markOopDesc::biased_locking_prototype()->set_age(age);
  //新建无锁模式的头:无hash、分代年龄为age、无锁(001)状态
  markOop unbiased_prototype = markOopDesc::prototype()->set_age(age);

  // Log at "info" level if not bulk, else "trace" level
  if (!is_bulk) {
    ResourceMark rm;
    log_info(biasedlocking)("Revoking bias of object " INTPTR_FORMAT ", mark "
                            INTPTR_FORMAT ", type %s, prototype header " INTPTR_FORMAT
                            ", allow rebias %d, requesting thread " INTPTR_FORMAT,
                            p2i((void *)obj),
                            (intptr_t) mark,
                            obj->klass()->external_name(),
                            (intptr_t) obj->klass()->prototype_header(),
                            (allow_rebias ? 1 : 0),
                            (intptr_t) requesting_thread);
  } else {
    ResourceMark rm;
    log_trace(biasedlocking)("Revoking bias of object " INTPTR_FORMAT " , mark "
                             INTPTR_FORMAT " , type %s , prototype header " INTPTR_FORMAT
                             " , allow rebias %d , requesting thread " INTPTR_FORMAT,
                             p2i((void *)obj),
                             (intptr_t) mark,
                             obj->klass()->external_name(),
                             (intptr_t) obj->klass()->prototype_header(),
                             (allow_rebias ? 1 : 0),
                             (intptr_t) requesting_thread);
  }

  //获取对象当前偏向的线程
  JavaThread* biased_thread = mark->biased_locker();
  if (biased_thread == NULL) {
    //  case 1: 没有偏向线程，identity hash code的计算会导致进入此分支
    // Object is anonymously biased. We can get here if, for
    // example, we revoke the bias due to an identity hash code
    // being computed for an object.
    if (!allow_rebias) {
      //  设置对象头为前面构建的无锁模式的头:无hash、分代年龄为age、无锁(001)状态
      obj->set_mark(unbiased_prototype);
    }
    // Log at "info" level if not bulk, else "trace" level
    if (!is_bulk) {
      log_info(biasedlocking)("  Revoked bias of anonymously-biased object");
    } else {
      log_trace(biasedlocking)("  Revoked bias of anonymously-biased object");
    }
    //  偏向锁撤销完成
    return BiasedLocking::BIAS_REVOKED;
  }

  // Handle case where the thread toward which the object was biased has exited
  bool thread_is_alive = false; //对象头偏向线程是否活着
  if (requesting_thread == biased_thread) {
    //当前请求线程 就是 对象头偏向线程，说明偏向线程活着
    thread_is_alive = true;
  } else {
    //  遍历存活线程队列，看看能不能找到对象头偏向线程,
    //  能找到说明对象头的偏向线程活着.
    ThreadsListHandle tlh;
    thread_is_alive = tlh.includes(biased_thread);
  }
  // case 2: 对象当前偏向的线程已经退出了.
  // 如果对象头偏向线程已退出，则撤销偏向锁
  if (!thread_is_alive) {
    if (allow_rebias) {
      // 如果允许重偏向
      // 设置匿名偏向模式(可偏向)的头：分代年龄为age、可偏向(101)状态
      obj->set_mark(biased_prototype);
    } else {
      // 如果不允许重偏向,
      // 设置无锁模式的头:无hash、分代年龄为age、无锁(001)状态
      obj->set_mark(unbiased_prototype);
    }
    // Log at "info" level if not bulk, else "trace" level
    if (!is_bulk) {
      log_info(biasedlocking)("  Revoked bias of object biased toward dead thread ("
                              PTR_FORMAT ")", p2i(biased_thread));
    } else {
      log_trace(biasedlocking)("  Revoked bias of object biased toward dead thread ("
                               PTR_FORMAT ")", p2i(biased_thread));
    }
    //  偏向锁撤销完成
    return BiasedLocking::BIAS_REVOKED;
  }

  // Log at "info" level if not bulk, else "trace" level
  if (!is_bulk) {
    log_info(biasedlocking)("  Revoked bias of object biased toward live thread ("
                            PTR_FORMAT ")", p2i(biased_thread));
  } else {
    log_trace(biasedlocking)("  Revoked bias of object biased toward live thread ("
                               PTR_FORMAT ")", p2i(biased_thread));
  }

  // case 3: 对象当前偏向的线程依然存活.
  // 注释解释了逻辑：
  // Thread owning bias is alive.
  // Check to see whether it currently owns the lock and, if so,
  // write down the needed displaced headers to the thread's stack.
  // Otherwise, restore the object's header either to the unlocked
  // or unbiased state.
  // get_or_compute_monitor_info返回对象头偏向线程的所有的被锁住的对象的监视器信息，
  // 即线程栈所有的Lock Record.
  GrowableArray<MonitorInfo*>* cached_monitor_info = get_or_compute_monitor_info(biased_thread);
  BasicLock* highest_lock = NULL;
  // 遍历偏向线程的线程栈的所有Lock Record，寻找当前被锁对象(obj)对应的Lock Record，
  // 若找到，说明偏向的线程还在执行同步代码块中的代码，需要进行锁膨胀.
  for (int i = 0; i < cached_monitor_info->length(); i++) {
    MonitorInfo* mon_info = cached_monitor_info->at(i);
    if (oopDesc::equals(mon_info->owner(), obj)) {  // 找到了
      log_trace(biasedlocking)("   mon_info->owner (" PTR_FORMAT ") == obj (" PTR_FORMAT ")",
                               p2i((void *) mon_info->owner()),
                               p2i((void *) obj));
      // 需要锁膨胀，直接修改偏向线程栈中的Lock Record。
      // 由于要处理锁重入的case，在这里暂时只将Lock Record的Displaced Mark Word设置为null，
      // 其余处理Lock Record会在下面的代码中再进行
      // Assume recursive case and fix up highest lock later
      markOop mark = markOopDesc::encode((BasicLock*) NULL);
      highest_lock = mon_info->lock();
      // 设置栈中的Displaced Mark Word为NULL
      highest_lock->set_displaced_header(mark);
    } else {
      log_trace(biasedlocking)("   mon_info->owner (" PTR_FORMAT ") != obj (" PTR_FORMAT ")",
                               p2i((void *) mon_info->owner()),
                               p2i((void *) obj));
    }
  }
  //  如果上面的过程找到了displaced_header，则highest_lock不为空
  //  说明当前撤销偏向的对象正在被偏向头里的线程锁定，即还在同步块中，
  //  进入下面分支，对正在被锁定的对象进行偏向锁撤销
  if (highest_lock != NULL) {
    // Fix up highest lock to contain displaced header and point
    // object at it
    // 如上面注释所言，用unbiased_prototype重新设置线程栈上的displaced header
    highest_lock->set_displaced_header(unbiased_prototype);
    // Reset object header to point to displaced mark.
    // Must release storing the lock address for platforms without TSO
    // ordering (e.g. ppc).
    // 使对象头(mark)指向这个displaced header
    obj->release_set_mark(markOopDesc::encode(highest_lock));
    assert(!obj->mark()->has_bias_pattern(), "illegal mark state: stack lock used bias bit");
    // Log at "info" level if not bulk, else "trace" level
    if (!is_bulk) {
      log_info(biasedlocking)("  Revoked bias of currently-locked object");
    } else {
      log_trace(biasedlocking)("  Revoked bias of currently-locked object");
    }
    // 对正在被锁定的对象进行偏向锁撤销完成，并没有改变对象头的锁状态，而是回到fast_enter继续锁膨胀过程
  } else {
    //  如果上面的过程没找displaced_header，说明当前撤销偏向锁
    //  的对象目前没有被锁定，即已经不在同步块中了，
    //  进入这个分支，对未锁定对象进行偏向撤销
    // Log at "info" level if not bulk, else "trace" level
    if (!is_bulk) {
      log_info(biasedlocking)("  Revoked bias of currently-unlocked object");
    } else {
      log_trace(biasedlocking)("  Revoked bias of currently-unlocked object");
    }
    if (allow_rebias) {
      // 如果允许重偏向
      // 设置为匿名偏向状态
      obj->set_mark(biased_prototype);
    } else {
      // 如果不允许重偏向
      // 设置为无锁状态
      // Store the unlocked value into the object's header.
      obj->set_mark(unbiased_prototype);
      //对未锁定对象进行偏向锁撤销完成，也表明对象成为了无锁模式:无hash、分代年龄为age、无锁(001)状态
    }
  }

  // If requested, return information on which thread held the bias
  if (biased_locker != NULL) {
    *biased_locker = biased_thread;
  }

  //  偏向撤销完成
  return BiasedLocking::BIAS_REVOKED;
}


enum HeuristicsResult {
  HR_NOT_BIASED    = 1,
  HR_SINGLE_REVOKE = 2,
  HR_BULK_REBIAS   = 3,
  HR_BULK_REVOKE   = 4
};


// 启发式的方式决定要做哪种操作
static HeuristicsResult update_heuristics(oop o, bool allow_rebias) {
  markOop mark = o->mark();
  if (!mark->has_bias_pattern()) {
    // 不可偏向直接返回
    return HR_NOT_BIASED;
  }

  // 控制撤销的次数
  // Heuristics to attempt to throttle the number of revocations.
  // Stages:
  // 1. Revoke the biases of all objects in the heap of this type,
  //    but allow rebiasing of those objects if unlocked.
  // 2. Revoke the biases of all objects in the heap of this type
  //    and don't allow rebiasing of these objects. Disable
  //    allocation of objects of that type with the bias bit set.
  Klass* k = o->klass();                  // 锁对象的类
  jlong cur_time = os::javaTimeMillis();  // 当前时间
  jlong last_bulk_revocation_time = k->last_biased_lock_bulk_revocation_time(); // 该类上一次批量撤销的时间
  int revocation_count = k->biased_lock_revocation_count();                     // 该类偏向锁撤销的次数
  // 定义在globs.hpp,
  // BiasedLockingBulkRebiasThreshold(重偏向阈值,默认值为20),
  // BiasedLockingBulkRevokeThreshold(批量撤销阈值,默认值为40),
  // BiasedLockingDecayTime(开启一次新的批量重偏向距离上次批量重偏向的后的延迟时间,默认值为25000,
  // 也就是开启批量重偏向后，经过了一段较长的时间（>=BiasedLockingDecayTime），撤销计数器才超过阈值，那我们会重置计数器。),
  // 这些值可通过JVM启动参数改变
  if ((revocation_count >= BiasedLockingBulkRebiasThreshold) &&
      (revocation_count <  BiasedLockingBulkRevokeThreshold) &&
      (last_bulk_revocation_time != 0) &&
      (cur_time - last_bulk_revocation_time >= BiasedLockingDecayTime)) {
    // This is the first revocation we've seen in a while of an
    // object of this type since the last time we performed a bulk
    // rebiasing operation. The application is allocating objects in
    // bulk which are biased toward a thread and then handing them
    // off to another thread. We can cope with this allocation
    // pattern via the bulk rebiasing mechanism so we reset the
    // klass's revocation count rather than allow it to increase
    // monotonically. If we see the need to perform another bulk
    // rebias operation later, we will, and if subsequently we see
    // many more revocation operations in a short period of time we
    // will completely disable biasing for this type.
    // 在执行了一定时间之内，执行的撤销次数没有超过阈值，
    // 那么认为可以优先执行bulk rebias,因此将计数回归原始值
    k->set_biased_lock_revocation_count(0);
    revocation_count = 0;
  }

  // 对执行撤销的次数进行计数
  // Make revocation count saturate just beyond BiasedLockingBulkRevokeThreshold
  if (revocation_count <= BiasedLockingBulkRevokeThreshold) {
    revocation_count = k->atomic_incr_biased_lock_revocation_count();
  }

  // 如果达到批量撤销阈值则返回HR_BULK_REVOKE，执行bulk revoke
  if (revocation_count == BiasedLockingBulkRevokeThreshold) {
    return HR_BULK_REVOKE;
  }

  // 如果达到批量重偏向阈值则返回HR_BULK_REBIAS，执行bulk rebias
  if (revocation_count == BiasedLockingBulkRebiasThreshold) {
    return HR_BULK_REBIAS;
  }

  // 默认(fall back)执行单个对象的锁撤销
  return HR_SINGLE_REVOKE;
}


static BiasedLocking::Condition bulk_revoke_or_rebias_at_safepoint(oop o,
                                                                   bool bulk_rebias,
                                                                   bool attempt_rebias_of_object,
                                                                   JavaThread* requesting_thread) {
  assert(SafepointSynchronize::is_at_safepoint(), "must be done at safepoint");

  log_info(biasedlocking)("* Beginning bulk revocation (kind == %s) because of object "
                          INTPTR_FORMAT " , mark " INTPTR_FORMAT " , type %s",
                          (bulk_rebias ? "rebias" : "revoke"),
                          p2i((void *) o),
                          (intptr_t) o->mark(),
                          o->klass()->external_name());

  jlong cur_time = os::javaTimeMillis();
  o->klass()->set_last_biased_lock_bulk_revocation_time(cur_time);


  Klass* k_o = o->klass();
  Klass* klass = k_o;

  {
    JavaThreadIteratorWithHandle jtiwh;

    if (bulk_rebias) {
      // Use the epoch in the klass of the object to implicitly revoke
      // all biases of objects of this data type and force them to be
      // reacquired. However, we also need to walk the stacks of all
      // threads and update the headers of lightweight locked objects
      // with biases to have the current epoch.

      // If the prototype header doesn't have the bias pattern, don't
      // try to update the epoch -- assume another VM operation came in
      // and reset the header to the unbiased state, which will
      // implicitly cause all existing biases to be revoked
      // 批量重偏向的逻辑
      if (klass->prototype_header()->has_bias_pattern()) {
        // 备份自增前类中的的epoch
        int prev_epoch = klass->prototype_header()->bias_epoch();
        // 类中的epoch自增
        klass->set_prototype_header(klass->prototype_header()->incr_bias_epoch());
        int cur_epoch = klass->prototype_header()->bias_epoch();

        // 遍历所有线程的栈，更新类型为该klass的所有锁实例的epoch
        // Now walk all threads' stacks and adjust epochs of any biased
        // and locked objects of this data type we encounter
        for (; JavaThread *thr = jtiwh.next(); ) {
          GrowableArray<MonitorInfo*>* cached_monitor_info = get_or_compute_monitor_info(thr);
          for (int i = 0; i < cached_monitor_info->length(); i++) {
            MonitorInfo* mon_info = cached_monitor_info->at(i);
            oop owner = mon_info->owner();
            markOop mark = owner->mark();
            if ((owner->klass() == k_o) && mark->has_bias_pattern()) {
              // We might have encountered this object already in the case of recursive locking
              assert(mark->bias_epoch() == prev_epoch || mark->bias_epoch() == cur_epoch, "error in bias epoch adjustment");
              owner->set_mark(mark->set_bias_epoch(cur_epoch));
            }
          }
        }
      }

      // 接下来对当前锁对象进行重偏向
      // At this point we're done. All we have to do is potentially
      // adjust the header of the given object to revoke its bias.
      revoke_bias(o, attempt_rebias_of_object && klass->prototype_header()->has_bias_pattern(), true, requesting_thread, NULL);
    } else {
      if (log_is_enabled(Info, biasedlocking)) {
        ResourceMark rm;
        log_info(biasedlocking)("* Disabling biased locking for type %s", klass->external_name());
      }

      // 批量撤销的逻辑，将类中的偏向标记关闭，markOopDesc::prototype()返回的是一个关闭偏向模式的prototype
      // Disable biased locking for this data type. Not only will this
      // cause future instances to not be biased, but existing biased
      // instances will notice that this implicitly caused their biases
      // to be revoked.
      klass->set_prototype_header(markOopDesc::prototype());

      // 遍历所有线程的栈，撤销该类所有锁的偏向
      // Now walk all threads' stacks and forcibly revoke the biases of
      // any locked and biased objects of this data type we encounter.
      for (; JavaThread *thr = jtiwh.next(); ) {
        GrowableArray<MonitorInfo*>* cached_monitor_info = get_or_compute_monitor_info(thr);
        for (int i = 0; i < cached_monitor_info->length(); i++) {
          MonitorInfo* mon_info = cached_monitor_info->at(i);
          oop owner = mon_info->owner();
          markOop mark = owner->mark();
          if ((owner->klass() == k_o) && mark->has_bias_pattern()) {
            revoke_bias(owner, false, true, requesting_thread, NULL);
          }
        }
      }

      // 撤销当前锁对象的偏向模式
      // Must force the bias of the passed object to be forcibly revoked
      // as well to ensure guarantees to callers
      revoke_bias(o, false, true, requesting_thread, NULL);
    }
  } // ThreadsListHandle is destroyed here.

  log_info(biasedlocking)("* Ending bulk revocation");

  BiasedLocking::Condition status_code = BiasedLocking::BIAS_REVOKED;

  if (attempt_rebias_of_object &&
      o->mark()->has_bias_pattern() &&
      klass->prototype_header()->has_bias_pattern()) {
    // 构造一个偏向请求线程的mark word
    markOop new_mark = markOopDesc::encode(requesting_thread, o->mark()->age(),
                                           klass->prototype_header()->bias_epoch());
    // 更新当前锁对象的mark word
    o->set_mark(new_mark);
    status_code = BiasedLocking::BIAS_REVOKED_AND_REBIASED;
    log_info(biasedlocking)("  Rebiased object toward thread " INTPTR_FORMAT, (intptr_t) requesting_thread);
  }

  assert(!o->mark()->has_bias_pattern() ||
         (attempt_rebias_of_object && (o->mark()->biased_locker() == requesting_thread)),
         "bug in bulk bias revocation");

  return status_code;
}


static void clean_up_cached_monitor_info() {
  // Walk the thread list clearing out the cached monitors
  for (JavaThreadIteratorWithHandle jtiwh; JavaThread *thr = jtiwh.next(); ) {
    thr->set_cached_monitor_info(NULL);
  }
}

//  VM_RevokeBias继承了VM_Operation
//  并重写了doit_prologue()和doit()两个虚函数
class VM_RevokeBias : public VM_Operation {
protected:
  Handle* _obj;
  GrowableArray<Handle>* _objs;
  JavaThread* _requesting_thread;
  BiasedLocking::Condition _status_code;
  traceid _biased_locker_id;

public:
  VM_RevokeBias(Handle* obj, JavaThread* requesting_thread)
    : _obj(obj)
    , _objs(NULL)
    , _requesting_thread(requesting_thread)
    , _status_code(BiasedLocking::NOT_BIASED)
    , _biased_locker_id(0) {}

  VM_RevokeBias(GrowableArray<Handle>* objs, JavaThread* requesting_thread)
    : _obj(NULL)
    , _objs(objs)
    , _requesting_thread(requesting_thread)
    , _status_code(BiasedLocking::NOT_BIASED)
    , _biased_locker_id(0) {}

  virtual VMOp_Type type() const { return VMOp_RevokeBias; }

  // 如vm_operations.hpp注释描述的，若返回false则取消该VM操作
  virtual bool doit_prologue() {
    //  若被锁对象不为空，则返回true继续后续逻辑即通过evaluate()回调doit()
    // Verify that there is actual work to do since the callers just
    // give us locked object(s). If we don't find any biased objects
    // there is nothing to do and we avoid a safepoint.
    if (_obj != NULL) {
      markOop mark = (*_obj)()->mark();
      if (mark->has_bias_pattern()) {
        return true;
      }
    } else {
      //  遍历被锁对象，若存在可偏向状态，返回true继续后续逻辑即通过evaluate()回调doit()
      for ( int i = 0 ; i < _objs->length(); i++ ) {
        markOop mark = (_objs->at(i))()->mark();
        if (mark->has_bias_pattern()) {
          return true;
        }
      }
    }
    // 没有可偏向状态，返回true继续后续逻辑即通过evaluate()回调doit()
    return false;
  }

  virtual void doit() {
    if (_obj != NULL) { //  被锁对象不为空
      log_info(biasedlocking)("Revoking bias with potentially per-thread safepoint:");
      JavaThread* biased_locker = NULL;
      // 调用revoke_bias, 注意第一个参数为被锁对象，第2、3个参数为都为false
      _status_code = revoke_bias((*_obj)(), false, false, _requesting_thread, &biased_locker);
      if (biased_locker != NULL) {
        _biased_locker_id = JFR_THREAD_ID(biased_locker);
      }
      clean_up_cached_monitor_info();
      return;
    } else {
      log_info(biasedlocking)("Revoking bias with global safepoint:");
      BiasedLocking::revoke_at_safepoint(_objs);
    }
  }

  BiasedLocking::Condition status_code() const {
    return _status_code;
  }

  traceid biased_locker() const {
    return _biased_locker_id;
  }
};


class VM_BulkRevokeBias : public VM_RevokeBias {
private:
  bool _bulk_rebias;
  bool _attempt_rebias_of_object;

public:
  VM_BulkRevokeBias(Handle* obj, JavaThread* requesting_thread,
                    bool bulk_rebias,
                    bool attempt_rebias_of_object)
    : VM_RevokeBias(obj, requesting_thread)
    , _bulk_rebias(bulk_rebias)
    , _attempt_rebias_of_object(attempt_rebias_of_object) {}

  virtual VMOp_Type type() const { return VMOp_BulkRevokeBias; }
  virtual bool doit_prologue()   { return true; }

  virtual void doit() {
    _status_code = bulk_revoke_or_rebias_at_safepoint((*_obj)(), _bulk_rebias, _attempt_rebias_of_object, _requesting_thread);
    clean_up_cached_monitor_info();
  }
};

template <typename E>
static void set_safepoint_id(E* event) {
  assert(event != NULL, "invariant");
  // Subtract 1 to match the id of events committed inside the safepoint
  event->set_safepointId(SafepointSynchronize::safepoint_counter() - 1);
}

static void post_self_revocation_event(EventBiasedLockSelfRevocation* event, Klass* k) {
  assert(event != NULL, "invariant");
  assert(k != NULL, "invariant");
  assert(event->should_commit(), "invariant");
  event->set_lockClass(k);
  event->commit();
}

static void post_revocation_event(EventBiasedLockRevocation* event, Klass* k, VM_RevokeBias* revoke) {
  assert(event != NULL, "invariant");
  assert(k != NULL, "invariant");
  assert(revoke != NULL, "invariant");
  assert(event->should_commit(), "invariant");
  event->set_lockClass(k);
  set_safepoint_id(event);
  event->set_previousOwner(revoke->biased_locker());
  event->commit();
}

static void post_class_revocation_event(EventBiasedLockClassRevocation* event, Klass* k, bool disabled_bias) {
  assert(event != NULL, "invariant");
  assert(k != NULL, "invariant");
  assert(event->should_commit(), "invariant");
  event->set_revokedClass(k);
  event->set_disableBiasing(disabled_bias);
  set_safepoint_id(event);
  event->commit();
}

// 撤销或者重偏向
// obj: 被锁对象(lockee)
// attempt_rebias: 是否允许重偏向,InterpreterRuntime::monitorenter中传入了false.
BiasedLocking::Condition BiasedLocking::revoke_and_rebias(Handle obj, bool attempt_rebias, TRAPS) {
  assert(!SafepointSynchronize::is_at_safepoint(), "must not be called while at safepoint");  // 必须在安全点

  // We can revoke the biases of anonymously-biased objects
  // efficiently enough that we should not cause these revocations to
  // update the heuristics because doing so may cause unwanted bulk
  // revocations (which are expensive) to occur.
  markOop mark = obj->mark(); // 读取对象头
  if (mark->is_biased_anonymously() && !attempt_rebias) {
    // case 1:如果是匿名偏向且attempt_rebias==false会走到这里，如锁对象的hashcode方法被调用会出现这种情况，需要撤销偏向锁。
    // We are probably trying to revoke the bias of this object due to
    // an identity hash code computation. Try to revoke the bias
    // without a safepoint. This is possible if we can successfully
    // compare-and-exchange an unbiased header into the mark word of
    // the object, meaning that no other thread has raced to acquire
    // the bias of the object.
    markOop biased_value       = mark;
    // 创建一个非偏向的markword
    markOop unbiased_prototype = markOopDesc::prototype()->set_age(mark->age());
    // 通过cas重新设置偏向锁状态
    markOop res_mark = obj->cas_set_mark(unbiased_prototype, mark);
    // 如果CAS成功，返回"偏向锁撤销"状态
    if (res_mark == biased_value) {
      return BIAS_REVOKED;
    }
  } else if (mark->has_bias_pattern()) {
    // case 2: 锁对象开启了偏向模式会走到这里
    Klass* k = obj->klass();
    markOop prototype_header = k->prototype_header();
    if (!prototype_header->has_bias_pattern()) {  // case 2.1: 如果对应class的prototype_header关闭了偏向模式，则进行取消偏向锁操作
      // This object has a stale bias from before the bulk revocation
      // for this data type occurred. It's pointless to update the
      // heuristics at this point so simply update the header with a
      // CAS. If we fail this race, the object's bias has been revoked
      // by another thread so we simply return and let the caller deal
      // with it.
      markOop biased_value       = mark;
      // CAS 更新对象头markword为非偏向锁
      markOop res_mark = obj->cas_set_mark(prototype_header, mark);
      assert(!obj->mark()->has_bias_pattern(), "even if we raced, should still be revoked");
      return BIAS_REVOKED;
    } else if (prototype_header->bias_epoch() != mark->bias_epoch()) {  // case 2.2: 如果epoch过期
      // The epoch of this biasing has expired indicating that the
      // object is effectively unbiased. Depending on whether we need
      // to rebias or revoke the bias of this object we can do it
      // efficiently enough with a CAS that we shouldn't update the
      // heuristics. This is normally done in the assembly code but we
      // can reach this point due to various points in the runtime
      // needing to revoke biases.
      if (attempt_rebias) { // 如果允许尝试重新偏向
        assert(THREAD->is_Java_thread(), "");
        markOop biased_value       = mark;
        // 构建新的偏向本线程的markOop，设置好本线程的 ThreadID 、分代年龄、epoch值
        markOop rebiased_prototype = markOopDesc::encode((JavaThread*) THREAD, mark->age(), prototype_header->bias_epoch());
        // 通过CAS 操作， 将尝试新markOop写入对象头中
        markOop res_mark = obj->cas_set_mark(rebiased_prototype, mark);
        // CAS成功，则返回撤销和重新偏向状态
        if (res_mark == biased_value) {
          return BIAS_REVOKED_AND_REBIASED;
        }
      } else {
        // 不允许重新偏向，则取消偏向锁
        markOop biased_value       = mark;
        markOop unbiased_prototype = markOopDesc::prototype()->set_age(mark->age());
        markOop res_mark = obj->cas_set_mark(unbiased_prototype, mark);
        // 如果CAS操作成功，返回偏向锁撤销状态
        if (res_mark == biased_value) {
          return BIAS_REVOKED;
        }
      }
    }
  }

  // case 3: 批量重偏向与批量撤销的逻辑,重点!!!
  //重偏向与撤销的逻辑
  //通过启发式的方式决定到底是执行撤销还是执行重偏向
  HeuristicsResult heuristics = update_heuristics(obj(), attempt_rebias);
  if (heuristics == HR_NOT_BIASED) {            // 决定不偏向
    return NOT_BIASED;
  } else if (heuristics == HR_SINGLE_REVOKE) {  // 决定撤销单个线程
    Klass *k = obj->klass();
    markOop prototype_header = k->prototype_header();
    if (mark->biased_locker() == THREAD &&
        prototype_header->bias_epoch() == mark->bias_epoch()) {
      // 需要撤销的是偏向当前线程的锁，当调用Object#hashcode方法时会走到这一步.
      // 因为只要遍历当前线程的栈就好了，所以不需要等到safepoint再撤销.
      // A thread is trying to revoke the bias of an object biased
      // toward it, again likely due to an identity hash code
      // computation. We can again avoid a safepoint in this case
      // since we are only going to walk our own stack. There are no
      // races with revocations occurring in other threads because we
      // reach no safepoints in the revocation path.
      // Also check the epoch because even if threads match, another thread
      // can come in with a CAS to steal the bias of an object that has a
      // stale epoch.
      ResourceMark rm;
      log_info(biasedlocking)("Revoking bias by walking my own stack:");
      EventBiasedLockSelfRevocation event;
      // 直接调用revoke_bias撤销偏向锁
      BiasedLocking::Condition cond = revoke_bias(obj(), false, false, (JavaThread*) THREAD, NULL);
      ((JavaThread*) THREAD)->set_cached_monitor_info(NULL);
      assert(cond == BIAS_REVOKED, "why not?");
      if (event.should_commit()) {
        post_self_revocation_event(&event, k);
      }
      return cond;
    } else {
      // 下面代码最终会在VM Thread中的safepoint调用revoke_bias方法.
      // 关于VM Thread这里介绍下：在JVM中有个专门的VM Thread，
      // 该线程会源源不断的从VMOperationQueue中取出请求，比如GC请求.
      // 对于需要safepoint的操作（VM_Operationevaluate_at_safepoint返回true）
      // 必须要等到所有的Java线程进入到safepoint才开始执行.
      EventBiasedLockRevocation event;
      // VM_RevokeBias继承了VM_Operation
      // 并重写了doit_prologue()和doit()两个虚函数,
      // 其中doti()调用了revoke方法.
      VM_RevokeBias revoke(&obj, (JavaThread*) THREAD);
      // 提交运行,
      // 这样在在VM Thread中的safepoint,
      // 就会通过回调doti()调用revoke_bias方法了
      VMThread::execute(&revoke);
      if (event.should_commit() && revoke.status_code() != NOT_BIASED) {
        post_revocation_event(&event, k, &revoke);
      }
      return revoke.status_code();
    }
  }

  // case 4: 批量撤销、批量重偏向的逻辑
  assert((heuristics == HR_BULK_REVOKE) ||
         (heuristics == HR_BULK_REBIAS), "?");
  EventBiasedLockClassRevocation event;
  VM_BulkRevokeBias bulk_revoke(&obj, (JavaThread*) THREAD,
                                (heuristics == HR_BULK_REBIAS),
                                attempt_rebias);
  VMThread::execute(&bulk_revoke);
  if (event.should_commit()) {
    post_class_revocation_event(&event, obj->klass(), heuristics != HR_BULK_REBIAS);
  }
  return bulk_revoke.status_code();
}


void BiasedLocking::revoke(GrowableArray<Handle>* objs) {
  assert(!SafepointSynchronize::is_at_safepoint(), "must not be called while at safepoint");
  if (objs->length() == 0) {
    return;
  }
  VM_RevokeBias revoke(objs, JavaThread::current());
  VMThread::execute(&revoke);
}


void BiasedLocking::revoke_at_safepoint(Handle h_obj) {
  assert(SafepointSynchronize::is_at_safepoint(), "must only be called while at safepoint");
  oop obj = h_obj();
  HeuristicsResult heuristics = update_heuristics(obj, false);
  if (heuristics == HR_SINGLE_REVOKE) {
    revoke_bias(obj, false, false, NULL, NULL);
  } else if ((heuristics == HR_BULK_REBIAS) ||
             (heuristics == HR_BULK_REVOKE)) {
    bulk_revoke_or_rebias_at_safepoint(obj, (heuristics == HR_BULK_REBIAS), false, NULL);
  }
  clean_up_cached_monitor_info();
}


void BiasedLocking::revoke_at_safepoint(GrowableArray<Handle>* objs) {
  assert(SafepointSynchronize::is_at_safepoint(), "must only be called while at safepoint");
  int len = objs->length();
  for (int i = 0; i < len; i++) {
    oop obj = (objs->at(i))();
    HeuristicsResult heuristics = update_heuristics(obj, false);
    if (heuristics == HR_SINGLE_REVOKE) {
      revoke_bias(obj, false, false, NULL, NULL);
    } else if ((heuristics == HR_BULK_REBIAS) ||
               (heuristics == HR_BULK_REVOKE)) {
      bulk_revoke_or_rebias_at_safepoint(obj, (heuristics == HR_BULK_REBIAS), false, NULL);
    }
  }
  clean_up_cached_monitor_info();
}


void BiasedLocking::preserve_marks() {
  if (!UseBiasedLocking)
    return;

  assert(SafepointSynchronize::is_at_safepoint(), "must only be called while at safepoint");

  assert(_preserved_oop_stack  == NULL, "double initialization");
  assert(_preserved_mark_stack == NULL, "double initialization");

  // In order to reduce the number of mark words preserved during GC
  // due to the presence of biased locking, we reinitialize most mark
  // words to the class's prototype during GC -- even those which have
  // a currently valid bias owner. One important situation where we
  // must not clobber a bias is when a biased object is currently
  // locked. To handle this case we iterate over the currently-locked
  // monitors in a prepass and, if they are biased, preserve their
  // mark words here. This should be a relatively small set of objects
  // especially compared to the number of objects in the heap.
  _preserved_mark_stack = new (ResourceObj::C_HEAP, mtInternal) GrowableArray<markOop>(10, true);
  _preserved_oop_stack = new (ResourceObj::C_HEAP, mtInternal) GrowableArray<Handle>(10, true);

  ResourceMark rm;
  Thread* cur = Thread::current();
  for (JavaThreadIteratorWithHandle jtiwh; JavaThread *thread = jtiwh.next(); ) {
    if (thread->has_last_Java_frame()) {
      RegisterMap rm(thread);
      for (javaVFrame* vf = thread->last_java_vframe(&rm); vf != NULL; vf = vf->java_sender()) {
        GrowableArray<MonitorInfo*> *monitors = vf->monitors();
        if (monitors != NULL) {
          int len = monitors->length();
          // Walk monitors youngest to oldest
          for (int i = len - 1; i >= 0; i--) {
            MonitorInfo* mon_info = monitors->at(i);
            if (mon_info->owner_is_scalar_replaced()) continue;
            oop owner = mon_info->owner();
            if (owner != NULL) {
              markOop mark = owner->mark();
              if (mark->has_bias_pattern()) {
                _preserved_oop_stack->push(Handle(cur, owner));
                _preserved_mark_stack->push(mark);
              }
            }
          }
        }
      }
    }
  }
}


void BiasedLocking::restore_marks() {
  if (!UseBiasedLocking)
    return;

  assert(_preserved_oop_stack  != NULL, "double free");
  assert(_preserved_mark_stack != NULL, "double free");

  int len = _preserved_oop_stack->length();
  for (int i = 0; i < len; i++) {
    Handle owner = _preserved_oop_stack->at(i);
    markOop mark = _preserved_mark_stack->at(i);
    owner->set_mark(mark);
  }

  delete _preserved_oop_stack;
  _preserved_oop_stack = NULL;
  delete _preserved_mark_stack;
  _preserved_mark_stack = NULL;
}


int* BiasedLocking::total_entry_count_addr()                   { return _counters.total_entry_count_addr(); }
int* BiasedLocking::biased_lock_entry_count_addr()             { return _counters.biased_lock_entry_count_addr(); }
int* BiasedLocking::anonymously_biased_lock_entry_count_addr() { return _counters.anonymously_biased_lock_entry_count_addr(); }
int* BiasedLocking::rebiased_lock_entry_count_addr()           { return _counters.rebiased_lock_entry_count_addr(); }
int* BiasedLocking::revoked_lock_entry_count_addr()            { return _counters.revoked_lock_entry_count_addr(); }
int* BiasedLocking::fast_path_entry_count_addr()               { return _counters.fast_path_entry_count_addr(); }
int* BiasedLocking::slow_path_entry_count_addr()               { return _counters.slow_path_entry_count_addr(); }


// BiasedLockingCounters

int BiasedLockingCounters::slow_path_entry_count() {
  if (_slow_path_entry_count != 0) {
    return _slow_path_entry_count;
  }
  int sum = _biased_lock_entry_count   + _anonymously_biased_lock_entry_count +
            _rebiased_lock_entry_count + _revoked_lock_entry_count +
            _fast_path_entry_count;

  return _total_entry_count - sum;
}

void BiasedLockingCounters::print_on(outputStream* st) {
  tty->print_cr("# total entries: %d", _total_entry_count);
  tty->print_cr("# biased lock entries: %d", _biased_lock_entry_count);
  tty->print_cr("# anonymously biased lock entries: %d", _anonymously_biased_lock_entry_count);
  tty->print_cr("# rebiased lock entries: %d", _rebiased_lock_entry_count);
  tty->print_cr("# revoked lock entries: %d", _revoked_lock_entry_count);
  tty->print_cr("# fast path lock entries: %d", _fast_path_entry_count);
  tty->print_cr("# slow path lock entries: %d", slow_path_entry_count());
}
