/*
 * Copyright (c) 1998, 2018, Oracle and/or its affiliates. All rights reserved.
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
#include "classfile/vmSymbols.hpp"
#include "jfr/jfrEvents.hpp"
#include "jfr/support/jfrThreadId.hpp"
#include "memory/allocation.inline.hpp"
#include "memory/resourceArea.hpp"
#include "oops/markOop.hpp"
#include "oops/oop.inline.hpp"
#include "runtime/atomic.hpp"
#include "runtime/handles.inline.hpp"
#include "runtime/interfaceSupport.inline.hpp"
#include "runtime/mutexLocker.hpp"
#include "runtime/objectMonitor.hpp"
#include "runtime/objectMonitor.inline.hpp"
#include "runtime/orderAccess.hpp"
#include "runtime/osThread.hpp"
#include "runtime/safepointMechanism.inline.hpp"
#include "runtime/sharedRuntime.hpp"
#include "runtime/stubRoutines.hpp"
#include "runtime/thread.inline.hpp"
#include "services/threadService.hpp"
#include "utilities/dtrace.hpp"
#include "utilities/macros.hpp"
#include "utilities/preserveException.hpp"
#if INCLUDE_JFR
#include "jfr/support/jfrFlush.hpp"
#endif

#ifdef DTRACE_ENABLED

// Only bother with this argument setup if dtrace is available
// TODO-FIXME: probes should not fire when caller is _blocked.  assert() accordingly.


#define DTRACE_MONITOR_PROBE_COMMON(obj, thread)                           \
  char* bytes = NULL;                                                      \
  int len = 0;                                                             \
  jlong jtid = SharedRuntime::get_java_tid(thread);                        \
  Symbol* klassname = ((oop)obj)->klass()->name();                         \
  if (klassname != NULL) {                                                 \
    bytes = (char*)klassname->bytes();                                     \
    len = klassname->utf8_length();                                        \
  }

#define DTRACE_MONITOR_WAIT_PROBE(monitor, obj, thread, millis)            \
  {                                                                        \
    if (DTraceMonitorProbes) {                                             \
      DTRACE_MONITOR_PROBE_COMMON(obj, thread);                            \
      HOTSPOT_MONITOR_WAIT(jtid,                                           \
                           (monitor), bytes, len, (millis));               \
    }                                                                      \
  }

#define HOTSPOT_MONITOR_contended__enter HOTSPOT_MONITOR_CONTENDED_ENTER
#define HOTSPOT_MONITOR_contended__entered HOTSPOT_MONITOR_CONTENDED_ENTERED
#define HOTSPOT_MONITOR_contended__exit HOTSPOT_MONITOR_CONTENDED_EXIT
#define HOTSPOT_MONITOR_notify HOTSPOT_MONITOR_NOTIFY
#define HOTSPOT_MONITOR_notifyAll HOTSPOT_MONITOR_NOTIFYALL

#define DTRACE_MONITOR_PROBE(probe, monitor, obj, thread)                  \
  {                                                                        \
    if (DTraceMonitorProbes) {                                             \
      DTRACE_MONITOR_PROBE_COMMON(obj, thread);                            \
      HOTSPOT_MONITOR_##probe(jtid,                                        \
                              (uintptr_t)(monitor), bytes, len);           \
    }                                                                      \
  }

#else //  ndef DTRACE_ENABLED

#define DTRACE_MONITOR_WAIT_PROBE(obj, thread, millis, mon)    {;}
#define DTRACE_MONITOR_PROBE(probe, obj, thread, mon)          {;}

#endif // ndef DTRACE_ENABLED

// Tunables ...
// The knob* variables are effectively final.  Once set they should
// never be modified hence.  Consider using __read_mostly with GCC.

int ObjectMonitor::Knob_ExitRelease  = 0;
int ObjectMonitor::Knob_InlineNotify = 1;
int ObjectMonitor::Knob_Verbose      = 0;
int ObjectMonitor::Knob_VerifyInUse  = 0;
int ObjectMonitor::Knob_VerifyMatch  = 0;
int ObjectMonitor::Knob_SpinLimit    = 5000;    // derived by an external tool -

static int Knob_ReportSettings      = 0;
static int Knob_SpinBase            = 0;       // Floor AKA SpinMin
static int Knob_SpinBackOff         = 0;       // spin-loop backoff
static int Knob_CASPenalty          = -1;      // Penalty for failed CAS
static int Knob_OXPenalty           = -1;      // Penalty for observed _owner change
static int Knob_SpinSetSucc         = 1;       // spinners set the _succ field
static int Knob_SpinEarly           = 1;
static int Knob_SuccEnabled         = 1;       // futile wake throttling
static int Knob_SuccRestrict        = 0;       // Limit successors + spinners to at-most-one
static int Knob_MaxSpinners         = -1;      // Should be a function of # CPUs
static int Knob_Bonus               = 100;     // spin success bonus
static int Knob_BonusB              = 100;     // spin success bonus
static int Knob_Penalty             = 200;     // spin failure penalty
static int Knob_Poverty             = 1000;
static int Knob_SpinAfterFutile     = 1;       // Spin after returning from park()
static int Knob_FixedSpin           = 0;
static int Knob_OState              = 3;       // Spinner checks thread state of _owner
static int Knob_UsePause            = 1;
static int Knob_ExitPolicy          = 0;
static int Knob_PreSpin             = 10;      // 20-100 likely better
static int Knob_ResetEvent          = 0;
static int BackOffMask              = 0;

static int Knob_FastHSSEC           = 0;
static int Knob_MoveNotifyee        = 2;       // notify() - disposition of notifyee
static int Knob_QMode               = 0;       // EntryList-cxq policy - queue discipline
static volatile int InitDone        = 0;

// -----------------------------------------------------------------------------
// Theory of operations -- Monitors lists, thread residency, etc:
//
// * A thread acquires ownership of a monitor by successfully
//   CAS()ing the _owner field from null to non-null.
//
// * Invariant: A thread appears on at most one monitor list --
//   cxq, EntryList or WaitSet -- at any one time.
//
// * Contending threads "push" themselves onto the cxq with CAS
//   and then spin/park.
//
// * After a contending thread eventually acquires the lock it must
//   dequeue itself from either the EntryList or the cxq.
//
// * The exiting thread identifies and unparks an "heir presumptive"
//   tentative successor thread on the EntryList.  Critically, the
//   exiting thread doesn't unlink the successor thread from the EntryList.
//   After having been unparked, the wakee will recontend for ownership of
//   the monitor.   The successor (wakee) will either acquire the lock or
//   re-park itself.
//
//   Succession is provided for by a policy of competitive handoff.
//   The exiting thread does _not_ grant or pass ownership to the
//   successor thread.  (This is also referred to as "handoff" succession").
//   Instead the exiting thread releases ownership and possibly wakes
//   a successor, so the successor can (re)compete for ownership of the lock.
//   If the EntryList is empty but the cxq is populated the exiting
//   thread will drain the cxq into the EntryList.  It does so by
//   by detaching the cxq (installing null with CAS) and folding
//   the threads from the cxq into the EntryList.  The EntryList is
//   doubly linked, while the cxq is singly linked because of the
//   CAS-based "push" used to enqueue recently arrived threads (RATs).
//
// * Concurrency invariants:
//
//   -- only the monitor owner may access or mutate the EntryList.
//      The mutex property of the monitor itself protects the EntryList
//      from concurrent interference.
//   -- Only the monitor owner may detach the cxq.
//
// * The monitor entry list operations avoid locks, but strictly speaking
//   they're not lock-free.  Enter is lock-free, exit is not.
//   For a description of 'Methods and apparatus providing non-blocking access
//   to a resource,' see U.S. Pat. No. 7844973.
//
// * The cxq can have multiple concurrent "pushers" but only one concurrent
//   detaching thread.  This mechanism is immune from the ABA corruption.
//   More precisely, the CAS-based "push" onto cxq is ABA-oblivious.
//
// * Taken together, the cxq and the EntryList constitute or form a
//   single logical queue of threads stalled trying to acquire the lock.
//   We use two distinct lists to improve the odds of a constant-time
//   dequeue operation after acquisition (in the ::enter() epilogue) and
//   to reduce heat on the list ends.  (c.f. Michael Scott's "2Q" algorithm).
//   A key desideratum is to minimize queue & monitor metadata manipulation
//   that occurs while holding the monitor lock -- that is, we want to
//   minimize monitor lock holds times.  Note that even a small amount of
//   fixed spinning will greatly reduce the # of enqueue-dequeue operations
//   on EntryList|cxq.  That is, spinning relieves contention on the "inner"
//   locks and monitor metadata.
//
//   Cxq points to the set of Recently Arrived Threads attempting entry.
//   Because we push threads onto _cxq with CAS, the RATs must take the form of
//   a singly-linked LIFO.  We drain _cxq into EntryList  at unlock-time when
//   the unlocking thread notices that EntryList is null but _cxq is != null.
//
//   The EntryList is ordered by the prevailing queue discipline and
//   can be organized in any convenient fashion, such as a doubly-linked list or
//   a circular doubly-linked list.  Critically, we want insert and delete operations
//   to operate in constant-time.  If we need a priority queue then something akin
//   to Solaris' sleepq would work nicely.  Viz.,
//   http://agg.eng/ws/on10_nightly/source/usr/src/uts/common/os/sleepq.c.
//   Queue discipline is enforced at ::exit() time, when the unlocking thread
//   drains the cxq into the EntryList, and orders or reorders the threads on the
//   EntryList accordingly.
//
//   Barring "lock barging", this mechanism provides fair cyclic ordering,
//   somewhat similar to an elevator-scan.
//
// * The monitor synchronization subsystem avoids the use of native
//   synchronization primitives except for the narrow platform-specific
//   park-unpark abstraction.  See the comments in os_solaris.cpp regarding
//   the semantics of park-unpark.  Put another way, this monitor implementation
//   depends only on atomic operations and park-unpark.  The monitor subsystem
//   manages all RUNNING->BLOCKED and BLOCKED->READY transitions while the
//   underlying OS manages the READY<->RUN transitions.
//
// * Waiting threads reside on the WaitSet list -- wait() puts
//   the caller onto the WaitSet.
//
// * notify() or notifyAll() simply transfers threads from the WaitSet to
//   either the EntryList or cxq.  Subsequent exit() operations will
//   unpark the notifyee.  Unparking a notifee in notify() is inefficient -
//   it's likely the notifyee would simply impale itself on the lock held
//   by the notifier.
//
// * An interesting alternative is to encode cxq as (List,LockByte) where
//   the LockByte is 0 iff the monitor is owned.  _owner is simply an auxiliary
//   variable, like _recursions, in the scheme.  The threads or Events that form
//   the list would have to be aligned in 256-byte addresses.  A thread would
//   try to acquire the lock or enqueue itself with CAS, but exiting threads
//   could use a 1-0 protocol and simply STB to set the LockByte to 0.
//   Note that is is *not* word-tearing, but it does presume that full-word
//   CAS operations are coherent with intermix with STB operations.  That's true
//   on most common processors.
//
// * See also http://blogs.sun.com/dave


void* ObjectMonitor::operator new (size_t size) throw() {
  return AllocateHeap(size, mtInternal);
}
void* ObjectMonitor::operator new[] (size_t size) throw() {
  return operator new (size);
}
void ObjectMonitor::operator delete(void* p) {
  FreeHeap(p);
}
void ObjectMonitor::operator delete[] (void *p) {
  operator delete(p);
}

// 膨胀完成之后，会调用enter方法.
// 1.如果当前是无锁状态、锁重入、当前线程是之前持有轻量级锁的线程则进行简单操作后返回.
// 2.先自旋尝试获得锁，这样做的目的是为了减少执行操作系统同步操作带来的开销.
// 3.调用EnterI方法获得锁或阻塞.
// -----------------------------------------------------------------------------
// Enter support

void ObjectMonitor::enter(TRAPS) {
  // The following code is ordered to check the most common cases first
  // and to reduce RTS->RTO cache line upgrades on SPARC and IA32 processors.
  Thread * const Self = THREAD;

  // 若当前ObjectMonitor的owner为null，如果能CAS设置_owner为当前线程成功，则当前线程直接获得锁.
  void * cur = Atomic::cmpxchg(Self, &_owner, (void*)NULL);
  if (cur == NULL) {
    // Either ASSERT _recursions == 0 or explicitly set _recursions = 0.
    assert(_recursions == 0, "invariant");
    assert(_owner == Self, "invariant");
    return;
  }

  // 如果是重入的情况,重入计数自增后返回.
  if (cur == Self) {
    // TODO-FIXME: check for integer overflow!  BUGID 6557169.
    _recursions++;
    return;
  }

  // 当前线程是之前持有轻量级锁的线程。由轻量级锁膨胀且第一次调用enter方法，那cur是指向Lock Record的指针
  if (Self->is_lock_owned ((address)cur)) {
    assert(_recursions == 0, "internal state error");
    // 重入计数重置为1
    _recursions = 1;
    // 设置owner字段为当前线程（之前owner是指向Lock Record的指针）
    // Commute owner from a thread-specific on-stack BasicLockObject address to
    // a full-fledged "Thread *".
    _owner = Self;
    return;
  }

  // We've encountered genuine contention.
  assert(Self->_Stalled == 0, "invariant");
  Self->_Stalled = intptr_t(this);

  // Try one round of spinning *before* enqueueing Self
  // and before going through the awkward and expensive state
  // transitions.  The following spin is strictly optional ...
  // Note that if we acquire the monitor from an initial spin
  // we forgo posting JVMTI events and firing DTRACE probes.
  // 在调用系统的同步操作之前，先尝试自适应自旋获得锁
  if (Knob_SpinEarly && TrySpin (Self) > 0) {
    //自旋的过程中获得了锁，则直接返回
    assert(_owner == Self, "invariant");
    assert(_recursions == 0, "invariant");
    assert(((oop)(object()))->mark() == markOopDesc::encode(this), "invariant");
    Self->_Stalled = 0;
    return;
  }

  assert(_owner != Self, "invariant");
  assert(_succ != Self, "invariant");
  assert(Self->is_Java_thread(), "invariant");
  JavaThread * jt = (JavaThread *) Self;
  assert(!SafepointSynchronize::is_at_safepoint(), "invariant");
  assert(jt->thread_state() != _thread_blocked, "invariant");
  assert(this->object() != NULL, "invariant");
  assert(_count >= 0, "invariant");

  // Prevent deflation at STW-time.  See deflate_idle_monitors() and is_busy().
  // Ensure the object-monitor relationship remains stable while there's contention.
  Atomic::inc(&_count);

  JFR_ONLY(JfrConditionalFlushWithStacktrace<EventJavaMonitorEnter> flush(jt);)
  EventJavaMonitorEnter event;
  if (event.should_commit()) {
    event.set_monitorClass(((oop)this->object())->klass());
    event.set_address((uintptr_t)(this->object_addr()));
  }

  { // Change java thread status to indicate blocked on monitor enter.
    // 改变Java Thread对象的状态为block
    JavaThreadBlockedOnMonitorEnterState jtbmes(jt, this);

    Self->set_current_pending_monitor(this);

    DTRACE_MONITOR_PROBE(contended__enter, this, object(), jt);
    if (JvmtiExport::should_post_monitor_contended_enter()) {
      JvmtiExport::post_monitor_contended_enter(jt, this);

      // The current thread does not yet own the monitor and does not
      // yet appear on any queues that would get it made the successor.
      // This means that the JVMTI_EVENT_MONITOR_CONTENDED_ENTER event
      // handler cannot accidentally consume an unpark() meant for the
      // ParkEvent associated with this ObjectMonitor.
    }

    OSThreadContendState osts(Self->osthread());
    ThreadBlockInVM tbivm(jt);

    // TODO-FIXME: change the following for(;;) loop to straight-line code.
    for (;;) {
      jt->set_suspend_equivalent();
      // cleared by handle_special_suspend_equivalent_condition()
      // or java_suspend_self()

      // 重点,在该方法中调用系统同步操作(进入队列将当前线程阻塞)
      EnterI(THREAD);

      if (!ExitSuspendEquivalent(jt)) break;

      // We have acquired the contended monitor, but while we were
      // waiting another thread suspended us. We don't want to enter
      // the monitor while suspended because that would surprise the
      // thread that suspended us.
      //
      _recursions = 0;
      _succ = NULL;
      exit(false, Self);

      jt->java_suspend_self();
    }
    Self->set_current_pending_monitor(NULL);

    // We cleared the pending monitor info since we've just gotten past
    // the enter-check-for-suspend dance and we now own the monitor free
    // and clear, i.e., it is no longer pending. The ThreadBlockInVM
    // destructor can go to a safepoint at the end of this block. If we
    // do a thread dump during that safepoint, then this thread will show
    // as having "-locked" the monitor, but the OS and java.lang.Thread
    // states will still report that the thread is blocked trying to
    // acquire it.
  }

  Atomic::dec(&_count);
  assert(_count >= 0, "invariant");
  Self->_Stalled = 0;

  // Must either set _recursions = 0 or ASSERT _recursions == 0.
  assert(_recursions == 0, "invariant");
  assert(_owner == Self, "invariant");
  assert(_succ != Self, "invariant");
  assert(((oop)(object()))->mark() == markOopDesc::encode(this), "invariant");

  // The thread -- now the owner -- is back in vm mode.
  // Report the glorious news via TI,DTrace and jvmstat.
  // The probe effect is non-trivial.  All the reportage occurs
  // while we hold the monitor, increasing the length of the critical
  // section.  Amdahl's parallel speedup law comes vividly into play.
  //
  // Another option might be to aggregate the events (thread local or
  // per-monitor aggregation) and defer reporting until a more opportune
  // time -- such as next time some thread encounters contention but has
  // yet to acquire the lock.  While spinning that thread could
  // spinning we could increment JVMStat counters, etc.

  DTRACE_MONITOR_PROBE(contended__entered, this, object(), jt);
  if (JvmtiExport::should_post_monitor_contended_entered()) {
    JvmtiExport::post_monitor_contended_entered(jt, this);

    // The current thread already owns the monitor and is not going to
    // call park() for the remainder of the monitor enter protocol. So
    // it doesn't matter if the JVMTI_EVENT_MONITOR_CONTENDED_ENTERED
    // event handler consumed an unpark() issued by the thread that
    // just exited the monitor.
  }
  if (event.should_commit()) {
    event.set_previousOwner((uintptr_t)_previous_owner_tid);
    event.commit();
  }
  OM_PERFDATA_OP(ContendedLockAttempts, inc());
}

//尝试通过 cas 操作将 _owner 字段设置为 Self，
// 其中 _owner 表示当前 ObjectMonitor 对象锁持有的线程指针，
// Self 指向当前执行的线程。
// 如果设置上了，表示当前线程获得了锁，否则没有获得。
// Caveat: TryLock() is not necessarily serializing if it returns failure.
// Callers must compensate as needed.

int ObjectMonitor::TryLock(Thread * Self) {
  void * own = _owner;
  if (own != NULL) return 0;
  if (Atomic::replace_if_null(Self, &_owner)) {
    // Either guarantee _recursions == 0 or set _recursions = 0.
    assert(_recursions == 0, "invariant");
    assert(_owner == Self, "invariant");
    return 1;
  }
  // The lock had been free momentarily, but we lost the race to the lock.
  // Interference -- the CAS failed.
  // We can either return -1 or retry.
  // Retry doesn't make as much sense because the lock was just acquired.
  return -1;
}

#define MAX_RECHECK_INTERVAL 1000

// 进入队列将当前线程阻塞.
// 大致原理:
// 一个ObjectMonitor对象包括这么几个关键字段：
// cxq（ContentionList），EntryList ，WaitSet和owner.
// 其中cxq ，EntryList ，WaitSet都是由ObjectWaiter的链表结构，其owner指向持有锁的线程。
// 它们的作用可以看:
// [深入JVM锁机制1-synchronized](https://blog.csdn.net/chen77716/article/details/6618779)
// 当一个线程尝试获得锁时，如果该锁已经被占用，则会将该线程封装成一个ObjectWaiter对象,
// 插入到cxq的队列的队首，然后调用park函数挂起当前线程。
// 在Linux系统上，park函数底层调用的是glibc库的pthread_cond_wait，
// JDK的ReentrantLock底层也是用该方法挂起线程的,
// 关于Linux同步更多细节可以看:
// [关于同步的一点思考](https://github.com/farmerjohngit/myblog/issues/7)
// [linux内核级同步机制--futex](https://github.com/farmerjohngit/myblog/issues/8)
// 当线程释放锁时，会从cxq或EntryList中挑选一个线程唤醒，
// 被选中的线程叫做Heir presumptive(假定继承人)，假定继承人被唤醒后会尝试获得锁，
// 但synchronized是非公平的，所以假定继承人不一定能获得锁（这也是它叫"假定"继承人的原因）。
// 如果线程获得锁后调用Object#wait方法，则会将线程加入到WaitSet中，
// 当被Object#notify唤醒后，会将线程从WaitSet移动到cxq或EntryList中去。
// 需要注意的是，当调用一个锁对象的wait或notify方法时，如当前锁的状态是偏向锁或轻量级锁
// 则会先膨胀成重量级锁。
// synchronized的monitor锁机制和JDK的ReentrantLock与Condition是很相似的，
// ReentrantLock也有一个存放等待获取锁线程的链表，Condition也有一个类似WaitSet的集合用来存放调用了await的线程。
void ObjectMonitor::EnterI(TRAPS) {
  Thread * const Self = THREAD;
  assert(Self->is_Java_thread(), "invariant");
  assert  (((JavaThread *) Self)->thread_state() == _thread_blocked, "invariant");

  // 先执行TryLock尝试获得锁
  // Try the lock - TATAS
  if (TryLock (Self) > 0) {
    assert(_succ != Self, "invariant");
    assert(_owner == Self, "invariant");
    assert(_Responsible != Self, "invariant");
    return;
  }

  DeferredInitialize();

  // 在将自己入队前再次重试,
  // 其实是为了在入队阻塞线程之前的最后检查，防止线程无谓地进行状态切换。
  // 但是为什么执行两次？其实第下面的英文的注释已经说明了，这么做有一些微妙的亲和力影响？什么是亲和力？
  // 这是很多操作系统中都有的一种 CPU 执行调度逻辑，说的是，如果在过去一段时间内，
  // 某个线程尝试获取某种资源一直失败，那么系统在后面会倾向于将该资源分配给这个线程。
  // 这里我们前后两次执行，就是告诉系统当前线程「迫切」想要获得这个 cas 资源，如果可以用的话尽量分配给它。
  // 当然这种亲和力不是一种得到保证的协议，因此这种操作只能是一种积极的、并且无害的操作。
  // We try one round of spinning *before* enqueueing Self.
  //
  // If the _owner is ready but OFFPROC we could use a YieldTo()
  // operation to donate the remainder of this thread's quantum
  // to the owner.  This has subtle but beneficial affinity
  // effects.

  if (TrySpin (Self) > 0) {
    assert(_owner == Self, "invariant");
    assert(_succ != Self, "invariant");
    assert(_Responsible != Self, "invariant");
    return;
  }

  // The Spin failed -- Enqueue and park the thread ...
  assert(_succ != Self, "invariant");
  assert(_owner != Self, "invariant");
  assert(_Responsible != Self, "invariant");

  // 两次「微妙」的 try lock 之后仍然失败，那么就只能乖乖入队阻塞了.
  // Enqueue "Self" on ObjectMonitor's _cxq.
  //
  // Node acts as a proxy for Self.
  // As an aside, if were to ever rewrite the synchronization code mostly
  // in Java, WaitNodes, ObjectMonitors, and Events would become 1st-class
  // Java objects.  This would avoid awkward lifecycle and liveness issues,
  // as well as eliminate a subset of ABA issues.
  // TODO: eliminate ObjectWaiter and enqueue either Threads or Events.

  // 创建一个 ObjectWaiter 对象，
  // 这个对象将当前线程的对象（注意是 JavaThread 对象）包裹起来.
  ObjectWaiter node(Self);
  Self->_ParkEvent->reset();
  node._prev   = (ObjectWaiter *) 0xBAD;
  node.TState  = ObjectWaiter::TS_CXQ;

  // 自旋入队.
  // 正如注释中说的那样，我们是要将当前节点放到 CXQ 队列的头部，
  // 将链表的头节点_cxq指针通过 cas 操作指向 新建的节点node 指针就完成了入队操作。(头插法)
  // 如果入队成功，则退出当前循环，否则再次尝试获取锁，因为可能这个时候会成功。
  // Push "Self" onto the front of the _cxq.
  // Once on cxq/EntryList, Self stays on-queue until it acquires the lock.
  // Note that spinning tends to reduce the rate at which threads
  // enqueue and dequeue on EntryList|cxq.
  ObjectWaiter * nxt;
  for (;;) {
    node._next = nxt = _cxq;
    if (Atomic::cmpxchg(&node, &_cxq, nxt) == nxt) break;

    // Interference - the CAS failed because _cxq changed.  Just retry.
    // As an optional optimization we retry the lock.
    if (TryLock (Self) > 0) {
      assert(_succ != Self, "invariant");
      assert(_owner == Self, "invariant");
      assert(_Responsible != Self, "invariant");
      return;
    }
  }

  // Check for cxq|EntryList edge transition to non-null.  This indicates
  // the onset of contention.  While contention persists exiting threads
  // will use a ST:MEMBAR:LD 1-1 exit protocol.  When contention abates exit
  // operations revert to the faster 1-0 mode.  This enter operation may interleave
  // (race) a concurrent 1-0 exit operation, resulting in stranding, so we
  // arrange for one of the contending thread to use a timed park() operations
  // to detect and recover from the race.  (Stranding is form of progress failure
  // where the monitor is unlocked but all the contending threads remain parked).
  // That is, at least one of the contended threads will periodically poll _owner.
  // One of the contending threads will become the designated "Responsible" thread.
  // The Responsible thread uses a timed park instead of a normal indefinite park
  // operation -- it periodically wakes and checks for and recovers from potential
  // strandings admitted by 1-0 exit operations.   We need at most one Responsible
  // thread per-monitor at any given moment.  Only threads on cxq|EntryList may
  // be responsible for a monitor.
  //
  // Currently, one of the contended threads takes on the added role of "Responsible".
  // A viable alternative would be to use a dedicated "stranding checker" thread
  // that periodically iterated over all the threads (or active monitors) and unparked
  // successors where there was risk of stranding.  This would help eliminate the
  // timer scalability issues we see on some platforms as we'd only have one thread
  // -- the checker -- parked on a timer.

  // SyncFlags默认为0.
  // 当竞争发生时，选取一个线程作为_Responsible,
  // 这个_Responsible线程在下面park时,
  // 调用的是带时间参数的park,防止出现"饥饿"现象.
  // 如果没有其他等待的线程，则将_Responsible设置为自己.
  if ((SyncFlags & 16) == 0 && nxt == NULL && _EntryList == NULL) {
    // Try to assume the role of responsible thread for the monitor.
    // CONSIDER:  ST vs CAS vs { if (Responsible==null) Responsible=Self }
    Atomic::replace_if_null(Self, &_Responsible);
  }

  // The lock might have been released while this thread was occupied queueing
  // itself onto _cxq.  To close the race and avoid "stranding" and
  // progress-liveness failure we must resample-retry _owner before parking.
  // Note the Dekker/Lamport duality: ST cxq; MEMBAR; LD Owner.
  // In this case the ST-MEMBAR is accomplished with CAS().
  //
  // TODO: Defer all thread state transitions until park-time.
  // Since state transitions are heavy and inefficient we'd like
  // to defer the state transitions until absolutely necessary,
  // and in doing so avoid some transitions ...

  TEVENT(Inflated enter - Contention);
  int nWakeups = 0;
  int recheckInterval = 1;

  // 这个循环主要执行三件事：
  // 1. 尝试获取锁
  // 2. park 当前线程
  // 3. 再次尝试获取锁
  // 也就是在成功获取到锁前,线程可能经过多次park与unpark.
  for (;;) {

    if (TryLock(Self) > 0) break;
    assert(_owner != Self, "invariant");

    if ((SyncFlags & 2) && _Responsible == NULL) {
      Atomic::replace_if_null(Self, &_Responsible);
    }

    // park self
    if (_Responsible == Self || (SyncFlags & 1)) {
      // 当前线程是_Responsible时，调用带时间参数的park
      // 防止出现"饥饿"现象.
      // 简单的「退避算法」:
      // 第一次等待 1 ms，第二次等待 8 ms，第三次等待 64 ms，以此类推，
      // 直到达到等待时长的上线：MAX_RECHECK_INTERVAL.
      TEVENT(Inflated enter - park TIMED);
      Self->_ParkEvent->park((jlong) recheckInterval);
      // Increase the recheckInterval, but clamp the value.
      recheckInterval *= 8;
      if (recheckInterval > MAX_RECHECK_INTERVAL) {
        recheckInterval = MAX_RECHECK_INTERVAL;
      }
    } else {
      // 否则直接调用park挂起当前线程
      TEVENT(Inflated enter - park UNTIMED);
      Self->_ParkEvent->park();
    }

    if (TryLock(Self) > 0) break;

    // The lock is still contested.
    // Keep a tally of the # of futile wakeups.
    // Note that the counter is not protected by a lock or updated by atomics.
    // That is by design - we trade "lossy" counters which are exposed to
    // races during updates for a lower probe effect.
    TEVENT(Inflated enter - Futile wakeup);
    // This PerfData object can be used in parallel with a safepoint.
    // See the work around in PerfDataManager::destroy().
    OM_PERFDATA_OP(FutileWakeups, inc());
    ++nWakeups;

    // Assuming this is not a spurious wakeup we'll normally find _succ == Self.
    // We can defer clearing _succ until after the spin completes
    // TrySpin() must tolerate being called with _succ == Self.
    // Try yet another round of adaptive spinning.
    if ((Knob_SpinAfterFutile & 1) && TrySpin(Self) > 0) break;

    // We can find that we were unpark()ed and redesignated _succ while
    // we were spinning.  That's harmless.  If we iterate and call park(),
    // park() will consume the event and return immediately and we'll
    // just spin again.  This pattern can repeat, leaving _succ to simply
    // spin on a CPU.  Enable Knob_ResetEvent to clear pending unparks().
    // Alternately, we can sample fired() here, and if set, forgo spinning
    // in the next iteration.

    if ((Knob_ResetEvent & 1) && Self->_ParkEvent->fired()) {
      Self->_ParkEvent->reset();
      OrderAccess::fence();
    }
    // 在释放锁时，_succ会被设置为EntryList或_cxq中的一个线程.
    // 其含义是Heir presumptive，也就是我们上面注释中说的假定继承人.
    if (_succ == Self) _succ = NULL;

    // Invariant: after clearing _succ a thread *must* retry _owner before parking.
    OrderAccess::fence();
  }

  // 走到这里说明已经获得锁了
  // Egress :
  // Self has acquired the lock -- Unlink Self from the cxq or EntryList.
  // Normally we'll find Self on the EntryList .
  // From the perspective of the lock owner (this thread), the
  // EntryList is stable and cxq is prepend-only.
  // The head of cxq is volatile but the interior is stable.
  // In addition, Self.TState is stable.

  assert(_owner == Self, "invariant");
  assert(object() != NULL, "invariant");
  // I'd like to write:
  //   guarantee (((oop)(object()))->mark() == markOopDesc::encode(this), "invariant") ;
  // but as we're at a safepoint that's not safe.

  // 将当前线程的node从cxq或EntryList中移除
  UnlinkAfterAcquire(Self, &node);
  if (_succ == Self) _succ = NULL;

  assert(_succ != Self, "invariant");
  if (_Responsible == Self) {
    _Responsible = NULL;
    OrderAccess::fence(); // Dekker pivot-point

    // We may leave threads on cxq|EntryList without a designated
    // "Responsible" thread.  This is benign.  When this thread subsequently
    // exits the monitor it can "see" such preexisting "old" threads --
    // threads that arrived on the cxq|EntryList before the fence, above --
    // by LDing cxq|EntryList.  Newly arrived threads -- that is, threads
    // that arrive on cxq after the ST:MEMBAR, above -- will set Responsible
    // non-null and elect a new "Responsible" timer thread.
    //
    // This thread executes:
    //    ST Responsible=null; MEMBAR    (in enter epilogue - here)
    //    LD cxq|EntryList               (in subsequent exit)
    //
    // Entering threads in the slow/contended path execute:
    //    ST cxq=nonnull; MEMBAR; LD Responsible (in enter prolog)
    //    The (ST cxq; MEMBAR) is accomplished with CAS().
    //
    // The MEMBAR, above, prevents the LD of cxq|EntryList in the subsequent
    // exit operation from floating above the ST Responsible=null.
  }

  // We've acquired ownership with CAS().
  // CAS is serializing -- it has MEMBAR/FENCE-equivalent semantics.
  // But since the CAS() this thread may have also stored into _succ,
  // EntryList, cxq or Responsible.  These meta-data updates must be
  // visible __before this thread subsequently drops the lock.
  // Consider what could occur if we didn't enforce this constraint --
  // STs to monitor meta-data and user-data could reorder with (become
  // visible after) the ST in exit that drops ownership of the lock.
  // Some other thread could then acquire the lock, but observe inconsistent
  // or old monitor meta-data and heap data.  That violates the JMM.
  // To that end, the 1-0 exit() operation must have at least STST|LDST
  // "release" barrier semantics.  Specifically, there must be at least a
  // STST|LDST barrier in exit() before the ST of null into _owner that drops
  // the lock.   The barrier ensures that changes to monitor meta-data and data
  // protected by the lock will be visible before we release the lock, and
  // therefore before some other thread (CPU) has a chance to acquire the lock.
  // See also: http://gee.cs.oswego.edu/dl/jmm/cookbook.html.
  //
  // Critically, any prior STs to _succ or EntryList must be visible before
  // the ST of null into _owner in the *subsequent* (following) corresponding
  // monitorexit.  Recall too, that in 1-0 mode monitorexit does not necessarily
  // execute a serializing instruction.

  if (SyncFlags & 8) {
    OrderAccess::fence();
  }
  return;
}

// ReenterI() is a specialized inline form of the latter half of the
// contended slow-path from EnterI().  We use ReenterI() only for
// monitor reentry in wait().
//
// In the future we should reconcile EnterI() and ReenterI(), adding
// Knob_Reset and Knob_SpinAfterFutile support and restructuring the
// loop accordingly.

void ObjectMonitor::ReenterI(Thread * Self, ObjectWaiter * SelfNode) {
  assert(Self != NULL, "invariant");
  assert(SelfNode != NULL, "invariant");
  assert(SelfNode->_thread == Self, "invariant");
  assert(_waiters > 0, "invariant");
  assert(((oop)(object()))->mark() == markOopDesc::encode(this), "invariant");
  assert(((JavaThread *)Self)->thread_state() != _thread_blocked, "invariant");
  JavaThread * jt = (JavaThread *) Self;

  int nWakeups = 0;
  for (;;) {
    ObjectWaiter::TStates v = SelfNode->TState;
    guarantee(v == ObjectWaiter::TS_ENTER || v == ObjectWaiter::TS_CXQ, "invariant");
    assert(_owner != Self, "invariant");

    if (TryLock(Self) > 0) break;
    if (TrySpin(Self) > 0) break;

    TEVENT(Wait Reentry - parking);

    // State transition wrappers around park() ...
    // ReenterI() wisely defers state transitions until
    // it's clear we must park the thread.
    {
      OSThreadContendState osts(Self->osthread());
      ThreadBlockInVM tbivm(jt);

      // cleared by handle_special_suspend_equivalent_condition()
      // or java_suspend_self()
      jt->set_suspend_equivalent();
      if (SyncFlags & 1) {
        Self->_ParkEvent->park((jlong)MAX_RECHECK_INTERVAL);
      } else {
        Self->_ParkEvent->park();
      }

      // were we externally suspended while we were waiting?
      for (;;) {
        if (!ExitSuspendEquivalent(jt)) break;
        if (_succ == Self) { _succ = NULL; OrderAccess::fence(); }
        jt->java_suspend_self();
        jt->set_suspend_equivalent();
      }
    }

    // Try again, but just so we distinguish between futile wakeups and
    // successful wakeups.  The following test isn't algorithmically
    // necessary, but it helps us maintain sensible statistics.
    if (TryLock(Self) > 0) break;

    // The lock is still contested.
    // Keep a tally of the # of futile wakeups.
    // Note that the counter is not protected by a lock or updated by atomics.
    // That is by design - we trade "lossy" counters which are exposed to
    // races during updates for a lower probe effect.
    TEVENT(Wait Reentry - futile wakeup);
    ++nWakeups;

    // Assuming this is not a spurious wakeup we'll normally
    // find that _succ == Self.
    if (_succ == Self) _succ = NULL;

    // Invariant: after clearing _succ a contending thread
    // *must* retry  _owner before parking.
    OrderAccess::fence();

    // This PerfData object can be used in parallel with a safepoint.
    // See the work around in PerfDataManager::destroy().
    OM_PERFDATA_OP(FutileWakeups, inc());
  }

  // Self has acquired the lock -- Unlink Self from the cxq or EntryList .
  // Normally we'll find Self on the EntryList.
  // Unlinking from the EntryList is constant-time and atomic-free.
  // From the perspective of the lock owner (this thread), the
  // EntryList is stable and cxq is prepend-only.
  // The head of cxq is volatile but the interior is stable.
  // In addition, Self.TState is stable.

  assert(_owner == Self, "invariant");
  assert(((oop)(object()))->mark() == markOopDesc::encode(this), "invariant");
  UnlinkAfterAcquire(Self, SelfNode);
  if (_succ == Self) _succ = NULL;
  assert(_succ != Self, "invariant");
  SelfNode->TState = ObjectWaiter::TS_RUN;
  OrderAccess::fence();      // see comments at the end of EnterI()
}

// By convention we unlink a contending thread from EntryList|cxq immediately
// after the thread acquires the lock in ::enter().  Equally, we could defer
// unlinking the thread until ::exit()-time.

void ObjectMonitor::UnlinkAfterAcquire(Thread *Self, ObjectWaiter *SelfNode) {
  assert(_owner == Self, "invariant");
  assert(SelfNode->_thread == Self, "invariant");

  if (SelfNode->TState == ObjectWaiter::TS_ENTER) {
    // Normal case: remove Self from the DLL EntryList .
    // This is a constant-time operation.
    ObjectWaiter * nxt = SelfNode->_next;
    ObjectWaiter * prv = SelfNode->_prev;
    if (nxt != NULL) nxt->_prev = prv;
    if (prv != NULL) prv->_next = nxt;
    if (SelfNode == _EntryList) _EntryList = nxt;
    assert(nxt == NULL || nxt->TState == ObjectWaiter::TS_ENTER, "invariant");
    assert(prv == NULL || prv->TState == ObjectWaiter::TS_ENTER, "invariant");
    TEVENT(Unlink from EntryList);
  } else {
    assert(SelfNode->TState == ObjectWaiter::TS_CXQ, "invariant");
    // Inopportune interleaving -- Self is still on the cxq.
    // This usually means the enqueue of self raced an exiting thread.
    // Normally we'll find Self near the front of the cxq, so
    // dequeueing is typically fast.  If needbe we can accelerate
    // this with some MCS/CHL-like bidirectional list hints and advisory
    // back-links so dequeueing from the interior will normally operate
    // in constant-time.
    // Dequeue Self from either the head (with CAS) or from the interior
    // with a linear-time scan and normal non-atomic memory operations.
    // CONSIDER: if Self is on the cxq then simply drain cxq into EntryList
    // and then unlink Self from EntryList.  We have to drain eventually,
    // so it might as well be now.

    ObjectWaiter * v = _cxq;
    assert(v != NULL, "invariant");
    if (v != SelfNode || Atomic::cmpxchg(SelfNode->_next, &_cxq, v) != v) {
      // The CAS above can fail from interference IFF a "RAT" arrived.
      // In that case Self must be in the interior and can no longer be
      // at the head of cxq.
      if (v == SelfNode) {
        assert(_cxq != v, "invariant");
        v = _cxq;          // CAS above failed - start scan at head of list
      }
      ObjectWaiter * p;
      ObjectWaiter * q = NULL;
      for (p = v; p != NULL && p != SelfNode; p = p->_next) {
        q = p;
        assert(p->TState == ObjectWaiter::TS_CXQ, "invariant");
      }
      assert(v != SelfNode, "invariant");
      assert(p == SelfNode, "Node not found on cxq");
      assert(p != _cxq, "invariant");
      assert(q != NULL, "invariant");
      assert(q->_next == p, "invariant");
      q->_next = p->_next;
    }
    TEVENT(Unlink from cxq);
  }

#ifdef ASSERT
  // Diagnostic hygiene ...
  SelfNode->_prev  = (ObjectWaiter *) 0xBAD;
  SelfNode->_next  = (ObjectWaiter *) 0xBAD;
  SelfNode->TState = ObjectWaiter::TS_RUN;
#endif
}

// -----------------------------------------------------------------------------
// Exit support
//
// exit()
// ~~~~~~
// Note that the collector can't reclaim the objectMonitor or deflate
// the object out from underneath the thread calling ::exit() as the
// thread calling ::exit() never transitions to a stable state.
// This inhibits GC, which in turn inhibits asynchronous (and
// inopportune) reclamation of "this".
//
// We'd like to assert that: (THREAD->thread_state() != _thread_blocked) ;
// There's one exception to the claim above, however.  EnterI() can call
// exit() to drop a lock if the acquirer has been externally suspended.
// In that case exit() is called with _thread_state as _thread_blocked,
// but the monitor's _count field is > 0, which inhibits reclamation.
//
// 1-0 exit
// ~~~~~~~~
// ::exit() uses a canonical 1-1 idiom with a MEMBAR although some of
// the fast-path operators have been optimized so the common ::exit()
// operation is 1-0, e.g., see macroAssembler_x86.cpp: fast_unlock().
// The code emitted by fast_unlock() elides the usual MEMBAR.  This
// greatly improves latency -- MEMBAR and CAS having considerable local
// latency on modern processors -- but at the cost of "stranding".  Absent the
// MEMBAR, a thread in fast_unlock() can race a thread in the slow
// ::enter() path, resulting in the entering thread being stranding
// and a progress-liveness failure.   Stranding is extremely rare.
// We use timers (timed park operations) & periodic polling to detect
// and recover from stranding.  Potentially stranded threads periodically
// wake up and poll the lock.  See the usage of the _Responsible variable.
//
// The CAS() in enter provides for safety and exclusion, while the CAS or
// MEMBAR in exit provides for progress and avoids stranding.  1-0 locking
// eliminates the CAS/MEMBAR from the exit path, but it admits stranding.
// We detect and recover from stranding with timers.
//
// If a thread transiently strands it'll park until (a) another
// thread acquires the lock and then drops the lock, at which time the
// exiting thread will notice and unpark the stranded thread, or, (b)
// the timer expires.  If the lock is high traffic then the stranding latency
// will be low due to (a).  If the lock is low traffic then the odds of
// stranding are lower, although the worst-case stranding latency
// is longer.  Critically, we don't want to put excessive load in the
// platform's timer subsystem.  We want to minimize both the timer injection
// rate (timers created/sec) as well as the number of timers active at
// any one time.  (more precisely, we want to minimize timer-seconds, which is
// the integral of the # of active timers at any instant over time).
// Both impinge on OS scalability.  Given that, at most one thread parked on
// a monitor will use a timer.
//
// There is also the risk of a futile wake-up. If we drop the lock
// another thread can reacquire the lock immediately, and we can
// then wake a thread unnecessarily. This is benign, and we've
// structured the code so the windows are short and the frequency
// of such futile wakups is low.

void ObjectMonitor::exit(bool not_suspended, TRAPS) {
  Thread * const Self = THREAD;
  // 如果_owner不是当前线程
  if (THREAD != _owner) {
    // 当前线程是之前持有轻量级锁的线程。由轻量级锁膨胀后还没调用过enter方法，_owner会是指向Lock Record的指针。
    if (THREAD->is_lock_owned((address) _owner)) {
      // Transmute _owner from a BasicLock pointer to a Thread address.
      // We don't need to hold _mutex for this transition.
      // Non-null to Non-null is safe as long as all readers can
      // tolerate either flavor.
      assert(_recursions == 0, "invariant");
      _owner = THREAD;
      _recursions = 0;
    } else {
      // 异常情况:当前不是持有锁的线程
      // Apparent unbalanced locking ...
      // Naively we'd like to throw IllegalMonitorStateException.
      // As a practical matter we can neither allocate nor throw an
      // exception as ::exit() can be called from leaf routines.
      // see x86_32.ad Fast_Unlock() and the I1 and I2 properties.
      // Upon deeper reflection, however, in a properly run JVM the only
      // way we should encounter this situation is in the presence of
      // unbalanced JNI locking. TODO: CheckJNICalls.
      // See also: CR4414101
      TEVENT(Exit - Throw IMSX);
      assert(false, "Non-balanced monitor enter/exit! Likely JNI locking");
      return;
    }
  }

  // 重入计数器还不为0，则计数器-1后返回
  if (_recursions != 0) {
    _recursions--;        // this is simple recursive enter
    TEVENT(Inflated exit - recursive);
    return;
  }

  // _Responsible设置为null
  // Invariant: after setting Responsible=null an thread must execute
  // a MEMBAR or other serializing instruction before fetching EntryList|cxq.
  if ((SyncFlags & 4) == 0) {
    _Responsible = NULL;
  }

#if INCLUDE_JFR
  // get the owner's thread id for the MonitorEnter event
  // if it is enabled and the thread isn't suspended
  if (not_suspended && EventJavaMonitorEnter::is_enabled()) {
    _previous_owner_tid = JFR_THREAD_ID(Self);
  }
#endif

  for (;;) {
    assert(THREAD == _owner, "invariant");

    // Knob_ExitPolicy默认为0
    if (Knob_ExitPolicy == 0) {
      // release semantics: prior loads and stores from within the critical section
      // must not float (reorder) past the following store that drops the lock.
      // On SPARC that requires MEMBAR #loadstore|#storestore.
      // But of course in TSO #loadstore|#storestore is not required.
      // I'd like to write one of the following:
      // A.  OrderAccess::release() ; _owner = NULL
      // B.  OrderAccess::loadstore(); OrderAccess::storestore(); _owner = NULL;
      // Unfortunately OrderAccess::release() and OrderAccess::loadstore() both
      // store into a _dummy variable.  That store is not needed, but can result
      // in massive wasteful coherency traffic on classic SMP systems.
      // Instead, I use release_store(), which is implemented as just a simple
      // ST on x64, x86 and SPARC.
      // 先设置owner为null，即释放锁.
      // 这时如果有其他线程进入同步块则能获得锁,
      // 这是一个非公平锁的优化.
      OrderAccess::release_store(&_owner, (void*)NULL);   // drop the lock
      OrderAccess::storeload();                        // See if we need to wake a successor
      // 如果没有等待的线程或已经有假定继承人,直接返回,因为不需要唤醒其他线程.
      // 或者如果说_succ不为null，代表当前已经有个"醒着的"继承人线程，那当前线程不需要唤醒任何线程.
      if ((intptr_t(_EntryList)|intptr_t(_cxq)) == 0 || _succ != NULL) {
        TEVENT(Inflated exit - simple egress);
        return;
      }
      TEVENT(Inflated exit - complex egress);
      // Other threads are blocked trying to acquire the lock.

      // Normally the exiting thread is responsible for ensuring succession,
      // but if other successors are ready or other entering threads are spinning
      // then this thread can simply store NULL into _owner and exit without
      // waking a successor.  The existence of spinners or ready successors
      // guarantees proper succession (liveness).  Responsibility passes to the
      // ready or running successors.  The exiting thread delegates the duty.
      // More precisely, if a successor already exists this thread is absolved
      // of the responsibility of waking (unparking) one.
      //
      // The _succ variable is critical to reducing futile wakeup frequency.
      // _succ identifies the "heir presumptive" thread that has been made
      // ready (unparked) but that has not yet run.  We need only one such
      // successor thread to guarantee progress.
      // See http://www.usenix.org/events/jvm01/full_papers/dice/dice.pdf
      // section 3.3 "Futile Wakeup Throttling" for details.
      //
      // Note that spinners in Enter() also set _succ non-null.
      // In the current implementation spinners opportunistically set
      // _succ so that exiting threads might avoid waking a successor.
      // Another less appealing alternative would be for the exiting thread
      // to drop the lock and then spin briefly to see if a spinner managed
      // to acquire the lock.  If so, the exiting thread could exit
      // immediately without waking a successor, otherwise the exiting
      // thread would need to dequeue and wake a successor.
      // (Note that we'd need to make the post-drop spin short, but no
      // shorter than the worst-case round-trip cache-line migration time.
      // The dropped lock needs to become visible to the spinner, and then
      // the acquisition of the lock by the spinner must become visible to
      // the exiting thread).

      // It appears that an heir-presumptive (successor) must be made ready.
      // Only the current lock owner can manipulate the EntryList or
      // drain _cxq, so we need to reacquire the lock.  If we fail
      // to reacquire the lock the responsibility for ensuring succession
      // falls to the new owner.
      //
      // 因为之后要操作cxq和EntryList队列以及唤醒线程,
      // 所以需要重新获得锁，即设置_owner为当前线程.
      if (!Atomic::replace_if_null(THREAD, &_owner)) {
        return;
      }
      TEVENT(Exit - Reacquired);
    } else {
      if ((intptr_t(_EntryList)|intptr_t(_cxq)) == 0 || _succ != NULL) {
        OrderAccess::release_store(&_owner, (void*)NULL);   // drop the lock
        OrderAccess::storeload();
        // Ratify the previously observed values.
        if (_cxq == NULL || _succ != NULL) {
          TEVENT(Inflated exit - simple egress);
          return;
        }

        // inopportune interleaving -- the exiting thread (this thread)
        // in the fast-exit path raced an entering thread in the slow-enter
        // path.
        // We have two choices:
        // A.  Try to reacquire the lock.
        //     If the CAS() fails return immediately, otherwise
        //     we either restart/rerun the exit operation, or simply
        //     fall-through into the code below which wakes a successor.
        // B.  If the elements forming the EntryList|cxq are TSM
        //     we could simply unpark() the lead thread and return
        //     without having set _succ.
        if (!Atomic::replace_if_null(THREAD, &_owner)) {
          TEVENT(Inflated exit - reacquired succeeded);
          return;
        }
        TEVENT(Inflated exit - reacquired failed);
      } else {
        TEVENT(Inflated exit - complex egress);
      }
    }

    guarantee(_owner == THREAD, "invariant");

    ObjectWaiter * w = NULL;
    // 根据QMode的不同会有不同的唤醒策略，默认为0.
    // QMode = 2且cxq非空：取cxq队列队首的ObjectWaiter对象，
    //          调用ExitEpilog方法，该方法会唤醒该ObjectWaiter对象的线程，然后立即返回，后面的代码不会执行了；
    // QMode = 3且cxq非空：把cxq队列插入到EntryList的尾部；
    // QMode = 4且cxq非空：把cxq队列插入到EntryList的头部；
    // QMode = 0或1：暂时什么都不做，继续往下看.
    int QMode = Knob_QMode;

    if (QMode == 2 && _cxq != NULL) {
      // QMode == 2 : cxq中的线程有更高优先级，直接唤醒cxq的队首线程
      // QMode == 2 : cxq has precedence over EntryList.
      // Try to directly wake a successor from the cxq.
      // If successful, the successor will need to unlink itself from cxq.
      w = _cxq;
      assert(w != NULL, "invariant");
      assert(w->TState == ObjectWaiter::TS_CXQ, "Invariant");
      ExitEpilog(Self, w);
      return;
    }

    if (QMode == 3 && _cxq != NULL) {
      // QMode == 3 : 将cxq中的元素插入到EntryList的末尾
      // Aggressively drain cxq into EntryList at the first opportunity.
      // This policy ensure that recently-run threads live at the head of EntryList.
      // Drain _cxq into EntryList - bulk transfer.
      // First, detach _cxq.
      // The following loop is tantamount to: w = swap(&cxq, NULL)
      w = _cxq;
      for (;;) {
        assert(w != NULL, "Invariant");
        ObjectWaiter * u = Atomic::cmpxchg((ObjectWaiter*)NULL, &_cxq, w);
        if (u == w) break;
        w = u;
      }
      assert(w != NULL, "invariant");

      ObjectWaiter * q = NULL;
      ObjectWaiter * p;
      for (p = w; p != NULL; p = p->_next) {
        guarantee(p->TState == ObjectWaiter::TS_CXQ, "Invariant");
        p->TState = ObjectWaiter::TS_ENTER;
        p->_prev = q;
        q = p;
      }

      // Append the RATs to the EntryList
      // TODO: organize EntryList as a CDLL so we can locate the tail in constant-time.
      ObjectWaiter * Tail;
      for (Tail = _EntryList; Tail != NULL && Tail->_next != NULL;
           Tail = Tail->_next)
        /* empty */;
      if (Tail == NULL) {
        _EntryList = w;
      } else {
        Tail->_next = w;
        w->_prev = Tail;
      }

      // Fall thru into code that tries to wake a successor from EntryList
    }

    if (QMode == 4 && _cxq != NULL) {
      // QMode == 4 : 将cxq插入到EntryList的队首
      // Aggressively drain cxq into EntryList at the first opportunity.
      // This policy ensure that recently-run threads live at the head of EntryList.

      // Drain _cxq into EntryList - bulk transfer.
      // First, detach _cxq.
      // The following loop is tantamount to: w = swap(&cxq, NULL)
      w = _cxq;
      for (;;) {
        assert(w != NULL, "Invariant");
        ObjectWaiter * u = Atomic::cmpxchg((ObjectWaiter*)NULL, &_cxq, w);
        if (u == w) break;
        w = u;
      }
      assert(w != NULL, "invariant");

      ObjectWaiter * q = NULL;
      ObjectWaiter * p;
      for (p = w; p != NULL; p = p->_next) {
        guarantee(p->TState == ObjectWaiter::TS_CXQ, "Invariant");
        p->TState = ObjectWaiter::TS_ENTER;
        p->_prev = q;
        q = p;
      }

      // Prepend the RATs to the EntryList
      if (_EntryList != NULL) {
        q->_next = _EntryList;
        _EntryList->_prev = q;
      }
      _EntryList = w;

      // Fall thru into code that tries to wake a successor from EntryList
    }

    // 前面只有QMode=2的时候会提前返回，等于3、4的时候都会继续执行下面的逻辑;此外,对于QMode=0、1,也会先执行下面的逻辑：
    // 1.如果EntryList的首元素非空，就取出来调用ExitEpilog方法，该方法会唤醒该ObjectWaiter对象的线程，然后立即返回；
    // 2.如果EntryList的首元素为空，就将cxq的所有元素按其在cxq的原有顺序放入到EntryList中，
    //   然后再从EntryList中取出来队首元素执行ExitEpilog方法，然后立即返回.

    // 如果EntryList不为空，则直接唤醒EntryList的队首元素
    w = _EntryList;
    if (w != NULL) {
      // I'd like to write: guarantee (w->_thread != Self).
      // But in practice an exiting thread may find itself on the EntryList.
      // Let's say thread T1 calls O.wait().  Wait() enqueues T1 on O's waitset and
      // then calls exit().  Exit release the lock by setting O._owner to NULL.
      // Let's say T1 then stalls.  T2 acquires O and calls O.notify().  The
      // notify() operation moves T1 from O's waitset to O's EntryList. T2 then
      // release the lock "O".  T2 resumes immediately after the ST of null into
      // _owner, above.  T2 notices that the EntryList is populated, so it
      // reacquires the lock and then finds itself on the EntryList.
      // Given all that, we have to tolerate the circumstance where "w" is
      // associated with Self.
      assert(w->TState == ObjectWaiter::TS_ENTER, "invariant");
      ExitEpilog(Self, w);
      return;
    }

    // EntryList为null，则处理cxq中的元素
    // If we find that both _cxq and EntryList are null then just
    // re-run the exit protocol from the top.
    w = _cxq;
    if (w == NULL) continue;

    // 因为之后要将cxq的元素移动到EntryList，所以这里将cxq字段设置为null
    // Drain _cxq into EntryList - bulk transfer.
    // First, detach _cxq.
    // The following loop is tantamount to: w = swap(&cxq, NULL)
    for (;;) {
      assert(w != NULL, "Invariant");
      ObjectWaiter * u = Atomic::cmpxchg((ObjectWaiter*)NULL, &_cxq, w);
      if (u == w) break;
      w = u;
    }
    TEVENT(Inflated exit - drain cxq into EntryList);

    assert(w != NULL, "invariant");
    assert(_EntryList == NULL, "invariant");

    // Convert the LIFO SLL anchored by _cxq into a DLL.
    // The list reorganization step operates in O(LENGTH(w)) time.
    // It's critical that this step operate quickly as
    // "Self" still holds the outer-lock, restricting parallelism
    // and effectively lengthening the critical section.
    // Invariant: s chases t chases u.
    // TODO-FIXME: consider changing EntryList from a DLL to a CDLL so
    // we have faster access to the tail.

    if (QMode == 1) {
      // QMode == 1 : 将cxq中的元素转移到EntryList，并反转顺序
      // QMode == 1 : drain cxq to EntryList, reversing order
      // We also reverse the order of the list.
      ObjectWaiter * s = NULL;
      ObjectWaiter * t = w;
      ObjectWaiter * u = NULL;
      while (t != NULL) {
        guarantee(t->TState == ObjectWaiter::TS_CXQ, "invariant");
        t->TState = ObjectWaiter::TS_ENTER;
        u = t->_next;
        t->_prev = u;
        t->_next = s;
        s = t;
        t = u;
      }
      _EntryList  = s;
      assert(s != NULL, "invariant");
    } else {
      // QMode == 0 or QMode == 2
      // QMode == 0 或 QMode == 2 ???
      // 设置_EntryList的队头节点设置为cxq的队头节点,
      // 相当于将cxq中的元素按原顺序转移到EntryList.
      _EntryList = w;
      ObjectWaiter * q = NULL;
      ObjectWaiter * p;
      // 将原本的单向链表变成双向链表, 方便后面进行查询
      // 同时设置节点状态为TS_ENTER, 表明进入了_EntryList队列
      for (p = w; p != NULL; p = p->_next) {
        guarantee(p->TState == ObjectWaiter::TS_CXQ, "Invariant");
        p->TState = ObjectWaiter::TS_ENTER;
        p->_prev = q;
        q = p;
      }
    }

    // In 1-0 mode we need: ST EntryList; MEMBAR #storestore; ST _owner = NULL
    // The MEMBAR is satisfied by the release_store() operation in ExitEpilog().

    // _succ不为null，说明已经有个继承人了，所以不需要当前线程去唤醒，减少上下文切换的比率
    // See if we can abdicate to a spinner instead of waking a thread.
    // A primary goal of the implementation is to reduce the
    // context-switch rate.
    if (_succ != NULL) continue;

    // 将_EntryList队头的节点
    // 传递给ExitEpilog函数,
    // 将唤醒EntryList的头节点.
    w = _EntryList;
    if (w != NULL) {
      guarantee(w->TState == ObjectWaiter::TS_ENTER, "invariant");
      ExitEpilog(Self, w);
      return;
    }
  }
}

// ExitSuspendEquivalent:
// A faster alternate to handle_special_suspend_equivalent_condition()
//
// handle_special_suspend_equivalent_condition() unconditionally
// acquires the SR_lock.  On some platforms uncontended MutexLocker()
// operations have high latency.  Note that in ::enter() we call HSSEC
// while holding the monitor, so we effectively lengthen the critical sections.
//
// There are a number of possible solutions:
//
// A.  To ameliorate the problem we might also defer state transitions
//     to as late as possible -- just prior to parking.
//     Given that, we'd call HSSEC after having returned from park(),
//     but before attempting to acquire the monitor.  This is only a
//     partial solution.  It avoids calling HSSEC while holding the
//     monitor (good), but it still increases successor reacquisition latency --
//     the interval between unparking a successor and the time the successor
//     resumes and retries the lock.  See ReenterI(), which defers state transitions.
//     If we use this technique we can also avoid EnterI()-exit() loop
//     in ::enter() where we iteratively drop the lock and then attempt
//     to reacquire it after suspending.
//
// B.  In the future we might fold all the suspend bits into a
//     composite per-thread suspend flag and then update it with CAS().
//     Alternately, a Dekker-like mechanism with multiple variables
//     would suffice:
//       ST Self->_suspend_equivalent = false
//       MEMBAR
//       LD Self_>_suspend_flags
//
// UPDATE 2007-10-6: since I've replaced the native Mutex/Monitor subsystem
// with a more efficient implementation, the need to use "FastHSSEC" has
// decreased. - Dave


bool ObjectMonitor::ExitSuspendEquivalent(JavaThread * jSelf) {
  const int Mode = Knob_FastHSSEC;
  if (Mode && !jSelf->is_external_suspend()) {
    assert(jSelf->is_suspend_equivalent(), "invariant");
    jSelf->clear_suspend_equivalent();
    if (2 == Mode) OrderAccess::storeload();
    if (!jSelf->is_external_suspend()) return false;
    // We raced a suspension -- fall thru into the slow path
    TEVENT(ExitSuspendEquivalent - raced);
    jSelf->set_suspend_equivalent();
  }
  return jSelf->handle_special_suspend_equivalent_condition();
}


void ObjectMonitor::ExitEpilog(Thread * Self, ObjectWaiter * Wakee) {
  assert(_owner == Self, "invariant");

  // Exit protocol:
  // 1. ST _succ = wakee
  // 2. membar #loadstore|#storestore;
  // 2. ST _owner = NULL
  // 3. unpark(wakee)

  // 设置_succ为EntryList的头节点
  _succ = Knob_SuccEnabled ? Wakee->_thread : NULL;
  ParkEvent * Trigger = Wakee->_event;

  // Hygiene -- once we've set _owner = NULL we can't safely dereference Wakee again.
  // The thread associated with Wakee may have grabbed the lock and "Wakee" may be
  // out-of-scope (non-extant).
  Wakee  = NULL;

  // Drop the lock
  OrderAccess::release_store(&_owner, (void*)NULL);
  OrderAccess::fence();                               // ST _owner vs LD in unpark()

  if (SafepointMechanism::poll(Self)) {
    TEVENT(unpark before SAFEPOINT);
  }

  DTRACE_MONITOR_PROBE(contended__exit, this, object(), Self);
  // unpark线程
  Trigger->unpark();

  // Maintain stats and report events to JVMTI
  OM_PERFDATA_OP(Parks, inc());
}


// -----------------------------------------------------------------------------
// Class Loader deadlock handling.
//
// complete_exit exits a lock returning recursion count
// complete_exit/reenter operate as a wait without waiting
// complete_exit requires an inflated monitor
// The _owner field is not always the Thread addr even with an
// inflated monitor, e.g. the monitor can be inflated by a non-owning
// thread due to contention.
intptr_t ObjectMonitor::complete_exit(TRAPS) {
  Thread * const Self = THREAD;
  assert(Self->is_Java_thread(), "Must be Java thread!");
  JavaThread *jt = (JavaThread *)THREAD;

  DeferredInitialize();

  if (THREAD != _owner) {
    if (THREAD->is_lock_owned ((address)_owner)) {
      assert(_recursions == 0, "internal state error");
      _owner = THREAD;   // Convert from basiclock addr to Thread addr
      _recursions = 0;
    }
  }

  guarantee(Self == _owner, "complete_exit not owner");
  intptr_t save = _recursions; // record the old recursion count
  _recursions = 0;        // set the recursion level to be 0
  exit(true, Self);           // exit the monitor
  guarantee(_owner != Self, "invariant");
  return save;
}

// reenter() enters a lock and sets recursion count
// complete_exit/reenter operate as a wait without waiting
void ObjectMonitor::reenter(intptr_t recursions, TRAPS) {
  Thread * const Self = THREAD;
  assert(Self->is_Java_thread(), "Must be Java thread!");
  JavaThread *jt = (JavaThread *)THREAD;

  guarantee(_owner != Self, "reenter already owner");
  enter(THREAD);       // enter the monitor
  guarantee(_recursions == 0, "reenter recursion");
  _recursions = recursions;
  return;
}


// -----------------------------------------------------------------------------
// A macro is used below because there may already be a pending
// exception which should not abort the execution of the routines
// which use this (which is why we don't put this into check_slow and
// call it with a CHECK argument).

#define CHECK_OWNER()                                                       \
  do {                                                                      \
    if (THREAD != _owner) {                                                 \
      if (THREAD->is_lock_owned((address) _owner)) {                        \
        _owner = THREAD;  /* Convert from basiclock addr to Thread addr */  \
        _recursions = 0;                                                    \
      } else {                                                              \
        TEVENT(Throw IMSX);                                                 \
        THROW(vmSymbols::java_lang_IllegalMonitorStateException());         \
      }                                                                     \
    }                                                                       \
  } while (false)

// check_slow() is a misnomer.  It's called to simply to throw an IMSX exception.
// TODO-FIXME: remove check_slow() -- it's likely dead.

void ObjectMonitor::check_slow(TRAPS) {
  TEVENT(check_slow - throw IMSX);
  assert(THREAD != _owner && !THREAD->is_lock_owned((address) _owner), "must not be owner");
  THROW_MSG(vmSymbols::java_lang_IllegalMonitorStateException(), "current thread not owner");
}

static int Adjust(volatile int * adr, int dx) {
  int v;
  for (v = *adr; Atomic::cmpxchg(v + dx, adr, v) != v; v = *adr) /* empty */;
  return v;
}

static void post_monitor_wait_event(EventJavaMonitorWait* event,
                                    ObjectMonitor* monitor,
                                    jlong notifier_tid,
                                    jlong timeout,
                                    bool timedout) {
  assert(event != NULL, "invariant");
  assert(monitor != NULL, "invariant");
  event->set_monitorClass(((oop)monitor->object())->klass());
  event->set_timeout(timeout);
  event->set_address((uintptr_t)monitor->object_addr());
  event->set_notifier(notifier_tid);
  event->set_timedOut(timedout);
  event->commit();
}

// -----------------------------------------------------------------------------
// Wait/Notify/NotifyAll
//
// Note: a subset of changes to ObjectMonitor::wait()
// will need to be replicated in complete_exit
void ObjectMonitor::wait(jlong millis, bool interruptible, TRAPS) {
  Thread * const Self = THREAD;
  assert(Self->is_Java_thread(), "Must be Java thread!");
  JavaThread *jt = (JavaThread *)THREAD;

  DeferredInitialize();

  // Throw IMSX or IEX.
  CHECK_OWNER();

  EventJavaMonitorWait event;

  // 判断一下当前线程是否为可中断并且是否已经被中断
  // check for a pending interrupt
  if (interruptible && Thread::is_interrupted(Self, true) && !HAS_PENDING_EXCEPTION) {
    // post monitor waited event.  Note that this is past-tense, we are done waiting.
    if (JvmtiExport::should_post_monitor_waited()) {
      // Note: 'false' parameter is passed here because the
      // wait was not timed out due to thread interrupt.
      JvmtiExport::post_monitor_waited(jt, this, false);

      // In this short circuit of the monitor wait protocol, the
      // current thread never drops ownership of the monitor and
      // never gets added to the wait queue so the current thread
      // cannot be made the successor. This means that the
      // JVMTI_EVENT_MONITOR_WAITED event handler cannot accidentally
      // consume an unpark() meant for the ParkEvent associated with
      // this ObjectMonitor.
    }
    if (event.should_commit()) {
      post_monitor_wait_event(&event, this, 0, millis, false);
    }
    TEVENT(Wait - Throw IEX);
    // 抛出异常，不会直接进入等待
    THROW(vmSymbols::java_lang_InterruptedException());
    return;
  }

  TEVENT(Wait);

  assert(Self->_Stalled == 0, "invariant");
  Self->_Stalled = intptr_t(this);
  jt->set_current_waiting_monitor(this);

  // 首先会根据 Self 当前线程新建一个 ObjectWaiter 对象节点
  // create a node to be put into the queue
  // Critically, after we reset() the event but prior to park(), we must check
  // for a pending interrupt.
  ObjectWaiter node(Self);
  node.TState = ObjectWaiter::TS_WAIT;
  Self->_ParkEvent->reset();
  OrderAccess::fence();          // ST into Event; membar ; LD interrupted-flag

  // Enter the waiting queue, which is a circular doubly linked list in this case
  // but it could be a priority queue or any data structure.
  // _WaitSetLock protects the wait queue.  Normally the wait queue is accessed only
  // by the the owner of the monitor *except* in the case where park()
  // returns because of a timeout of interrupt.  Contention is exceptionally rare
  // so we use a simple spin-lock instead of a heavier-weight blocking lock.

  // 在自旋锁的保护下，
  Thread::SpinAcquire(&_WaitSetLock, "WaitSet - add");
  // 将 node 插入双向链表 WaitSet 的尾部,
  AddWaiter(&node);
  // 然后释放自旋锁.
  Thread::SpinRelease(&_WaitSetLock);

  if ((SyncFlags & 4) == 0) {
    _Responsible = NULL;
  }
  intptr_t save = _recursions; // record the old recursion count
  _waiters++;                  // increment the number of waiters
  _recursions = 0;             // set the recursion level to be 1
  // Java Object 的 wait 操作会释放 monitor 锁，释放操作就是这里实现的
  exit(true, Self);                    // exit the monitor
  guarantee(_owner != Self, "invariant");

  // 释放完锁，接下来就需要将当前线程进行 park 等待了
  // The thread is on the WaitSet list - now park() it.
  // On MP systems it's conceivable that a brief spin before we park
  // could be profitable.
  //
  // TODO-FIXME: change the following logic to a loop of the form
  //   while (!timeout && !interrupted && _notified == 0) park()

  int ret = OS_OK;
  int WasNotified = 0;
  // 设置Java Thread状态为OBJECT_WAIT,
  // 然后park线程.
  { // State transition wrappers
    OSThread* osthread = Self->osthread();
    OSThreadWaitState osts(osthread, true);
    {
      ThreadBlockInVM tbivm(jt);
      // Thread is in thread_blocked state and oop access is unsafe.
      jt->set_suspend_equivalent();

      // 在正式 park 之前，还会再一次看下是否有 interrupted
      if (interruptible && (Thread::is_interrupted(THREAD, false) || HAS_PENDING_EXCEPTION)) {
        // 如果有的话就会跳过 park 操作
        // Intentionally empty
      } else if (node._notified == 0) {
        if (millis <= 0) {
          Self->_ParkEvent->park();
        } else {
          ret = Self->_ParkEvent->park(millis);
        }
      }

      // were we externally suspended while we were waiting?
      if (ExitSuspendEquivalent (jt)) {
        // TODO-FIXME: add -- if succ == Self then succ = null.
        jt->java_suspend_self();
      }

    } // Exit thread safepoint: transition _thread_blocked -> _thread_in_vm

    // Node may be on the WaitSet, the EntryList (or cxq), or in transition
    // from the WaitSet to the EntryList.
    // See if we need to remove Node from the WaitSet.
    // We use double-checked locking to avoid grabbing _WaitSetLock
    // if the thread is not on the wait queue.
    //
    // Note that we don't need a fence before the fetch of TState.
    // In the worst case we'll fetch a old-stale value of TS_WAIT previously
    // written by the is thread. (perhaps the fetch might even be satisfied
    // by a look-aside into the processor's own store buffer, although given
    // the length of the code path between the prior ST and this load that's
    // highly unlikely).  If the following LD fetches a stale TS_WAIT value
    // then we'll acquire the lock and then re-fetch a fresh TState value.
    // That is, we fail toward safety.

    if (node.TState == ObjectWaiter::TS_WAIT) {
      Thread::SpinAcquire(&_WaitSetLock, "WaitSet - unlink");
      if (node.TState == ObjectWaiter::TS_WAIT) {
        DequeueSpecificWaiter(&node);       // unlink from WaitSet
        assert(node._notified == 0, "invariant");
        node.TState = ObjectWaiter::TS_RUN;
      }
      Thread::SpinRelease(&_WaitSetLock);
    }

    // The thread is now either on off-list (TS_RUN),
    // on the EntryList (TS_ENTER), or on the cxq (TS_CXQ).
    // The Node's TState variable is stable from the perspective of this thread.
    // No other threads will asynchronously modify TState.
    guarantee(node.TState != ObjectWaiter::TS_WAIT, "invariant");
    OrderAccess::loadload();
    if (_succ == Self) _succ = NULL;
    WasNotified = node._notified;

    // Reentry phase -- reacquire the monitor.
    // re-enter contended monitor after object.wait().
    // retain OBJECT_WAIT state until re-enter successfully completes
    // Thread state is thread_in_vm and oop access is again safe,
    // although the raw address of the object may have changed.
    // (Don't cache naked oops over safepoints, of course).

    // post monitor waited event. Note that this is past-tense, we are done waiting.
    if (JvmtiExport::should_post_monitor_waited()) {
      JvmtiExport::post_monitor_waited(jt, this, ret == OS_TIMEOUT);

      if (node._notified != 0 && _succ == Self) {
        // In this part of the monitor wait-notify-reenter protocol it
        // is possible (and normal) for another thread to do a fastpath
        // monitor enter-exit while this thread is still trying to get
        // to the reenter portion of the protocol.
        //
        // The ObjectMonitor was notified and the current thread is
        // the successor which also means that an unpark() has already
        // been done. The JVMTI_EVENT_MONITOR_WAITED event handler can
        // consume the unpark() that was done when the successor was
        // set because the same ParkEvent is shared between Java
        // monitors and JVM/TI RawMonitors (for now).
        //
        // We redo the unpark() to ensure forward progress, i.e., we
        // don't want all pending threads hanging (parked) with none
        // entering the unlocked monitor.
        node._event->unpark();
      }
    }

    if (event.should_commit()) {
      post_monitor_wait_event(&event, this, node._notifier_tid, millis, ret == OS_TIMEOUT);
    }

    OrderAccess::fence();

    assert(Self->_Stalled != 0, "invariant");
    Self->_Stalled = 0;

    assert(_owner != Self, "invariant");
    ObjectWaiter::TStates v = node.TState;
    if (v == ObjectWaiter::TS_RUN) {
      enter(Self);
    } else {
      guarantee(v == ObjectWaiter::TS_ENTER || v == ObjectWaiter::TS_CXQ, "invariant");
      ReenterI(Self, &node);
      node.wait_reenter_end(this);
    }

    // Self has reacquired the lock.
    // Lifecycle - the node representing Self must not appear on any queues.
    // Node is about to go out-of-scope, but even if it were immortal we wouldn't
    // want residual elements associated with this thread left on any lists.
    guarantee(node.TState == ObjectWaiter::TS_RUN, "invariant");
    assert(_owner == Self, "invariant");
    assert(_succ != Self, "invariant");
  } // OSThreadWaitState()

  jt->set_current_waiting_monitor(NULL);

  guarantee(_recursions == 0, "invariant");
  _recursions = save;     // restore the old recursion count
  _waiters--;             // decrement the number of waiters

  // Verify a few postconditions
  assert(_owner == Self, "invariant");
  assert(_succ != Self, "invariant");
  assert(((oop)(object()))->mark() == markOopDesc::encode(this), "invariant");

  if (SyncFlags & 32) {
    OrderAccess::fence();
  }

  // check if the notification happened
  if (!WasNotified) {
    // no, it could be timeout or Thread.interrupt() or both
    // check for interrupt event, otherwise it is timeout
    if (interruptible && Thread::is_interrupted(Self, true) && !HAS_PENDING_EXCEPTION) {
      TEVENT(Wait - throw IEX from epilog);
      THROW(vmSymbols::java_lang_InterruptedException());
    }
  }

  // NOTE: Spurious wake up will be consider as timeout.
  // Monitor notify has precedence over thread interrupt.
}


// Consider:
// If the lock is cool (cxq == null && succ == null) and we're on an MP system
// then instead of transferring a thread from the WaitSet to the EntryList
// we might just dequeue a thread from the WaitSet and directly unpark() it.
//
// 首先会从 WaitSet 队列中出队一个节点，然后针对这个节点根据
// Knob_MoveNotifyee 来决定执行不同策略逻辑:
// 策略 0：将需要唤醒的 node 放到 EntryList 的头部;
// 策略 1：将需要唤醒的 node 放到 EntryList 的尾部;
// 策略 2：将需要唤醒的 node 放到 CXQ 的头部; (PS: EntryList为空的话，第一个被notify的线程会进入到EntryList;后面的放到 CXQ 的头部)
// 策略 3：将需要唤醒的 node 放到 CXQ 的尾部.
// 默认为策略2.
// 你会发现这里全是队列的操作，并没有唤醒线程，
// 真正的唤醒操作在exit中.
void ObjectMonitor::INotify(Thread * Self) {
  const int policy = Knob_MoveNotifyee;

  Thread::SpinAcquire(&_WaitSetLock, "WaitSet - notify");
  // 将 WaitSet 队列中的第一个 node 出队
  ObjectWaiter * iterator = DequeueWaiter();
  if (iterator != NULL) {
    TEVENT(Notify1 - Transfer);
    guarantee(iterator->TState == ObjectWaiter::TS_WAIT, "invariant");
    guarantee(iterator->_notified == 0, "invariant");
    // Disposition - what might we do with iterator ?
    // a.  add it directly to the EntryList - either tail (policy == 1)
    //     or head (policy == 0).
    // b.  push it onto the front of the _cxq (policy == 2).
    // For now we use (b).
    if (policy != 4) {
      iterator->TState = ObjectWaiter::TS_ENTER;
    }
    iterator->_notified = 1;
    iterator->_notifier_tid = JFR_THREAD_ID(Self);

    ObjectWaiter * list = _EntryList;
    if (list != NULL) {
      assert(list->_prev == NULL, "invariant");
      assert(list->TState == ObjectWaiter::TS_ENTER, "invariant");
      assert(list != iterator, "invariant");
    }

    if (policy == 0) {       // prepend to EntryList
      if (list == NULL) {
        iterator->_next = iterator->_prev = NULL;
        _EntryList = iterator;
      } else {
        list->_prev = iterator;
        iterator->_next = list;
        iterator->_prev = NULL;
        _EntryList = iterator;
      }
    } else if (policy == 1) {      // append to EntryList
      if (list == NULL) {
        iterator->_next = iterator->_prev = NULL;
        _EntryList = iterator;
      } else {
        // CONSIDER:  finding the tail currently requires a linear-time walk of
        // the EntryList.  We can make tail access constant-time by converting to
        // a CDLL instead of using our current DLL.
        ObjectWaiter * tail;
        for (tail = list; tail->_next != NULL; tail = tail->_next) {}
        assert(tail != NULL && tail->_next == NULL, "invariant");
        tail->_next = iterator;
        iterator->_prev = tail;
        iterator->_next = NULL;
      }
    } else if (policy == 2) {      // prepend to cxq
      if (list == NULL) {
        iterator->_next = iterator->_prev = NULL;
        _EntryList = iterator;
      } else {
        iterator->TState = ObjectWaiter::TS_CXQ;
        for (;;) {
          ObjectWaiter * front = _cxq;
          iterator->_next = front;
          if (Atomic::cmpxchg(iterator, &_cxq, front) == front) {
            break;
          }
        }
      }
    } else if (policy == 3) {      // append to cxq
      iterator->TState = ObjectWaiter::TS_CXQ;
      for (;;) {
        ObjectWaiter * tail = _cxq;
        if (tail == NULL) {
          iterator->_next = NULL;
          if (Atomic::replace_if_null(iterator, &_cxq)) {
            break;
          }
        } else {
          while (tail->_next != NULL) tail = tail->_next;
          tail->_next = iterator;
          iterator->_prev = tail;
          iterator->_next = NULL;
          break;
        }
      }
    } else {
      ParkEvent * ev = iterator->_event;
      iterator->TState = ObjectWaiter::TS_RUN;
      OrderAccess::fence();
      ev->unpark();
    }

    // _WaitSetLock protects the wait queue, not the EntryList.  We could
    // move the add-to-EntryList operation, above, outside the critical section
    // protected by _WaitSetLock.  In practice that's not useful.  With the
    // exception of  wait() timeouts and interrupts the monitor owner
    // is the only thread that grabs _WaitSetLock.  There's almost no contention
    // on _WaitSetLock so it's not profitable to reduce the length of the
    // critical section.

    if (policy < 4) {
      iterator->wait_reenter_begin(this);
    }
  }
  Thread::SpinRelease(&_WaitSetLock);
}

// Consider: a not-uncommon synchronization bug is to use notify() when
// notifyAll() is more appropriate, potentially resulting in stranded
// threads; this is one example of a lost wakeup. A useful diagnostic
// option is to force all notify() operations to behave as notifyAll().
//
// Note: We can also detect many such problems with a "minimum wait".
// When the "minimum wait" is set to a small non-zero timeout value
// and the program does not hang whereas it did absent "minimum wait",
// that suggests a lost wakeup bug. The '-XX:SyncFlags=1' option uses
// a "minimum wait" for all park() operations; see the recheckInterval
// variable and MAX_RECHECK_INTERVAL.

void ObjectMonitor::notify(TRAPS) {
  CHECK_OWNER();
  // 先会检查 WaitSet 队列是否为空
  if (_WaitSet == NULL) {
    TEVENT(Empty-Notify);
    return;
  }
  // 不为空表示有线程在这个 monitor 上 wait 了
  DTRACE_MONITOR_PROBE(notify, this, object(), THREAD);
  INotify(THREAD);  // 通过INotify唤醒某个线程
  OM_PERFDATA_OP(Notifications, inc(1));
}


// The current implementation of notifyAll() transfers the waiters one-at-a-time
// from the waitset to the EntryList. This could be done more efficiently with a
// single bulk transfer but in practice it's not time-critical. Beware too,
// that in prepend-mode we invert the order of the waiters. Let's say that the
// waitset is "ABCD" and the EntryList is "XYZ". After a notifyAll() in prepend
// mode the waitset will be empty and the EntryList will be "DCBAXYZ".
// notifyAll 的实现其实和 notify 实现大同小异,
// 其实就是根据 WaitSet 长度，反复调用 INotify 函数，
// 相当于多次调用 notify.
void ObjectMonitor::notifyAll(TRAPS) {
  CHECK_OWNER();
  if (_WaitSet == NULL) {
    TEVENT(Empty-NotifyAll);
    return;
  }

  DTRACE_MONITOR_PROBE(notifyAll, this, object(), THREAD);
  int tally = 0;
  while (_WaitSet != NULL) {
    tally++;
    INotify(THREAD);
  }

  OM_PERFDATA_OP(Notifications, inc(tally));
}

// -----------------------------------------------------------------------------
// Adaptive Spinning Support
// 自适应自旋的实现
//
// Adaptive spin-then-block - rational spinning
// 自适应自旋后才尝试阻塞 —— 即 合理地自旋
//
// 我们在_owner字段上进行全局的自旋，使用经典的
// 对称多处理机(SMP) test and test and set(TATAS) 算法.
//
// void acquireLock(bool *lock) {
//    do {
//          while (*lock) { }
//    } while (testAndSet(lock));
//  }
//
// 在高阶的对称多处理机系统(SMP)上， 最好是先短暂地全局自旋，然后再恢复为局部自旋.
// 根据MCS/CLH队列(想想AQS)的算法思想，一个竞争线程可以将自己入队到cxq队列中，
// 然后在线程私有的变量(比如说ParkEvent._Event标志)上进行局部自旋.
// 这些留给读者自行研究.
// Note that we spin "globally" on _owner with a classic SMP-polite TATAS
// algorithm.  On high order SMP systems it would be better to start with
// a brief global spin and then revert to spinning locally.  In the spirit of MCS/CLH,
// a contending thread could enqueue itself on the cxq and then spin locally
// on a thread-specific variable such as its ParkEvent._Event flag.
// That's left as an exercise for the reader.  Note that global spinning is
// not problematic on Niagara, as the L2 cache serves the interconnect and
// has both low latency and massive bandwidth.
//
// 我们可以设置自旋的频率为100%，然后变动自旋次数(自旋时间);
// 也可以将自旋次数设置为接近于（线程）上下文切换的时间，然后变动自旋的频率;
// 当然也可以两者都变动，但是要满足 K == Frequency * Duration , 其中 K 由monitor自适应调整.
// 其中自旋的频率，即竞争锁获取操作的尝试次数占我们设置的自旋次数的百分比.
// 下面的实现选用第一种逻辑.
// Broadly, we can fix the spin frequency -- that is, the % of contended lock
// acquisition attempts where we opt to spin --  at 100% and vary the spin count
// (duration) or we can fix the count at approximately the duration of
// a context switch and vary the frequency.   Of course we could also
// vary both satisfying K == Frequency * Duration, where K is adaptive by monitor.
// For a description of 'Adaptive spin-then-block mutual exclusion in
// multi-threaded processing,' see U.S. Pat. No. 8046758.
//
// 本实现会变动自旋次数"D"， 它根据最近的自旋尝试的成功率来变动.
// （D 的最大值近似于一次线程的往返上下文切换时间）. 最近自旋尝试的成功率是
// 未来自旋尝试成功率的一个很好的预测。 这个机制会自动适应变动的临界区长度（锁模式）、
// 系统负载和并行程度。 D 由每个monitor的_SpinDuration字段来维护， 并且它会被
// 初始化为一个比较乐观的值。本实现中，自旋频率被设置在了100%.
// This implementation varies the duration "D", where D varies with
// the success rate of recent spin attempts. (D is capped at approximately
// length of a round-trip context switch).  The success rate for recent
// spin attempts is a good predictor of the success rate of future spin
// attempts.  The mechanism adapts automatically to varying critical
// section length (lock modality), system load and degree of parallelism.
// D is maintained per-monitor in _SpinDuration and is initialized
// optimistically.  Spin frequency is fixed at 100%.
//
// 注意，_SpinDuration字段是volatile的，但是我们在更新它的时候没有加锁或使用原子性操作.
// 实现的代码经过设计，因此尽管存在竞争，_SpinDuration也能保持在一个合理的范围里。
// 尽管在最坏的情况会引入一些不确定性，但是由于自旋时间非常短，故在此极端情况下也是无害的。
// Note that _SpinDuration is volatile, but we update it without locks
// or atomics.  The code is designed so that _SpinDuration stays within
// a reasonable range even in the presence of races.  The arithmetic
// operations on _SpinDuration are closed over the domain of legal values,
// so at worst a race will install and older but still legal value.
// At the very worst this introduces some apparent non-determinism.
// We might spin when we shouldn't or vice-versa, but since the spin
// count are relatively short, even in the worst case, the effect is harmless.
//
// 注意，较低的“D”值不会成为"吸收态"(数学术语). 短暂的自旋失败不会影响自旋整体的优势.
// Care must be taken that a low "D" value does not become an
// an absorbing state.  Transient spinning failures -- when spinning
// is overall profitable -- should not cause the system to converge
// on low "D" values.  We want spinning to be stable and predictable
// and fairly responsive to change and at the same time we don't want
// it to oscillate, become metastable, be "too" non-deterministic,
// or converge on or enter undesirable stable absorbing states.
//
// 我们实现了一个基于反馈的控制系统——使用过去的行为来预测未来的行为.
// 对于系统的一些”无伤大雅“的问题，从全局来看无需担心，因此我们也没有添加过分的优化机制来避免这些问题.
// We implement a feedback-based control system -- using past behavior
// to predict future behavior.  We face two issues: (a) if the
// input signal is random then the spin predictor won't provide optimal
// results, and (b) if the signal frequency is too high then the control
// system, which has some natural response lag, will "chase" the signal.
// (b) can arise from multimodal lock hold times.  Transient preemption
// can also result in apparent bimodal lock hold times.
// Although sub-optimal, neither condition is particularly harmful, as
// in the worst-case we'll spin when we shouldn't or vice-versa.
// The maximum spin duration is rather short so the failure modes aren't bad.
// To be conservative, I've tuned the gain in system to bias toward
// _not spinning.  Relatedly, the system can sometimes enter a mode where it
// "rings" or oscillates between spinning and not spinning.  This happens
// when spinning is just on the cusp of profitability, however, so the
// situation is not dire.  The state is benign -- there's no need to add
// hysteresis control to damp the transition rate between spinning and
// not spinning.

// Spinning: Fixed frequency (100%), vary duration
int ObjectMonitor::TrySpin(Thread * Self) {
  // Dumb, brutal spin.  Good for comparative measurements against adaptive spinning.
  int ctr = Knob_FixedSpin;
  if (ctr != 0) {
    while (--ctr >= 0) {
      if (TryLock(Self) > 0) return 1;
      SpinPause();
    }
    return 0;
  }

  for (ctr = Knob_PreSpin + 1; --ctr >= 0;) {
    if (TryLock(Self) > 0) {
      // 如果本次自旋获取锁成功,
      // 则加大_SpinDuration值，
      // 下次该对象获取锁可以多自旋一会.
      // Increase _SpinDuration ...
      // Note that we don't clamp SpinDuration precisely at SpinLimit.
      // Raising _SpurDuration to the poverty line is key.
      int x = _SpinDuration;
      if (x < Knob_SpinLimit) {
        if (x < Knob_Poverty) x = Knob_Poverty;
        _SpinDuration = x + Knob_BonusB;
      }
      return 1;
    }
    // pause 指令，用来提升退出自旋后CPU的性能.
    SpinPause();
  }

  // Admission control - verify preconditions for spinning
  //
  // We always spin a little bit, just to prevent _SpinDuration == 0 from
  // becoming an absorbing state.  Put another way, we spin briefly to
  // sample, just in case the system load, parallelism, contention, or lock
  // modality changed.
  //
  // Consider the following alternative:
  // Periodically set _SpinDuration = _SpinLimit and try a long/full
  // spin attempt.  "Periodically" might mean after a tally of
  // the # of failed spin attempts (or iterations) reaches some threshold.
  // This takes us into the realm of 1-out-of-N spinning, where we
  // hold the duration constant but vary the frequency.

  ctr = _SpinDuration;
  if (ctr < Knob_SpinBase) ctr = Knob_SpinBase;
  if (ctr <= 0) return 0;

  if (Knob_SuccRestrict && _succ != NULL) return 0;
  if (Knob_OState && NotRunnable (Self, (Thread *) _owner)) {
    TEVENT(Spin abort - notrunnable [TOP]);
    return 0;
  }

  int MaxSpin = Knob_MaxSpinners;
  if (MaxSpin >= 0) {
    if (_Spinner > MaxSpin) {
      TEVENT(Spin abort -- too many spinners);
      return 0;
    }
    // Slightly racy, but benign ...
    Adjust(&_Spinner, 1);
  }

  // We're good to spin ... spin ingress.
  // CONSIDER: use Prefetch::write() to avoid RTS->RTO upgrades
  // when preparing to LD...CAS _owner, etc and the CAS is likely
  // to succeed.
  int hits    = 0;
  int msk     = 0;
  int caspty  = Knob_CASPenalty;
  int oxpty   = Knob_OXPenalty;
  int sss     = Knob_SpinSetSucc;
  if (sss && _succ == NULL) _succ = Self;
  Thread * prv = NULL;

  // There are three ways to exit the following loop:
  // 1.  A successful spin where this thread has acquired the lock.
  // 2.  Spin failure with prejudice
  // 3.  Spin failure without prejudice

  while (--ctr >= 0) {

    // Periodic polling -- Check for pending GC
    // Threads may spin while they're unsafe.
    // We don't want spinning threads to delay the JVM from reaching
    // a stop-the-world safepoint or to steal cycles from GC.
    // If we detect a pending safepoint we abort in order that
    // (a) this thread, if unsafe, doesn't delay the safepoint, and (b)
    // this thread, if safe, doesn't steal cycles from GC.
    // This is in keeping with the "no loitering in runtime" rule.
    // We periodically check to see if there's a safepoint pending.
    if ((ctr & 0xFF) == 0) {
      if (SafepointMechanism::poll(Self)) {
        TEVENT(Spin: safepoint);
        goto Abort;           // abrupt spin egress
      }
      if (Knob_UsePause & 1) SpinPause();
    }

    if (Knob_UsePause & 2) SpinPause();

    // Exponential back-off ...  Stay off the bus to reduce coherency traffic.
    // This is useful on classic SMP systems, but is of less utility on
    // N1-style CMT platforms.
    //
    // Trade-off: lock acquisition latency vs coherency bandwidth.
    // Lock hold times are typically short.  A histogram
    // of successful spin attempts shows that we usually acquire
    // the lock early in the spin.  That suggests we want to
    // sample _owner frequently in the early phase of the spin,
    // but then back-off and sample less frequently as the spin
    // progresses.  The back-off makes a good citizen on SMP big
    // SMP systems.  Oversampling _owner can consume excessive
    // coherency bandwidth.  Relatedly, if we _oversample _owner we
    // can inadvertently interfere with the the ST m->owner=null.
    // executed by the lock owner.
    if (ctr & msk) continue;
    ++hits;
    if ((hits & 0xF) == 0) {
      // The 0xF, above, corresponds to the exponent.
      // Consider: (msk+1)|msk
      msk = ((msk << 2)|3) & BackOffMask;
    }

    // Probe _owner with TATAS
    // If this thread observes the monitor transition or flicker
    // from locked to unlocked to locked, then the odds that this
    // thread will acquire the lock in this spin attempt go down
    // considerably.  The same argument applies if the CAS fails
    // or if we observe _owner change from one non-null value to
    // another non-null value.   In such cases we might abort
    // the spin without prejudice or apply a "penalty" to the
    // spin count-down variable "ctr", reducing it by 100, say.

    Thread * ox = (Thread *) _owner;
    if (ox == NULL) {
      ox = (Thread*)Atomic::cmpxchg(Self, &_owner, (void*)NULL);
      if (ox == NULL) {
        // The CAS succeeded -- this thread acquired ownership
        // Take care of some bookkeeping to exit spin state.
        if (sss && _succ == Self) {
          _succ = NULL;
        }
        if (MaxSpin > 0) Adjust(&_Spinner, -1);

        // Increase _SpinDuration :
        // The spin was successful (profitable) so we tend toward
        // longer spin attempts in the future.
        // CONSIDER: factor "ctr" into the _SpinDuration adjustment.
        // If we acquired the lock early in the spin cycle it
        // makes sense to increase _SpinDuration proportionally.
        // Note that we don't clamp SpinDuration precisely at SpinLimit.
        int x = _SpinDuration;
        if (x < Knob_SpinLimit) {
          if (x < Knob_Poverty) x = Knob_Poverty;
          _SpinDuration = x + Knob_Bonus;
        }
        return 1;
      }

      // The CAS failed ... we can take any of the following actions:
      // * penalize: ctr -= Knob_CASPenalty
      // * exit spin with prejudice -- goto Abort;
      // * exit spin without prejudice.
      // * Since CAS is high-latency, retry again immediately.
      prv = ox;
      TEVENT(Spin: cas failed);
      if (caspty == -2) break;
      if (caspty == -1) goto Abort;
      ctr -= caspty;
      continue;
    }

    // Did lock ownership change hands ?
    if (ox != prv && prv != NULL) {
      TEVENT(spin: Owner changed)
      if (oxpty == -2) break;
      if (oxpty == -1) goto Abort;
      ctr -= oxpty;
    }
    prv = ox;

    // Abort the spin if the owner is not executing.
    // The owner must be executing in order to drop the lock.
    // Spinning while the owner is OFFPROC is idiocy.
    // Consider: ctr -= RunnablePenalty ;
    if (Knob_OState && NotRunnable (Self, ox)) {
      TEVENT(Spin abort - notrunnable);
      goto Abort;
    }
    if (sss && _succ == NULL) _succ = Self;
  }

  // Spin failed with prejudice -- reduce _SpinDuration.
  // TODO: Use an AIMD-like policy to adjust _SpinDuration.
  // AIMD is globally stable.
  TEVENT(Spin failure);
  {
    int x = _SpinDuration;
    if (x > 0) {
      // Consider an AIMD scheme like: x -= (x >> 3) + 100
      // This is globally sample and tends to damp the response.
      x -= Knob_Penalty;
      if (x < 0) x = 0;
      _SpinDuration = x;
    }
  }

 Abort:
  if (MaxSpin >= 0) Adjust(&_Spinner, -1);
  if (sss && _succ == Self) {
    _succ = NULL;
    // Invariant: after setting succ=null a contending thread
    // must recheck-retry _owner before parking.  This usually happens
    // in the normal usage of TrySpin(), but it's safest
    // to make TrySpin() as foolproof as possible.
    OrderAccess::fence();
    if (TryLock(Self) > 0) return 1;
  }
  return 0;
}

// NotRunnable() -- informed spinning
//
// Don't bother spinning if the owner is not eligible to drop the lock.
// Peek at the owner's schedctl.sc_state and Thread._thread_values and
// spin only if the owner thread is _thread_in_Java or _thread_in_vm.
// The thread must be runnable in order to drop the lock in timely fashion.
// If the _owner is not runnable then spinning will not likely be
// successful (profitable).
//
// Beware -- the thread referenced by _owner could have died
// so a simply fetch from _owner->_thread_state might trap.
// Instead, we use SafeFetchXX() to safely LD _owner->_thread_state.
// Because of the lifecycle issues the schedctl and _thread_state values
// observed by NotRunnable() might be garbage.  NotRunnable must
// tolerate this and consider the observed _thread_state value
// as advisory.
//
// Beware too, that _owner is sometimes a BasicLock address and sometimes
// a thread pointer.
// Alternately, we might tag the type (thread pointer vs basiclock pointer)
// with the LSB of _owner.  Another option would be to probablistically probe
// the putative _owner->TypeTag value.
//
// Checking _thread_state isn't perfect.  Even if the thread is
// in_java it might be blocked on a page-fault or have been preempted
// and sitting on a ready/dispatch queue.  _thread state in conjunction
// with schedctl.sc_state gives us a good picture of what the
// thread is doing, however.
//
// TODO: check schedctl.sc_state.
// We'll need to use SafeFetch32() to read from the schedctl block.
// See RFE #5004247 and http://sac.sfbay.sun.com/Archives/CaseLog/arc/PSARC/2005/351/
//
// The return value from NotRunnable() is *advisory* -- the
// result is based on sampling and is not necessarily coherent.
// The caller must tolerate false-negative and false-positive errors.
// Spinning, in general, is probabilistic anyway.


int ObjectMonitor::NotRunnable(Thread * Self, Thread * ox) {
  // Check ox->TypeTag == 2BAD.
  if (ox == NULL) return 0;

  // Avoid transitive spinning ...
  // Say T1 spins or blocks trying to acquire L.  T1._Stalled is set to L.
  // Immediately after T1 acquires L it's possible that T2, also
  // spinning on L, will see L.Owner=T1 and T1._Stalled=L.
  // This occurs transiently after T1 acquired L but before
  // T1 managed to clear T1.Stalled.  T2 does not need to abort
  // its spin in this circumstance.
  intptr_t BlockedOn = SafeFetchN((intptr_t *) &ox->_Stalled, intptr_t(1));

  if (BlockedOn == 1) return 1;
  if (BlockedOn != 0) {
    return BlockedOn != intptr_t(this) && _owner == ox;
  }

  assert(sizeof(((JavaThread *)ox)->_thread_state == sizeof(int)), "invariant");
  int jst = SafeFetch32((int *) &((JavaThread *) ox)->_thread_state, -1);;
  // consider also: jst != _thread_in_Java -- but that's overspecific.
  return jst == _thread_blocked || jst == _thread_in_native;
}


// -----------------------------------------------------------------------------
// WaitSet management ...

ObjectWaiter::ObjectWaiter(Thread* thread) {
  _next     = NULL;
  _prev     = NULL;
  _notified = 0;
  _notifier_tid = 0;
  TState    = TS_RUN;
  _thread   = thread;
  _event    = thread->_ParkEvent;
  _active   = false;
  assert(_event != NULL, "invariant");
}

void ObjectWaiter::wait_reenter_begin(ObjectMonitor * const mon) {
  JavaThread *jt = (JavaThread *)this->_thread;
  _active = JavaThreadBlockedOnMonitorEnterState::wait_reenter_begin(jt, mon);
}

void ObjectWaiter::wait_reenter_end(ObjectMonitor * const mon) {
  JavaThread *jt = (JavaThread *)this->_thread;
  JavaThreadBlockedOnMonitorEnterState::wait_reenter_end(jt, _active);
}

inline void ObjectMonitor::AddWaiter(ObjectWaiter* node) {
  assert(node != NULL, "should not add NULL node");
  assert(node->_prev == NULL, "node already in list");
  assert(node->_next == NULL, "node already in list");
  // put node at end of queue (circular doubly linked list)
  if (_WaitSet == NULL) {
    _WaitSet = node;
    node->_prev = node;
    node->_next = node;
  } else {
    ObjectWaiter* head = _WaitSet;
    ObjectWaiter* tail = head->_prev;
    assert(tail->_next == head, "invariant check");
    tail->_next = node;
    head->_prev = node;
    node->_next = head;
    node->_prev = tail;
  }
}

inline ObjectWaiter* ObjectMonitor::DequeueWaiter() {
  // dequeue the very first waiter
  ObjectWaiter* waiter = _WaitSet;
  if (waiter) {
    DequeueSpecificWaiter(waiter);
  }
  return waiter;
}

inline void ObjectMonitor::DequeueSpecificWaiter(ObjectWaiter* node) {
  assert(node != NULL, "should not dequeue NULL node");
  assert(node->_prev != NULL, "node already removed from list");
  assert(node->_next != NULL, "node already removed from list");
  // when the waiter has woken up because of interrupt,
  // timeout or other spurious wake-up, dequeue the
  // waiter from waiting list
  ObjectWaiter* next = node->_next;
  if (next == node) {
    assert(node->_prev == node, "invariant check");
    _WaitSet = NULL;
  } else {
    ObjectWaiter* prev = node->_prev;
    assert(prev->_next == node, "invariant check");
    assert(next->_prev == node, "invariant check");
    next->_prev = prev;
    prev->_next = next;
    if (_WaitSet == node) {
      _WaitSet = next;
    }
  }
  node->_next = NULL;
  node->_prev = NULL;
}

// -----------------------------------------------------------------------------
// PerfData support
PerfCounter * ObjectMonitor::_sync_ContendedLockAttempts       = NULL;
PerfCounter * ObjectMonitor::_sync_FutileWakeups               = NULL;
PerfCounter * ObjectMonitor::_sync_Parks                       = NULL;
PerfCounter * ObjectMonitor::_sync_Notifications               = NULL;
PerfCounter * ObjectMonitor::_sync_Inflations                  = NULL;
PerfCounter * ObjectMonitor::_sync_Deflations                  = NULL;
PerfLongVariable * ObjectMonitor::_sync_MonExtant              = NULL;

// One-shot global initialization for the sync subsystem.
// We could also defer initialization and initialize on-demand
// the first time we call inflate().  Initialization would
// be protected - like so many things - by the MonitorCache_lock.

void ObjectMonitor::Initialize() {
  static int InitializationCompleted = 0;
  assert(InitializationCompleted == 0, "invariant");
  InitializationCompleted = 1;
  if (UsePerfData) {
    EXCEPTION_MARK;
#define NEWPERFCOUNTER(n)                                                \
  {                                                                      \
    n = PerfDataManager::create_counter(SUN_RT, #n, PerfData::U_Events,  \
                                        CHECK);                          \
  }
#define NEWPERFVARIABLE(n)                                                \
  {                                                                       \
    n = PerfDataManager::create_variable(SUN_RT, #n, PerfData::U_Events,  \
                                         CHECK);                          \
  }
    NEWPERFCOUNTER(_sync_Inflations);
    NEWPERFCOUNTER(_sync_Deflations);
    NEWPERFCOUNTER(_sync_ContendedLockAttempts);
    NEWPERFCOUNTER(_sync_FutileWakeups);
    NEWPERFCOUNTER(_sync_Parks);
    NEWPERFCOUNTER(_sync_Notifications);
    NEWPERFVARIABLE(_sync_MonExtant);
#undef NEWPERFCOUNTER
#undef NEWPERFVARIABLE
  }
}

static char * kvGet(char * kvList, const char * Key) {
  if (kvList == NULL) return NULL;
  size_t n = strlen(Key);
  char * Search;
  for (Search = kvList; *Search; Search += strlen(Search) + 1) {
    if (strncmp (Search, Key, n) == 0) {
      if (Search[n] == '=') return Search + n + 1;
      if (Search[n] == 0)   return(char *) "1";
    }
  }
  return NULL;
}

static int kvGetInt(char * kvList, const char * Key, int Default) {
  char * v = kvGet(kvList, Key);
  int rslt = v ? ::strtol(v, NULL, 0) : Default;
  if (Knob_ReportSettings && v != NULL) {
    tty->print_cr("INFO: SyncKnob: %s %d(%d)", Key, rslt, Default) ;
    tty->flush();
  }
  return rslt;
}

void ObjectMonitor::DeferredInitialize() {
  if (InitDone > 0) return;
  if (Atomic::cmpxchg (-1, &InitDone, 0) != 0) {
    while (InitDone != 1) /* empty */;
    return;
  }

  // One-shot global initialization ...
  // The initialization is idempotent, so we don't need locks.
  // In the future consider doing this via os::init_2().
  // SyncKnobs consist of <Key>=<Value> pairs in the style
  // of environment variables.  Start by converting ':' to NUL.

  if (SyncKnobs == NULL) SyncKnobs = "";

  size_t sz = strlen(SyncKnobs);
  char * knobs = (char *) os::malloc(sz + 2, mtInternal);
  if (knobs == NULL) {
    vm_exit_out_of_memory(sz + 2, OOM_MALLOC_ERROR, "Parse SyncKnobs");
    guarantee(0, "invariant");
  }
  strcpy(knobs, SyncKnobs);
  knobs[sz+1] = 0;
  for (char * p = knobs; *p; p++) {
    if (*p == ':') *p = 0;
  }

  #define SETKNOB(x) { Knob_##x = kvGetInt(knobs, #x, Knob_##x); }
  SETKNOB(ReportSettings);
  SETKNOB(ExitRelease);
  SETKNOB(InlineNotify);
  SETKNOB(Verbose);
  SETKNOB(VerifyInUse);
  SETKNOB(VerifyMatch);
  SETKNOB(FixedSpin);
  SETKNOB(SpinLimit);
  SETKNOB(SpinBase);
  SETKNOB(SpinBackOff);
  SETKNOB(CASPenalty);
  SETKNOB(OXPenalty);
  SETKNOB(SpinSetSucc);
  SETKNOB(SuccEnabled);
  SETKNOB(SuccRestrict);
  SETKNOB(Penalty);
  SETKNOB(Bonus);
  SETKNOB(BonusB);
  SETKNOB(Poverty);
  SETKNOB(SpinAfterFutile);
  SETKNOB(UsePause);
  SETKNOB(SpinEarly);
  SETKNOB(OState);
  SETKNOB(MaxSpinners);
  SETKNOB(PreSpin);
  SETKNOB(ExitPolicy);
  SETKNOB(QMode);
  SETKNOB(ResetEvent);
  SETKNOB(MoveNotifyee);
  SETKNOB(FastHSSEC);
  #undef SETKNOB

  if (Knob_Verbose) {
    sanity_checks();
  }

  if (os::is_MP()) {
    BackOffMask = (1 << Knob_SpinBackOff) - 1;
    if (Knob_ReportSettings) {
      tty->print_cr("INFO: BackOffMask=0x%X", BackOffMask);
    }
    // CONSIDER: BackOffMask = ROUNDUP_NEXT_POWER2 (ncpus-1)
  } else {
    Knob_SpinLimit = 0;
    Knob_SpinBase  = 0;
    Knob_PreSpin   = 0;
    Knob_FixedSpin = -1;
  }

  os::free(knobs);
  OrderAccess::fence();
  InitDone = 1;
}

void ObjectMonitor::sanity_checks() {
  int error_cnt = 0;
  int warning_cnt = 0;
  bool verbose = Knob_Verbose != 0 NOT_PRODUCT(|| VerboseInternalVMTests);

  if (verbose) {
    tty->print_cr("INFO: sizeof(ObjectMonitor)=" SIZE_FORMAT,
                  sizeof(ObjectMonitor));
    tty->print_cr("INFO: sizeof(PaddedEnd<ObjectMonitor>)=" SIZE_FORMAT,
                  sizeof(PaddedEnd<ObjectMonitor>));
  }

  uint cache_line_size = VM_Version::L1_data_cache_line_size();
  if (verbose) {
    tty->print_cr("INFO: L1_data_cache_line_size=%u", cache_line_size);
  }

  ObjectMonitor dummy;
  u_char *addr_begin  = (u_char*)&dummy;
  u_char *addr_header = (u_char*)&dummy._header;
  u_char *addr_owner  = (u_char*)&dummy._owner;

  uint offset_header = (uint)(addr_header - addr_begin);
  if (verbose) tty->print_cr("INFO: offset(_header)=%u", offset_header);

  uint offset_owner = (uint)(addr_owner - addr_begin);
  if (verbose) tty->print_cr("INFO: offset(_owner)=%u", offset_owner);

  if ((uint)(addr_header - addr_begin) != 0) {
    tty->print_cr("ERROR: offset(_header) must be zero (0).");
    error_cnt++;
  }

  if (cache_line_size != 0) {
    // We were able to determine the L1 data cache line size so
    // do some cache line specific sanity checks

    if ((offset_owner - offset_header) < cache_line_size) {
      tty->print_cr("WARNING: the _header and _owner fields are closer "
                    "than a cache line which permits false sharing.");
      warning_cnt++;
    }

    if ((sizeof(PaddedEnd<ObjectMonitor>) % cache_line_size) != 0) {
      tty->print_cr("WARNING: PaddedEnd<ObjectMonitor> size is not a "
                    "multiple of a cache line which permits false sharing.");
      warning_cnt++;
    }
  }

  ObjectSynchronizer::sanity_checks(verbose, cache_line_size, &error_cnt,
                                    &warning_cnt);

  if (verbose || error_cnt != 0 || warning_cnt != 0) {
    tty->print_cr("INFO: error_cnt=%d", error_cnt);
    tty->print_cr("INFO: warning_cnt=%d", warning_cnt);
  }

  guarantee(error_cnt == 0,
            "Fatal error(s) found in ObjectMonitor::sanity_checks()");
}

#ifndef PRODUCT
void ObjectMonitor_test() {
  ObjectMonitor::sanity_checks();
}
#endif
