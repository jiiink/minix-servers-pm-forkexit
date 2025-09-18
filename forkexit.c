/* This file deals with creating processes (via FORK) and deleting them (via
 * EXIT/WAIT4).  When a process forks, a new slot in the 'mproc' table is
 * allocated for it, and a copy of the parent's core image is made for the
 * child.  Then the kernel and file system are informed.  A process is removed
 * from the 'mproc' table when two events have occurred: (1) it has exited or
 * been killed by a signal, and (2) the parent has done a WAIT4.  If the
 * process exits first, it continues to occupy a slot until the parent does a
 * WAIT4.
 *
 * The entry points into this file are:
 *   do_fork:		perform the FORK system call
 *   do_srv_fork:	special FORK, used by RS to create sys services
 *   do_exit:		perform the EXIT system call (by calling exit_proc())
 *   exit_proc:		actually do the exiting, and tell VFS about it
 *   exit_restart:	continue exiting a process after VFS has replied
 *   do_wait4:		perform the WAIT4 system call
 *   wait_test:		check whether a parent is waiting for a child
 */

#include "pm.h"
#include <sys/wait.h>
#include <assert.h>
#include <minix/callnr.h>
#include <minix/com.h>
#include <minix/sched.h>
#include <minix/vm.h>
#include <sys/ptrace.h>
#include <sys/resource.h>
#include <signal.h>
#include "mproc.h"

#define LAST_FEW            2	/* last few slots reserved for superuser */

static void zombify(struct mproc *rmp);
static void check_parent(struct mproc *child, int try_cleanup);
static int tell_parent(struct mproc *child, vir_bytes addr);
static void tell_tracer(struct mproc *child);
static void tracer_died(struct mproc *child);
static void cleanup(register struct mproc *rmp);

/*===========================================================================*
 *				do_fork					     *
 *===========================================================================*/
#define FORK_TABLE_FULL_WARNING "PM: warning, process table is full!\n"
#define FORK_CHILD_SLOT_ERROR "do_fork can't find child slot"
#define FORK_WRONG_SLOT_ERROR "do_fork finds wrong child slot: %d"

static int check_fork_capacity(struct mproc *parent)
{
    if (procs_in_use == NR_PROCS)
        return 1;
    if (procs_in_use >= NR_PROCS - LAST_FEW && parent->mp_effuid != 0)
        return 1;
    return 0;
}

static int find_free_slot(unsigned int *next_child)
{
    int n = 0;
    do {
        *next_child = (*next_child + 1) % NR_PROCS;
        n++;
    } while ((mproc[*next_child].mp_flags & IN_USE) && n <= NR_PROCS);
    
    if (n > NR_PROCS)
        panic(FORK_CHILD_SLOT_ERROR);
    if (*next_child >= NR_PROCS || (mproc[*next_child].mp_flags & IN_USE))
        panic(FORK_WRONG_SLOT_ERROR, *next_child);
    
    return *next_child;
}

static void copy_parent_to_child(struct mproc *child, struct mproc *parent, int slot_index)
{
    *child = *parent;
    child->mp_sigact = mpsigact[slot_index];
    memcpy(child->mp_sigact, parent->mp_sigact, sizeof(mpsigact[slot_index]));
    child->mp_parent = who_p;
}

static void reset_tracer_if_needed(struct mproc *child)
{
    if (!(child->mp_trace_flags & TO_TRACEFORK)) {
        child->mp_tracer = NO_TRACER;
        child->mp_trace_flags = 0;
        (void) sigemptyset(&child->mp_sigtrace);
    }
}

static void set_scheduler_for_priv_proc(struct mproc *child)
{
    if (child->mp_flags & PRIV_PROC) {
        assert(child->mp_scheduler == NONE);
        child->mp_scheduler = SCHED_PROC_NR;
    }
}

static void reset_child_fields(struct mproc *child, endpoint_t child_ep)
{
    int i;
    
    child->mp_flags &= (IN_USE | DELAY_CALL | TAINTED);
    child->mp_child_utime = 0;
    child->mp_child_stime = 0;
    child->mp_exitstatus = 0;
    child->mp_sigstatus = 0;
    child->mp_endpoint = child_ep;
    
    for (i = 0; i < NR_ITIMERS; i++)
        child->mp_interval[i] = 0;
    
    child->mp_started = getticks();
    assert(child->mp_eventsub == NO_EVENTSUB);
}

static void notify_vfs_fork(struct mproc *child, struct mproc *parent)
{
    message m;
    
    memset(&m, 0, sizeof(m));
    m.m_type = VFS_PM_FORK;
    m.VFS_PM_ENDPT = child->mp_endpoint;
    m.VFS_PM_PENDPT = parent->mp_endpoint;
    m.VFS_PM_CPID = child->mp_pid;
    m.VFS_PM_REUID = -1;
    m.VFS_PM_REGID = -1;
    
    tell_vfs(child, &m);
}

int do_fork(void)
{
    register struct mproc *rmp;
    register struct mproc *rmc;
    pid_t new_pid;
    static unsigned int next_child = 0;
    endpoint_t child_ep;
    int s;
    
    rmp = mp;
    
    if (check_fork_capacity(rmp)) {
        printf(FORK_TABLE_FULL_WARNING);
        return EAGAIN;
    }
    
    find_free_slot(&next_child);
    
    if ((s = vm_fork(rmp->mp_endpoint, next_child, &child_ep)) != OK) {
        return s;
    }
    
    rmc = &mproc[next_child];
    procs_in_use++;
    
    copy_parent_to_child(rmc, rmp, next_child);
    reset_tracer_if_needed(rmc);
    set_scheduler_for_priv_proc(rmc);
    reset_child_fields(rmc, child_ep);
    
    new_pid = get_free_pid();
    rmc->mp_pid = new_pid;
    
    notify_vfs_fork(rmc, rmp);
    
    if (rmc->mp_tracer != NO_TRACER)
        sig_proc(rmc, SIGSTOP, TRUE, FALSE);
    
    return SUSPEND;
}

/*===========================================================================*
 *				do_srv_fork				     *
 *===========================================================================*/
#define RS_ALLOWED_ENDPOINT RS_PROC_NR
#define PROCESS_TABLE_FULL_THRESHOLD (NR_PROCS - LAST_FEW)

static int check_permission(void)
{
    if (mp->mp_endpoint != RS_ALLOWED_ENDPOINT)
        return EPERM;
    return OK;
}

static int check_process_table_capacity(struct mproc *rmp)
{
    if (procs_in_use == NR_PROCS)
        return EAGAIN;
    
    if (procs_in_use >= PROCESS_TABLE_FULL_THRESHOLD && rmp->mp_effuid != 0) {
        printf("PM: warning, process table is full!\n");
        return EAGAIN;
    }
    
    return OK;
}

static int find_free_slot(unsigned int *next_child)
{
    int n = 0;
    
    do {
        *next_child = (*next_child + 1) % NR_PROCS;
        n++;
    } while ((mproc[*next_child].mp_flags & IN_USE) && n <= NR_PROCS);
    
    if (n > NR_PROCS)
        panic("do_fork can't find child slot");
    
    if (*next_child >= NR_PROCS || (mproc[*next_child].mp_flags & IN_USE))
        panic("do_fork finds wrong child slot: %d", *next_child);
    
    return OK;
}

static void initialize_child_process(struct mproc *rmc, struct mproc *rmp, endpoint_t child_ep)
{
    *rmc = *rmp;
    rmc->mp_parent = who_p;
    rmc->mp_endpoint = child_ep;
    
    rmc->mp_child_utime = 0;
    rmc->mp_child_stime = 0;
    rmc->mp_exitstatus = 0;
    rmc->mp_sigstatus = 0;
    rmc->mp_started = getticks();
    
    rmc->mp_flags &= (IN_USE | PRIV_PROC | DELAY_CALL);
}

static void setup_child_signals(struct mproc *rmc, struct mproc *rmp, unsigned int next_child)
{
    rmc->mp_sigact = mpsigact[next_child];
    memcpy(rmc->mp_sigact, rmp->mp_sigact, sizeof(mpsigact[next_child]));
    
    if (!(rmc->mp_trace_flags & TO_TRACEFORK)) {
        rmc->mp_tracer = NO_TRACER;
        rmc->mp_trace_flags = 0;
        (void) sigemptyset(&rmc->mp_sigtrace);
    }
}

static void set_child_credentials(struct mproc *rmc)
{
    rmc->mp_realuid = m_in.m_lsys_pm_srv_fork.uid;
    rmc->mp_effuid = m_in.m_lsys_pm_srv_fork.uid;
    rmc->mp_svuid = m_in.m_lsys_pm_srv_fork.uid;
    rmc->mp_realgid = m_in.m_lsys_pm_srv_fork.gid;
    rmc->mp_effgid = m_in.m_lsys_pm_srv_fork.gid;
    rmc->mp_svgid = m_in.m_lsys_pm_srv_fork.gid;
}

static void reset_child_timers(struct mproc *rmc)
{
    int i;
    for (i = 0; i < NR_ITIMERS; i++)
        rmc->mp_interval[i] = 0;
}

static void notify_vfs_about_fork(struct mproc *rmc, struct mproc *rmp)
{
    message m;
    
    memset(&m, 0, sizeof(m));
    m.m_type = VFS_PM_SRV_FORK;
    m.VFS_PM_ENDPT = rmc->mp_endpoint;
    m.VFS_PM_PENDPT = rmp->mp_endpoint;
    m.VFS_PM_CPID = rmc->mp_pid;
    m.VFS_PM_REUID = m_in.m_lsys_pm_srv_fork.uid;
    m.VFS_PM_REGID = m_in.m_lsys_pm_srv_fork.gid;
    
    tell_vfs(rmc, &m);
}

int do_srv_fork(void)
{
    register struct mproc *rmp;
    register struct mproc *rmc;
    int s;
    pid_t new_pid;
    static unsigned int next_child = 0;
    endpoint_t child_ep;
    
    if ((s = check_permission()) != OK)
        return s;
    
    rmp = mp;
    
    if ((s = check_process_table_capacity(rmp)) != OK)
        return s;
    
    if (find_free_slot(&next_child) != OK)
        return EAGAIN;
    
    if ((s = vm_fork(rmp->mp_endpoint, next_child, &child_ep)) != OK)
        return s;
    
    rmc = &mproc[next_child];
    procs_in_use++;
    
    initialize_child_process(rmc, rmp, child_ep);
    setup_child_signals(rmc, rmp, next_child);
    set_child_credentials(rmc);
    reset_child_timers(rmc);
    
    assert(rmc->mp_eventsub == NO_EVENTSUB);
    
    new_pid = get_free_pid();
    rmc->mp_pid = new_pid;
    
    notify_vfs_about_fork(rmc, rmp);
    
    if (rmc->mp_tracer != NO_TRACER)
        sig_proc(rmc, SIGSTOP, TRUE, FALSE);
    
    reply(rmc - mproc, OK);
    
    return rmc->mp_pid;
}

/*===========================================================================*
 *				do_exit					     *
 *===========================================================================*/
int
do_exit(void)
{
    if (is_privileged_process()) {
        handle_privileged_process_exit();
    } else {
        perform_normal_exit();
    }
    return SUSPEND;
}

static int is_privileged_process(void)
{
    return mp->mp_flags & PRIV_PROC;
}

static void handle_privileged_process_exit(void)
{
    printf("PM: system process %d (%s) tries to exit(), sending SIGKILL\n",
        mp->mp_endpoint, mp->mp_name);
    sys_kill(mp->mp_endpoint, SIGKILL);
}

static void perform_normal_exit(void)
{
    exit_proc(mp, m_in.m_lc_pm_exit.status, FALSE);
}

/*===========================================================================*
 *				exit_proc				     *
 *===========================================================================*/
void exit_proc(register struct mproc *rmp, int exit_status, int dump_core)
{
  register int proc_nr, proc_nr_e;
  int r;
  pid_t procgrp;
  clock_t user_time, sys_time;
  message m;

  dump_core = should_dump_core(rmp, dump_core);
  
  proc_nr = (int) (rmp - mproc);
  proc_nr_e = rmp->mp_endpoint;
  procgrp = (rmp->mp_pid == mp->mp_procgrp) ? mp->mp_procgrp : 0;

  cleanup_timer(rmp);
  update_accounting(rmp, proc_nr_e);
  stop_process_if_needed(rmp, proc_nr_e);
  notify_vm_exit(proc_nr_e);
  
  if (handle_special_processes(proc_nr_e, exit_status))
    return;
  
  notify_vfs_about_exit(rmp, dump_core);
  
  if (rmp->mp_flags & PRIV_PROC)
    clear_system_process(rmp->mp_endpoint);
  
  finalize_process_state(rmp, exit_status);
  
  if (!dump_core)
    zombify(rmp);
  
  disinherit_children(proc_nr);
  
  if (procgrp != 0) 
    check_sig(-procgrp, SIGHUP, FALSE);
}

static int should_dump_core(struct mproc *rmp, int dump_core)
{
  if (dump_core && rmp->mp_realuid != rmp->mp_effuid)
    return FALSE;
  
  if (dump_core && (rmp->mp_flags & PRIV_PROC))
    return FALSE;
  
  return dump_core;
}

static void cleanup_timer(struct mproc *rmp)
{
  if (rmp->mp_flags & ALARM_ON) 
    set_alarm(rmp, (clock_t) 0);
}

static void update_accounting(struct mproc *rmp, int proc_nr_e)
{
  clock_t user_time, sys_time;
  int r;
  
  if ((r = sys_times(proc_nr_e, &user_time, &sys_time, NULL, NULL)) != OK)
    panic("exit_proc: sys_times failed: %d", r);
  
  rmp->mp_child_utime += user_time;
  rmp->mp_child_stime += sys_time;
}

static void stop_process_if_needed(struct mproc *rmp, int proc_nr_e)
{
  int r;
  
  if (!(rmp->mp_flags & PROC_STOPPED)) {
    if ((r = sys_stop(proc_nr_e)) != OK)
      panic("sys_stop failed: %d", r);
    rmp->mp_flags |= PROC_STOPPED;
  }
}

static void notify_vm_exit(int proc_nr_e)
{
  int r;
  
  if ((r = vm_willexit(proc_nr_e)) != OK)
    panic("exit_proc: vm_willexit failed: %d", r);
}

static int handle_special_processes(int proc_nr_e, int exit_status)
{
  if (proc_nr_e == INIT_PROC_NR) {
    printf("PM: INIT died with exit status %d; showing stacktrace\n", exit_status);
    sys_diagctl_stacktrace(proc_nr_e);
    return 1;
  }
  
  if (proc_nr_e == VFS_PROC_NR)
    panic("exit_proc: VFS died");
  
  return 0;
}

static void notify_vfs_about_exit(struct mproc *rmp, int dump_core)
{
  message m;
  
  memset(&m, 0, sizeof(m));
  m.m_type = dump_core ? VFS_PM_DUMPCORE : VFS_PM_EXIT;
  m.VFS_PM_ENDPT = rmp->mp_endpoint;
  
  if (dump_core) {
    m.VFS_PM_TERM_SIG = rmp->mp_sigstatus;
    m.VFS_PM_PATH = rmp->mp_name;
  }
  
  tell_vfs(rmp, &m);
}

static void clear_system_process(int endpoint)
{
  int r;
  
  if ((r = sys_clear(endpoint)) != OK)
    panic("exit_proc: sys_clear failed: %d", r);
}

static void finalize_process_state(struct mproc *rmp, int exit_status)
{
  rmp->mp_flags &= (IN_USE|VFS_CALL|PRIV_PROC|TRACE_EXIT|PROC_STOPPED);
  rmp->mp_flags |= EXITING;
  rmp->mp_exitstatus = (char) exit_status;
}

static void disinherit_children(int proc_nr)
{
  struct mproc *rmp;
  
  for (rmp = &mproc[0]; rmp < &mproc[NR_PROCS]; rmp++) {
    if (!(rmp->mp_flags & IN_USE)) 
      continue;
    
    if (rmp->mp_tracer == proc_nr)
      tracer_died(rmp);
    
    if (rmp->mp_parent == proc_nr) {
      rmp->mp_parent = INIT_PROC_NR;
      
      if (rmp->mp_flags & VFS_CALL)
        rmp->mp_flags |= NEW_PARENT;
      
      if (rmp->mp_flags & ZOMBIE)
        check_parent(rmp, TRUE);
    }
  }
}

/*===========================================================================*
 *				exit_restart				     *
 *===========================================================================*/
void exit_restart(struct mproc *rmp)
{
  int r;

  stop_scheduler(rmp);
  rmp->mp_scheduler = NONE;

  attempt_zombify(rmp);
  clear_user_process(rmp);
  release_process_memory(rmp);
  notify_tracer_if_needed(rmp);
  cleanup_if_parent_notified(rmp);
}

static void stop_scheduler(struct mproc *rmp)
{
  int r;
  
  if((r = sched_stop(rmp->mp_scheduler, rmp->mp_endpoint)) != OK) {
    printf("PM: The scheduler did not want to give up "
           "scheduling %s, ret=%d.\n", rmp->mp_name, r);
  }
}

static void attempt_zombify(struct mproc *rmp)
{
  if (!(rmp->mp_flags & (TRACE_ZOMBIE | ZOMBIE | TOLD_PARENT))) {
    zombify(rmp);
  }
}

static void clear_user_process(struct mproc *rmp)
{
  int r;
  
  if (!(rmp->mp_flags & PRIV_PROC)) {
    if((r = sys_clear(rmp->mp_endpoint)) != OK) {
      panic("exit_restart: sys_clear failed: %d", r);
    }
  }
}

static void release_process_memory(struct mproc *rmp)
{
  int r;
  
  if((r = vm_exit(rmp->mp_endpoint)) != OK) {
    panic("exit_restart: vm_exit failed: %d", r);
  }
}

static void notify_tracer_if_needed(struct mproc *rmp)
{
  if (rmp->mp_flags & TRACE_EXIT) {
    mproc[rmp->mp_tracer].mp_reply.m_pm_lc_ptrace.data = 0;
    reply(rmp->mp_tracer, OK);
  }
}

static void cleanup_if_parent_notified(struct mproc *rmp)
{
  if (rmp->mp_flags & TOLD_PARENT) {
    cleanup(rmp);
  }
}

/*===========================================================================*
 *				do_wait4				     *
 *===========================================================================*/
#define CHILD_IS_IN_USE(rp) ((rp->mp_flags & (IN_USE | TOLD_PARENT)) == IN_USE)
#define CHILD_BELONGS_TO_CALLER(rp) (rp->mp_parent == who_p || rp->mp_tracer == who_p)
#define CHILD_IS_ZOMBIE(rp) (rp->mp_flags & ZOMBIE)
#define CHILD_IS_TRACED_BY_CALLER(rp) (rp->mp_tracer == who_p)
#define CHILD_IS_PARENTED_BY_CALLER(rp) (rp->mp_parent == who_p)
#define TRACED_CHILD_IS_ZOMBIE(rp) (rp->mp_flags & TRACE_ZOMBIE)
#define TRACED_CHILD_IS_STOPPED(rp) (rp->mp_flags & TRACE_STOPPED)
#define PARENT_WANTS_TO_WAIT(options) (!(options & WNOHANG))
#define CHILD_HAS_NO_PENDING_CALLS(rp) (!(rp->mp_flags & (VFS_CALL | EVENT_CALL)))

static int matches_pid_criteria(int pidarg, struct mproc *rp)
{
    if (pidarg > 0 && pidarg != rp->mp_pid) return 0;
    if (pidarg < -1 && -pidarg != rp->mp_procgrp) return 0;
    return 1;
}

static int is_valid_child(struct mproc *rp, int who_p)
{
    if (!CHILD_IS_IN_USE(rp)) return 0;
    if (!CHILD_BELONGS_TO_CALLER(rp)) return 0;
    if (CHILD_IS_PARENTED_BY_CALLER(rp)) return 1;
    if (!CHILD_IS_ZOMBIE(rp)) return 1;
    return 0;
}

static int handle_traced_zombie(struct mproc *rp)
{
    tell_tracer(rp);
    check_parent(rp, TRUE);
    return SUSPEND;
}

static int deliver_trace_signal(struct mproc *rp)
{
    int i;
    for (i = 1; i < _NSIG; i++) {
        if (sigismember(&rp->mp_sigtrace, i)) {
            sigdelset(&rp->mp_sigtrace, i);
            mp->mp_reply.m_pm_lc_wait4.status = W_STOPCODE(i);
            return rp->mp_pid;
        }
    }
    return 0;
}

static int handle_traced_child(struct mproc *rp)
{
    if (TRACED_CHILD_IS_ZOMBIE(rp)) {
        return handle_traced_zombie(rp);
    }
    if (TRACED_CHILD_IS_STOPPED(rp)) {
        int result = deliver_trace_signal(rp);
        if (result != 0) return result;
    }
    return 0;
}

static int handle_zombie_child(struct mproc *rp, vir_bytes addr)
{
    int waited_for = tell_parent(rp, addr);
    if (waited_for && CHILD_HAS_NO_PENDING_CALLS(rp)) {
        cleanup(rp);
    }
    return SUSPEND;
}

static int process_child(struct mproc *rp, int who_p, vir_bytes addr)
{
    if (CHILD_IS_TRACED_BY_CALLER(rp)) {
        int result = handle_traced_child(rp);
        if (result != 0) return result;
    }
    
    if (CHILD_IS_PARENTED_BY_CALLER(rp) && CHILD_IS_ZOMBIE(rp)) {
        return handle_zombie_child(rp, addr);
    }
    
    return 0;
}

static int count_and_process_children(int pidarg, vir_bytes addr, int *children)
{
    struct mproc *rp;
    int result;
    
    *children = 0;
    
    for (rp = &mproc[0]; rp < &mproc[NR_PROCS]; rp++) {
        if (!is_valid_child(rp, who_p)) continue;
        if (!matches_pid_criteria(pidarg, rp)) continue;
        
        (*children)++;
        
        result = process_child(rp, who_p, addr);
        if (result != 0) return result;
    }
    
    return 0;
}

static int handle_no_exited_child(int children, int options, int pidarg, vir_bytes addr)
{
    if (children == 0) {
        return ECHILD;
    }
    
    if (!PARENT_WANTS_TO_WAIT(options)) {
        return 0;
    }
    
    mp->mp_flags |= WAITING;
    mp->mp_wpid = (pid_t) pidarg;
    mp->mp_waddr = addr;
    return SUSPEND;
}

int do_wait4(void)
{
    int pidarg, options, children, result;
    vir_bytes addr;
    
    pidarg = m_in.m_lc_pm_wait4.pid;
    options = m_in.m_lc_pm_wait4.options;
    addr = m_in.m_lc_pm_wait4.addr;
    
    if (pidarg == 0) pidarg = -mp->mp_procgrp;
    
    result = count_and_process_children(pidarg, addr, &children);
    if (result != 0) return result;
    
    return handle_no_exited_child(children, options, pidarg, addr);
}

/*===========================================================================*
 *				wait_test				     *
 *===========================================================================*/
int wait_test(struct mproc *rmp, struct mproc *child)
{
    int parent_waiting = rmp->mp_flags & WAITING;
    if (!parent_waiting) {
        return 0;
    }

    pid_t pidarg = rmp->mp_wpid;
    
    if (pidarg == -1) {
        return 1;
    }
    
    if (pidarg == child->mp_pid) {
        return 1;
    }
    
    if (-pidarg == child->mp_procgrp) {
        return 1;
    }
    
    return 0;
}

/*===========================================================================*
 *				zombify					     *
 *===========================================================================*/
static void set_zombie_flag(struct mproc *rmp, int is_trace_zombie)
{
    if (is_trace_zombie) {
        rmp->mp_flags |= TRACE_ZOMBIE;
    } else {
        rmp->mp_flags |= ZOMBIE;
    }
}

static int is_already_zombie(struct mproc *rmp)
{
    return rmp->mp_flags & (TRACE_ZOMBIE | ZOMBIE);
}

static int has_separate_tracer(struct mproc *rmp)
{
    return rmp->mp_tracer != NO_TRACER && rmp->mp_tracer != rmp->mp_parent;
}

static void notify_tracer(struct mproc *rmp)
{
    struct mproc *t_mp = &mproc[rmp->mp_tracer];
    
    if (!wait_test(t_mp, rmp))
        return;
    
    tell_tracer(rmp);
}

static void zombify(struct mproc *rmp)
{
    if (is_already_zombie(rmp))
        panic("zombify: process was already a zombie");
    
    if (has_separate_tracer(rmp)) {
        set_zombie_flag(rmp, 1);
        notify_tracer(rmp);
    } else {
        set_zombie_flag(rmp, 0);
    }
    
    check_parent(rmp, 0);
}

/*===========================================================================*
 *				check_parent				     *
 *===========================================================================*/
static void handle_exiting_parent(void) {
    return;
}

static int should_cleanup_child(struct mproc *child) {
    return !(child->mp_flags & (VFS_CALL | EVENT_CALL));
}

static void notify_waiting_parent(struct mproc *child, struct mproc *parent, int try_cleanup) {
    if (!tell_parent(child, parent->mp_waddr)) {
        return;
    }
    
    if (try_cleanup && should_cleanup_child(child)) {
        cleanup(child);
    }
}

static void notify_non_waiting_parent(struct mproc *parent) {
    sig_proc(parent, SIGCHLD, TRUE, FALSE);
}

static void check_parent(struct mproc *child, int try_cleanup) {
    struct mproc *parent = &mproc[child->mp_parent];

    if (parent->mp_flags & EXITING) {
        handle_exiting_parent();
        return;
    }

    if (wait_test(parent, child)) {
        notify_waiting_parent(child, parent, try_cleanup);
    } else {
        notify_non_waiting_parent(parent);
    }
}

/*===========================================================================*
 *				tell_parent				     *
 *===========================================================================*/
static void validate_parent_child_state(struct mproc *child, int mp_parent)
{
    if (mp_parent <= 0)
        panic("tell_parent: bad value in mp_parent: %d", mp_parent);
    if (!(child->mp_flags & ZOMBIE))
        panic("tell_parent: child not a zombie");
    if (child->mp_flags & TOLD_PARENT)
        panic("tell_parent: telling parent again");
}

static int report_resource_usage(struct mproc *parent, struct mproc *child, vir_bytes addr)
{
    struct rusage r_usage;
    int r;

    memset(&r_usage, 0, sizeof(r_usage));
    set_rusage_times(&r_usage, child->mp_child_utime, child->mp_child_stime);

    r = sys_datacopy(SELF, (vir_bytes)&r_usage, parent->mp_endpoint, 
                     addr, sizeof(r_usage));
    if (r != OK) {
        reply(child->mp_parent, r);
        return FALSE;
    }
    return TRUE;
}

static void notify_parent_and_cleanup(struct mproc *parent, struct mproc *child)
{
    parent->mp_reply.m_pm_lc_wait4.status = 
        W_EXITCODE(child->mp_exitstatus, child->mp_sigstatus);
    reply(child->mp_parent, child->mp_pid);
    parent->mp_flags &= ~WAITING;
    child->mp_flags &= ~ZOMBIE;
    child->mp_flags |= TOLD_PARENT;
}

static void accumulate_child_times(struct mproc *parent, struct mproc *child)
{
    parent->mp_child_utime += child->mp_child_utime;
    parent->mp_child_stime += child->mp_child_stime;
}

static int tell_parent(struct mproc *child, vir_bytes addr)
{
    int mp_parent = child->mp_parent;
    struct mproc *parent;

    validate_parent_child_state(child, mp_parent);
    parent = &mproc[mp_parent];

    if (addr && !report_resource_usage(parent, child, addr)) {
        return FALSE;
    }

    notify_parent_and_cleanup(parent, child);
    accumulate_child_times(parent, child);

    return TRUE;
}

/*===========================================================================*
 *				tell_tracer				     *
 *===========================================================================*/
static void validate_tracer(struct mproc *child, int mp_tracer) {
    if (mp_tracer <= 0)
        panic("tell_tracer: bad value in mp_tracer: %d", mp_tracer);
    if (!(child->mp_flags & TRACE_ZOMBIE))
        panic("tell_tracer: child not a zombie");
}

static int calculate_exit_status(struct mproc *child) {
    const int SIGNAL_MASK = 0377;
    return W_EXITCODE(child->mp_exitstatus, (child->mp_sigstatus & SIGNAL_MASK));
}

static void update_tracer_state(struct mproc *tracer, int status) {
    tracer->mp_reply.m_pm_lc_wait4.status = status;
    tracer->mp_flags &= ~WAITING;
}

static void update_child_state(struct mproc *child) {
    child->mp_flags &= ~TRACE_ZOMBIE;
    child->mp_flags |= ZOMBIE;
}

static void tell_tracer(struct mproc *child) {
    int mp_tracer = child->mp_tracer;
    validate_tracer(child, mp_tracer);
    
    struct mproc *tracer = &mproc[mp_tracer];
    int status = calculate_exit_status(child);
    
    update_tracer_state(tracer, status);
    reply(child->mp_tracer, child->mp_pid);
    update_child_state(child);
}

/*===========================================================================*
 *				tracer_died				     *
 *===========================================================================*/
static void clear_tracer(struct mproc *child) {
    child->mp_tracer = NO_TRACER;
    child->mp_flags &= ~TRACE_EXIT;
}

static void kill_running_child(struct mproc *child) {
    sig_proc(child, SIGKILL, TRUE, FALSE);
}

static void notify_real_parent(struct mproc *child) {
    child->mp_flags &= ~TRACE_ZOMBIE;
    child->mp_flags |= ZOMBIE;
    check_parent(child, TRUE);
}

static void tracer_died(struct mproc *child) {
    clear_tracer(child);

    if (!(child->mp_flags & EXITING)) {
        kill_running_child(child);
        return;
    }

    if (child->mp_flags & TRACE_ZOMBIE) {
        notify_real_parent(child);
    }
}

/*===========================================================================*
 *				cleanup					     *
 *===========================================================================*/
static void
cleanup(register struct mproc *rmp)
{
  rmp->mp_pid = 0;
  rmp->mp_flags = 0;
  rmp->mp_child_utime = 0;
  rmp->mp_child_stime = 0;
  procs_in_use--;
}

