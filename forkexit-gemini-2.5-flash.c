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
int
do_fork(void)
{
  const struct mproc *rmp;  /* pointer to parent */
  struct mproc *rmc;        /* pointer to child */
  pid_t new_pid;
  static unsigned int next_child = 0; /* Index for round-robin slot search */
  int i;
  endpoint_t child_ep;
  message m;
  int s;

  rmp = mp; /* `mp` is assumed to be a global or external pointer to the parent's mproc */

  /* If process tables might fill up during FORK, don't even start since
   * recovery half way through is such a nuisance. Root processes might
   * be allowed to fork even when others cannot.
   */
  if ((procs_in_use == NR_PROCS) ||
  		(procs_in_use >= NR_PROCS - LAST_FEW && rmp->mp_effuid != 0))
  {
  	printf("PM: warning, process table is full, cannot fork!\n");
  	return(EAGAIN);
  }

  /* Find a slot in 'mproc' for the child process.
   * Start search from (next_child + 1) % NR_PROCS, wrapping around.
   */
  int found_slot_idx = -1;
  for (i = 0; i < NR_PROCS; ++i) {
      unsigned int candidate_slot = (next_child + 1 + i) % NR_PROCS;
      if (!(mproc[candidate_slot].mp_flags & IN_USE)) {
          found_slot_idx = candidate_slot;
          break; /* Found a free slot */
      }
  }

  if (found_slot_idx == -1) {
      /* This should ideally not happen if the initial `procs_in_use` check is robust,
       * but serves as a safeguard against logic errors or race conditions.
       */
      panic("do_fork: no free mproc slot found for child after checking all slots");
  }

  next_child = found_slot_idx; /* Update static next_child for subsequent calls */
  rmc = &mproc[next_child];

  /* Memory part of the forking. This call updates child_ep. */
  if ((s = vm_fork(rmp->mp_endpoint, next_child, &child_ep)) != OK) {
	return s;
  }

  /* PM may not fail fork after call to vm_fork(), as VM calls sys_fork().
   * Set up the child and its memory map; copy its 'mproc' slot from parent.
   */
  procs_in_use++;
  *rmc = *rmp;			/* Copy parent's process slot to child's */

  /* Restore mp_sigact ptr to point to the child's specific mpsigact array slot
   * and copy the signal action data from parent.
   */
  rmc->mp_sigact = mpsigact[next_child];
  memcpy(rmc->mp_sigact, rmp->mp_sigact, sizeof(mpsigact[next_child]));

  rmc->mp_parent = who_p;	/* Record child's parent endpoint */

  /* If the child is not to inherit tracing, reset tracing flags. */
  if (!(rmc->mp_trace_flags & TO_TRACEFORK)) {
	rmc->mp_tracer = NO_TRACER;
	rmc->mp_trace_flags = 0;
	(void) sigemptyset(&rmc->mp_sigtrace);
  }

  /* Some system servers (PRIV_PROC) need their scheduler assigned by PM. */
  if (rmc->mp_flags & PRIV_PROC) {
	assert(rmc->mp_scheduler == NONE); /* Ensure scheduler is not already set */
	rmc->mp_scheduler = SCHED_PROC_NR;
  }

  /* Inherit only these specific flags. Others are cleared implicitly by the copy. */
  rmc->mp_flags &= (IN_USE | DELAY_CALL | TAINTED);

  /* Reset child-specific administrative fields. */
  rmc->mp_child_utime = 0;
  rmc->mp_child_stime = 0;
  rmc->mp_exitstatus = 0;
  rmc->mp_sigstatus = 0;
  rmc->mp_endpoint = child_ep;		/* Set endpoint passed back by VM */

  /* Reset timer intervals for the child. */
  for (i = 0; i < NR_ITIMERS; i++) {
	rmc->mp_interval[i] = 0;
  }
  rmc->mp_started = getticks();		/* Remember start time, for ps(1) */

  assert(rmc->mp_eventsub == NO_EVENTSUB); /* Ensure event subscription is clean */

  /* Find a free pid for the child and assign it. */
  new_pid = get_free_pid();
  rmc->mp_pid = new_pid;

  /* Notify VFS about the new child process. */
  memset(&m, 0, sizeof(m));
  m.m_type = VFS_PM_FORK;
  m.VFS_PM_ENDPT = rmc->mp_endpoint;
  m.VFS_PM_PENDPT = rmp->mp_endpoint;
  m.VFS_PM_CPID = rmc->mp_pid;
  m.VFS_PM_REUID = -1;	/* Not used by VFS_PM_FORK */
  m.VFS_PM_REGID = -1;	/* Not used by VFS_PM_FORK */

  tell_vfs(rmc, &m);

  /* Tell the tracer, if any, about the new child. */
  if (rmc->mp_tracer != NO_TRACER) {
	sig_proc(rmc, SIGSTOP, TRUE /*trace*/, FALSE /* ksig */);
  }

  /* Do not reply until VFS is ready to process the fork request.
   * The process remains suspended awaiting VFS reply.
   */
  return SUSPEND;
}

/*===========================================================================*
 *				do_srv_fork				     *
 *===========================================================================*/
int
do_srv_fork(void)
{
  struct mproc *rmc;
  int s;
  pid_t new_pid;
  static unsigned int next_child = 0;
  unsigned int i;
  endpoint_t child_ep;
  message m;

  if (mp->mp_endpoint != RS_PROC_NR) {
	return EPERM;
  }

  if ((procs_in_use == NR_PROCS) ||
  		(procs_in_use >= NR_PROCS - LAST_FEW && mp->mp_effuid != 0))
  {
  	printf("PM: warning, process table is full!\n");
  	return EAGAIN;
  }

  int found_slot_idx = -1;
  unsigned int search_start_idx = next_child;
  for (i = 0; i < NR_PROCS; ++i) {
      unsigned int current_check_idx = (search_start_idx + 1 + i) % NR_PROCS;
      if (!(mproc[current_check_idx].mp_flags & IN_USE)) {
          found_slot_idx = current_check_idx;
          break;
      }
  }

  if (found_slot_idx == -1) {
      panic("do_srv_fork: no free child slot found (internal error)");
  }
  rmc = &mproc[found_slot_idx];
  next_child = found_slot_idx;

  if ((s = vm_fork(mp->mp_endpoint, next_child, &child_ep)) != OK) {
	return s;
  }

  procs_in_use++;

  *rmc = *mp;
  rmc->mp_sigact = mpsigact[next_child];
  memcpy(rmc->mp_sigact, mp->mp_sigact, sizeof(mpsigact[next_child]));
  rmc->mp_parent = who_p;
  if (!(rmc->mp_trace_flags & TO_TRACEFORK)) {
	rmc->mp_tracer = NO_TRACER;
	rmc->mp_trace_flags = 0;
	(void) sigemptyset(&rmc->mp_sigtrace);
  }
  rmc->mp_flags &= (IN_USE | PRIV_PROC | DELAY_CALL);
  rmc->mp_child_utime = 0;
  rmc->mp_child_stime = 0;
  rmc->mp_exitstatus = 0;
  rmc->mp_sigstatus = 0;
  rmc->mp_endpoint = child_ep;
  rmc->mp_realuid = m_in.m_lsys_pm_srv_fork.uid;
  rmc->mp_effuid = m_in.m_lsys_pm_srv_fork.uid;
  rmc->mp_svuid = m_in.m_lsys_pm_srv_fork.uid;
  rmc->mp_realgid = m_in.m_lsys_pm_srv_fork.gid;
  rmc->mp_effgid = m_in.m_lsys_pm_srv_fork.gid;
  rmc->mp_svgid = m_in.m_lsys_pm_srv_fork.gid;
  for (i = 0; i < NR_ITIMERS; i++) {
	rmc->mp_interval[i] = 0;
  }
  rmc->mp_started = getticks();

  assert(rmc->mp_eventsub == NO_EVENTSUB);

  new_pid = get_free_pid();
  rmc->mp_pid = new_pid;

  memset(&m, 0, sizeof(m));
  m.m_type = VFS_PM_SRV_FORK;
  m.VFS_PM_ENDPT = rmc->mp_endpoint;
  m.VFS_PM_PENDPT = mp->mp_endpoint;
  m.VFS_PM_CPID = rmc->mp_pid;
  m.VFS_PM_REUID = m_in.m_lsys_pm_srv_fork.uid;
  m.VFS_PM_REGID = m_in.m_lsys_pm_srv_fork.gid;

  s = tell_vfs(rmc, &m);
  if (s != OK) {
      procs_in_use--;
      rmc->mp_flags &= ~IN_USE;
      return s;
  }

  if (rmc->mp_tracer != NO_TRACER) {
	sig_proc(rmc, SIGSTOP, TRUE /*trace*/, FALSE /* ksig */);
  }

  reply(rmc - mproc, OK);

  return rmc->mp_pid;
}

/*===========================================================================*
 *				do_exit					     *
 *===========================================================================*/
int
do_exit(void)
{
  const int current_process_flags = mp->mp_flags;
  const int current_process_endpoint = mp->mp_endpoint;
  const char *current_process_name = mp->mp_name;
  const int exit_status_code = m_in.m_lc_pm_exit.status;

  if (current_process_flags & PRIV_PROC) {
      printf("PM: system process %d (%s) tries to exit(). "
             "Sending SIGKILL.\n",
             current_process_endpoint, current_process_name);
      sys_kill(current_process_endpoint, SIGKILL);
  }
  else {
      exit_proc(mp, exit_status_code, FALSE);
  }
  return SUSPEND;
}

/*===========================================================================*
 *				exit_proc				     *
 *===========================================================================*/
void
exit_proc(
	struct mproc *rmp_to_exit,
	int exit_status,
	int dump_core_requested
)
{
  int proc_nr, r;
  pid_t procgrp;
  clock_t user_time, sys_time;
  message m;
  int dump_core_final = dump_core_requested;

  if (dump_core_final && rmp_to_exit->mp_realuid != rmp_to_exit->mp_effuid) {
	dump_core_final = FALSE;
  }

  if (dump_core_final && (rmp_to_exit->mp_flags & PRIV_PROC)) {
	dump_core_final = FALSE;
  }

  proc_nr = (int) (rmp_to_exit - mproc);

  procgrp = (rmp_to_exit->mp_pid == mp->mp_procgrp) ? mp->mp_procgrp : 0;

  if (rmp_to_exit->mp_flags & ALARM_ON) {
    set_alarm(rmp_to_exit, (clock_t) 0);
  }

  if ((r = sys_times(rmp_to_exit->mp_endpoint, &user_time, &sys_time, NULL, NULL)) != OK) {
  	panic("exit_proc: sys_times failed: %d", r);
  }
  rmp_to_exit->mp_child_utime += user_time;
  rmp_to_exit->mp_child_stime += sys_time;

  if (!(rmp_to_exit->mp_flags & PROC_STOPPED)) {
	if ((r = sys_stop(rmp_to_exit->mp_endpoint)) != OK) {
		panic("sys_stop failed: %d", r);
	}
	rmp_to_exit->mp_flags |= PROC_STOPPED;
  }

  if ((r = vm_willexit(rmp_to_exit->mp_endpoint)) != OK) {
	panic("exit_proc: vm_willexit failed: %d", r);
  }

  if (rmp_to_exit->mp_endpoint == INIT_PROC_NR) {
	printf("PM: INIT died with exit status %d; showing stacktrace\n", exit_status);
	sys_diagctl_stacktrace(rmp_to_exit->mp_endpoint);
	return;
  }
  if (rmp_to_exit->mp_endpoint == VFS_PROC_NR) {
	panic("exit_proc: VFS died unexpectedly.");
  }

  memset(&m, 0, sizeof(m));
  m.m_type = dump_core_final ? VFS_PM_DUMPCORE : VFS_PM_EXIT;
  m.VFS_PM_ENDPT = rmp_to_exit->mp_endpoint;

  if (dump_core_final) {
	m.VFS_PM_TERM_SIG = rmp_to_exit->mp_sigstatus;
	m.VFS_PM_PATH = rmp_to_exit->mp_name;
  }

  tell_vfs(rmp_to_exit, &m);

  if (rmp_to_exit->mp_flags & PRIV_PROC) {
	if ((r = sys_clear(rmp_to_exit->mp_endpoint)) != OK) {
		panic("exit_proc: sys_clear failed: %d", r);
	}
  }

  rmp_to_exit->mp_flags &= (IN_USE | VFS_CALL | PRIV_PROC | TRACE_EXIT | PROC_STOPPED);
  rmp_to_exit->mp_flags |= EXITING;

  rmp_to_exit->mp_exitstatus = (char) exit_status;

  if (!dump_core_final) {
	zombify(rmp_to_exit);
  }

  struct mproc *child_rmp;
  for (child_rmp = &mproc[0]; child_rmp < &mproc[NR_PROCS]; child_rmp++) {
	if (!(child_rmp->mp_flags & IN_USE)) {
        continue;
    }
	if (child_rmp->mp_tracer == proc_nr) {
		tracer_died(child_rmp);
	}
	if (child_rmp->mp_parent == proc_nr) {
		child_rmp->mp_parent = INIT_PROC_NR;

		if (child_rmp->mp_flags & VFS_CALL) {
			child_rmp->mp_flags |= NEW_PARENT;
		}

		if (child_rmp->mp_flags & ZOMBIE) {
			check_parent(child_rmp, TRUE);
		}
	}
  }

  if (procgrp != 0) {
    check_sig(-procgrp, SIGHUP, FALSE);
  }
}

/*===========================================================================*
 *				exit_restart				     *
 *===========================================================================*/
void exit_restart(struct mproc *rmp)
{
  int ret_code;

  if ((ret_code = sched_stop(rmp->mp_scheduler, rmp->mp_endpoint)) != OK) {
	printf("PM: The scheduler did not want to give up "
		"scheduling %s, ret=%d.\n", rmp->mp_name, ret_code);
  }

  rmp->mp_scheduler = NONE;

  if (!(rmp->mp_flags & (TRACE_ZOMBIE | ZOMBIE | TOLD_PARENT))) {
	zombify(rmp);
  }

  if (!(rmp->mp_flags & PRIV_PROC)) {
	if ((ret_code = sys_clear(rmp->mp_endpoint)) != OK) {
		panic("exit_restart: sys_clear failed: %d", ret_code);
	}
  }

  if ((ret_code = vm_exit(rmp->mp_endpoint)) != OK) {
  	panic("exit_restart: vm_exit failed: %d", ret_code);
  }

  if (rmp->mp_flags & TRACE_EXIT) {
	mproc[rmp->mp_tracer].mp_reply.m_pm_lc_ptrace.data = 0;
	reply(rmp->mp_tracer, OK);
  }

  if (rmp->mp_flags & TOLD_PARENT) {
	cleanup(rmp);
  }
}

/*===========================================================================*
 *				do_wait4				     *
 *===========================================================================*/
int
do_wait4(void)
{
    struct mproc *rp;
    vir_bytes rusage_address;
    int i;
    int target_pid_filter;
    int wait_options;
    int found_qualifying_child_count = 0;

    target_pid_filter = m_in.m_lc_pm_wait4.pid;
    wait_options = m_in.m_lc_pm_wait4.options;
    rusage_address = m_in.m_lc_pm_wait4.addr;

    if (target_pid_filter == 0) {
        target_pid_filter = -mp->mp_procgrp;
    }

    for (rp = &mproc[0]; rp < &mproc[NR_PROCS]; rp++) {
        // Process must be IN_USE and not already TOLD_PARENT
        if (!((rp->mp_flags & (IN_USE | TOLD_PARENT)) == IN_USE)) {
            continue;
        }

        // Current process must be either the child's parent or its tracer
        const int is_parent_of_child = (rp->mp_parent == who_p);
        const int is_tracer_of_child = (rp->mp_tracer == who_p);

        if (!is_parent_of_child && !is_tracer_of_child) {
            continue;
        }

        // If 'who_p' is *only* the tracer and the child is a regular ZOMBIE (not TRACE_ZOMBIE),
        // it does not qualify for 'who_p's wait4 call here.
        if (is_tracer_of_child && !is_parent_of_child && (rp->mp_flags & ZOMBIE)) {
            continue;
        }

        // Apply pidarg filter
        if (target_pid_filter > 0 && target_pid_filter != rp->mp_pid) {
            continue;
        }
        if (target_pid_filter < -1 && -target_pid_filter != rp->mp_procgrp) {
            continue;
        }

        // If we reach here, this child is acceptable based on relationship and pid/group filter
        found_qualifying_child_count++;

        // Handle traced children states
        if (is_tracer_of_child) {
            if (rp->mp_flags & TRACE_ZOMBIE) {
                // Traced child meets the pid test and has exited.
                tell_tracer(rp);
                check_parent(rp, TRUE);
                return SUSPEND;
            }
            if (rp->mp_flags & TRACE_STOPPED) {
                // This child meets the pid test and is being traced.
                // Deliver a signal to the tracer, if any.
                for (i = 1; i < _NSIG; i++) {
                    if (sigismember(&rp->mp_sigtrace, i)) {
                        sigdelset(&rp->mp_sigtrace, i);
                        mp->mp_reply.m_pm_lc_wait4.status = W_STOPCODE(i);
                        return rp->mp_pid;
                    }
                }
            }
        }

        // Handle parent's children states
        if (is_parent_of_child) {
            if (rp->mp_flags & ZOMBIE) {
                // This child meets the pid test and has exited.
                int successfully_waited_for = tell_parent(rp, rusage_address);

                if (successfully_waited_for && !(rp->mp_flags & (VFS_CALL | EVENT_CALL))) {
                    cleanup(rp);
                }
                return SUSPEND;
            }
        }
    } // End of for loop

    // No qualifying child has exited or stopped. Now decide whether to wait or error.
    if (found_qualifying_child_count > 0) {
        // At least one child meets the filter, but it's not yet in a waitable state.
        if (wait_options & WNOHANG) {
            return 0; // Parent does not want to wait (WNOHANG set)
        }
        // Parent wants to wait
        mp->mp_flags |= WAITING;
        mp->mp_wpid = (pid_t)target_pid_filter;
        mp->mp_waddr = rusage_address;
        return SUSPEND; // Do not reply, let it wait
    } else {
        // No child even meets the filter criteria.
        return ECHILD; // No such children
    }
}

/*===========================================================================*
 *				wait_test				     *
 *===========================================================================*/
int
wait_test(
	struct mproc *rmp,
	struct mproc *child
)
{
    if (rmp == NULL || child == NULL) {
        return 0;
    }

    pid_t pid_waiting_for = rmp->mp_wpid;
    int parent_is_in_waiting_state = (rmp->mp_flags & WAITING) != 0;

    int child_meets_waiting_criteria =
        (pid_waiting_for == -1 ||
         pid_waiting_for == child->mp_pid ||
         (pid_waiting_for < -1 && -pid_waiting_for == child->mp_procgrp));

    return (parent_is_in_waiting_state && child_meets_waiting_criteria);
}

/*===========================================================================*
 *				zombify					     *
 *===========================================================================*/
static void
zombify(struct mproc *rmp)
{
  if ((rmp->mp_flags & (TRACE_ZOMBIE | ZOMBIE)) != 0) {
    panic("zombify: process was already a zombie");
  }

  const int is_non_parent_traced = (rmp->mp_tracer != NO_TRACER && rmp->mp_tracer != rmp->mp_parent);

  if (is_non_parent_traced) {
    rmp->mp_flags |= TRACE_ZOMBIE;

    struct mproc *tracer_mp = &mproc[rmp->mp_tracer];

    if (!wait_test(tracer_mp, rmp)) {
      return;
    }

    tell_tracer(rmp);
  } else {
    rmp->mp_flags |= ZOMBIE;
  }

  check_parent(rmp, FALSE /*try_cleanup*/);
}

/*===========================================================================*
 *				check_parent				     *
 *===========================================================================*/
static void
check_parent(
	struct mproc *child,
	int try_cleanup
)
{
  const struct mproc *p_mp;

  p_mp = &mproc[child->mp_parent];

  if (p_mp->mp_flags & EXITING) {
  }
  else if (wait_test(p_mp, child)) {
	if (!tell_parent(child, p_mp->mp_waddr))
		try_cleanup = FALSE;

	if (try_cleanup && !(child->mp_flags & (VFS_CALL | EVENT_CALL)))
		cleanup(child);
  }
  else {
	sig_proc(p_mp, SIGCHLD, TRUE, FALSE);
  }
}

/*===========================================================================*
 *				tell_parent				     *
 *===========================================================================*/
static int tell_parent(struct mproc *child, vir_bytes addr)
{
  struct rusage r_usage;
  int mp_parent;
  struct mproc *parent;
  int r;

  if (child->mp_parent <= 0) {
    panic("tell_parent: bad value in mp_parent: %d", child->mp_parent);
  }
  if (!(child->mp_flags & ZOMBIE)) {
    panic("tell_parent: child not a zombie");
  }
  if (child->mp_flags & TOLD_PARENT) {
    panic("tell_parent: telling parent again");
  }

  mp_parent = child->mp_parent;
  parent = &mproc[mp_parent];

  if (addr != 0) {
    memset(&r_usage, 0, sizeof(r_usage));
    set_rusage_times(&r_usage, child->mp_child_utime, child->mp_child_stime);

    if ((r = sys_datacopy(SELF, (vir_bytes)&r_usage, parent->mp_endpoint,
                          addr, sizeof(r_usage))) != OK) {
      reply(child->mp_parent, r);
      return FALSE;
    }
  }

  parent->mp_reply.m_pm_lc_wait4.status =
    W_EXITCODE(child->mp_exitstatus, child->mp_sigstatus);
  reply(child->mp_parent, child->mp_pid);

  parent->mp_flags &= ~WAITING;
  child->mp_flags &= ~ZOMBIE;
  child->mp_flags |= TOLD_PARENT;

  parent->mp_child_utime += child->mp_child_utime;
  parent->mp_child_stime += child->mp_child_stime;

  return TRUE;
}

/*===========================================================================*
 *				tell_tracer				     *
 *===========================================================================*/
static void
tell_tracer(
	struct mproc *child
)
{
  int mp_tracer;
  struct mproc *tracer;

  mp_tracer = child->mp_tracer;
  if (mp_tracer <= 0 || mp_tracer >= NR_PROCS)
	panic("tell_tracer: invalid or out-of-bounds tracer PID: %d", mp_tracer);
  if(!(child->mp_flags & TRACE_ZOMBIE))
  	panic("tell_tracer: child is not a TRACE_ZOMBIE; unexpected state.");
  tracer = &mproc[mp_tracer];

  tracer->mp_reply.m_pm_lc_wait4.status =
	W_EXITCODE(child->mp_exitstatus, (child->mp_sigstatus & 0377));
  reply(child->mp_tracer, child->mp_pid);
  tracer->mp_flags &= ~WAITING;
  child->mp_flags &= ~TRACE_ZOMBIE;
  child->mp_flags |= ZOMBIE;
}

/*===========================================================================*
 *				tracer_died				     *
 *===========================================================================*/
static void
tracer_died(struct mproc *child)
{
    child->mp_tracer = NO_TRACER;
    child->mp_flags &= ~TRACE_EXIT;

    if (!(child->mp_flags & EXITING)) {
        sig_proc(child, SIGKILL, TRUE, FALSE);
        return;
    }

    if (child->mp_flags & TRACE_ZOMBIE) {
        child->mp_flags &= ~TRACE_ZOMBIE;
        child->mp_flags |= ZOMBIE;
        check_parent(child, TRUE);
    }
}

/*===========================================================================*
 *				cleanup					     *
 *===========================================================================*/
static void
cleanup(
	struct mproc *rmp
)
{
  if (rmp != NULL) {
    rmp->mp_pid = 0;
    rmp->mp_flags = 0;
    rmp->mp_child_utime = 0;
    rmp->mp_child_stime = 0;
    procs_in_use--;
  }
}

