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
static int is_proc_table_full(const struct mproc *parent_proc)
{
    return (procs_in_use == NR_PROCS) ||
           (procs_in_use >= NR_PROCS - LAST_FEW && parent_proc->mp_effuid != 0);
}

static int find_free_proc_slot(void)
{
    static unsigned int next_child = 0;
    int i;

    for (i = 0; i < NR_PROCS; i++) {
        next_child = (next_child + 1) % NR_PROCS;
        if (!(mproc[next_child].mp_flags & IN_USE)) {
            return (int)next_child;
        }
    }
    return -1;
}

static void init_child_proc(struct mproc *child_proc,
                            const struct mproc *parent_proc,
                            endpoint_t child_ep, pid_t new_pid, int child_slot)
{
    int i;

    *child_proc = *parent_proc;
    child_proc->mp_sigact = mpsigact[child_slot];
    memcpy(child_proc->mp_sigact, parent_proc->mp_sigact, sizeof(mpsigact[0]));

    child_proc->mp_parent = who_p;

    if (!(child_proc->mp_trace_flags & TO_TRACEFORK)) {
        child_proc->mp_tracer = NO_TRACER;
        child_proc->mp_trace_flags = 0;
        sigemptyset(&child_proc->mp_sigtrace);
    }

    if (child_proc->mp_flags & PRIV_PROC) {
        assert(child_proc->mp_scheduler == NONE);
        child_proc->mp_scheduler = SCHED_PROC_NR;
    }

    child_proc->mp_flags &= (IN_USE | DELAY_CALL | TAINTED);

    child_proc->mp_child_utime = 0;
    child_proc->mp_child_stime = 0;
    child_proc->mp_exitstatus = 0;
    child_proc->mp_sigstatus = 0;
    child_proc->mp_endpoint = child_ep;
    child_proc->mp_pid = new_pid;
    child_proc->mp_started = getticks();

    for (i = 0; i < NR_ITIMERS; i++) {
        child_proc->mp_interval[i] = 0;
    }

    assert(child_proc->mp_eventsub == NO_EVENTSUB);
}

static void prepare_vfs_fork_message(message *msg,
                                     const struct mproc *child_proc,
                                     const struct mproc *parent_proc)
{
    memset(msg, 0, sizeof(*msg));
    msg->m_type = VFS_PM_FORK;
    msg->VFS_PM_ENDPT = child_proc->mp_endpoint;
    msg->VFS_PM_PENDPT = parent_proc->mp_endpoint;
    msg->VFS_PM_CPID = child_proc->mp_pid;
    msg->VFS_PM_REUID = -1;
    msg->VFS_PM_REGID = -1;
}

int do_fork(void)
{
    struct mproc *parent_proc = mp;
    struct mproc *child_proc;
    int child_slot;
    int result;
    endpoint_t child_ep;
    pid_t new_pid;
    message m;

    if (is_proc_table_full(parent_proc)) {
        printf("PM: warning, process table is full!\n");
        return EAGAIN;
    }

    child_slot = find_free_proc_slot();
    if (child_slot < 0) {
        panic("do_fork can't find child slot");
    }

    result = vm_fork(parent_proc->mp_endpoint, child_slot, &child_ep);
    if (result != OK) {
        return result;
    }

    child_proc = &mproc[child_slot];
    procs_in_use++;

    new_pid = get_free_pid();
    init_child_proc(child_proc, parent_proc, child_ep, new_pid, child_slot);

    prepare_vfs_fork_message(&m, child_proc, parent_proc);
    tell_vfs(child_proc, &m);

    if (child_proc->mp_tracer != NO_TRACER) {
        sig_proc(child_proc, SIGSTOP, TRUE, FALSE);
    }

    return SUSPEND;
}

/*===========================================================================*
 *				do_srv_fork				     *
 *===========================================================================*/
static int find_free_proc_slot(void)
{
	static unsigned int next_proc = 0;
	for (int i = 0; i < NR_PROCS; i++) {
		next_proc = (next_proc + 1) % NR_PROCS;
		if (!(mproc[next_proc].mp_flags & IN_USE)) {
			return (int)next_proc;
		}
	}
	return -1;
}

static void init_child_proc(struct mproc *rmc, const struct mproc *rmp,
	int slot_nr, endpoint_t child_ep, pid_t pid)
{
	uid_t uid = m_in.m_lsys_pm_srv_fork.uid;
	gid_t gid = m_in.m_lsys_pm_srv_fork.gid;

	procs_in_use++;
	*rmc = *rmp;			/* copy parent's process slot to child's */
	rmc->mp_sigact = mpsigact[slot_nr];	/* restore mp_sigact ptr */
	memcpy(rmc->mp_sigact, rmp->mp_sigact, sizeof(mpsigact[0]));

	rmc->mp_parent = who_p;			/* record child's parent */

	if (!(rmc->mp_trace_flags & TO_TRACEFORK)) {
		rmc->mp_tracer = NO_TRACER;		/* no tracer attached */
		rmc->mp_trace_flags = 0;
		(void) sigemptyset(&rmc->mp_sigtrace);
	}

	/* inherit only these flags */
	rmc->mp_flags &= (IN_USE|PRIV_PROC|DELAY_CALL);

	/* reset administration */
	rmc->mp_child_utime = 0;
	rmc->mp_child_stime = 0;
	rmc->mp_exitstatus = 0;
	rmc->mp_sigstatus = 0;

	/* set new process properties */
	rmc->mp_endpoint = child_ep;
	rmc->mp_pid = pid;
	rmc->mp_realuid = uid;
	rmc->mp_effuid = uid;
	rmc->mp_svuid = uid;
	rmc->mp_realgid = gid;
	rmc->mp_effgid = gid;
	rmc->mp_svgid = gid;

	/* reset timer intervals */
	for (int i = 0; i < NR_ITIMERS; i++)
		rmc->mp_interval[i] = 0;

	rmc->mp_started = getticks();		/* remember start time, for ps(1) */

	assert(rmc->mp_eventsub == NO_EVENTSUB);
}

static void notify_vfs_of_fork(const struct mproc *rmp, struct mproc *rmc)
{
	message m;
	memset(&m, 0, sizeof(m));
	m.m_type = VFS_PM_SRV_FORK;
	m.VFS_PM_ENDPT = rmc->mp_endpoint;
	m.VFS_PM_PENDPT = rmp->mp_endpoint;
	m.VFS_PM_CPID = rmc->mp_pid;
	m.VFS_PM_REUID = rmc->mp_realuid;
	m.VFS_PM_REGID = rmc->mp_realgid;

	tell_vfs(rmc, &m);
}

int do_srv_fork(void)
{
	/* Only RS is allowed to use srv_fork. */
	if (mp->mp_endpoint != RS_PROC_NR) {
		return EPERM;
	}

	/* If tables might fill up during FORK, don't even start. */
	if ((procs_in_use >= NR_PROCS) ||
		(procs_in_use >= NR_PROCS-LAST_FEW && mp->mp_effuid != 0)) {
		printf("PM: warning, process table is full!\n");
		return EAGAIN;
	}

	/* Find a slot in 'mproc' for the child process. A slot must exist. */
	const int child_slot = find_free_proc_slot();
	if (child_slot < 0) {
		panic("do_srv_fork: could not find a free process slot");
	}

	endpoint_t child_ep;
	int s = vm_fork(mp->mp_endpoint, child_slot, &child_ep);
	if (s != OK) {
		return s;
	}

	/* Set up the child and its memory map. */
	struct mproc *rmc = &mproc[child_slot];
	const pid_t new_pid = get_free_pid();
	init_child_proc(rmc, mp, child_slot, child_ep, new_pid);

	/* Inform VFS about the new process. */
	notify_vfs_of_fork(mp, rmc);

	/* Tell the tracer, if any, about the new child. */
	if (rmc->mp_tracer != NO_TRACER) {
		sig_proc(rmc, SIGSTOP, TRUE /*trace*/, FALSE /* ksig */);
	}

	/* Wakeup the newly created process. */
	reply(child_slot, OK);

	return new_pid;
}

/*===========================================================================*
 *				do_exit					     *
 *===========================================================================*/
int
do_exit(void)
{
 /* Perform the exit(status) system call. The real work is done by exit_proc(),
  * which is also called when a process is killed by a signal. System processes
  * do not use PM's exit() to terminate. If they try to, we warn the user
  * and send a SIGKILL signal to the system process.
  */
  if (mp->mp_flags & PRIV_PROC) {
      printf("PM: system process %d (%s) tries to exit(), sending SIGKILL\n",
          mp->mp_endpoint, mp->mp_name);
      if (sys_kill(mp->mp_endpoint, SIGKILL) != 0) {
          printf("PM: warning, sending SIGKILL to system process %d failed\n",
                 mp->mp_endpoint);
      }
  } else {
      exit_proc(mp, m_in.m_lc_pm_exit.status, FALSE /*dump_core*/);
  }
  return SUSPEND;		/* can't communicate from beyond the grave */
}

/*===========================================================================*
 *				exit_proc				     *
 *===========================================================================*/
static int
should_dump_core(const struct mproc *rmp, int dump_core_requested)
{
	return dump_core_requested &&
		(rmp->mp_realuid == rmp->mp_effuid) &&
		!(rmp->mp_flags & PRIV_PROC);
}

static void
update_accounting(struct mproc *rmp)
{
	clock_t user_time, sys_time;
	int r;

	if ((r = sys_times(rmp->mp_endpoint, &user_time, &sys_time, NULL, NULL)) != OK) {
		panic("exit_proc: sys_times failed: %d", r);
	}
	rmp->mp_child_utime += user_time;
	rmp->mp_child_stime += sys_time;
}

static void
stop_process_at_kernel(struct mproc *rmp)
{
	int r;

	if (!(rmp->mp_flags & PROC_STOPPED)) {
		if ((r = sys_stop(rmp->mp_endpoint)) != OK) {
			panic("sys_stop failed: %d", r);
		}
		rmp->mp_flags |= PROC_STOPPED;
	}

	if ((r = vm_willexit(rmp->mp_endpoint)) != OK) {
		panic("exit_proc: vm_willexit failed: %d", r);
	}
}

static void
notify_vfs_of_exit(struct mproc *rmp, int dump_core)
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

static void
update_proc_state_for_exit(struct mproc *rmp, int exit_status)
{
	rmp->mp_flags &= (IN_USE | VFS_CALL | PRIV_PROC | TRACE_EXIT | PROC_STOPPED);
	rmp->mp_flags |= EXITING;
	rmp->mp_exitstatus = (char)exit_status;
}

static void
disinherit_children(int parent_proc_nr)
{
	struct mproc *child_proc;

	for (child_proc = &mproc[0]; child_proc < &mproc[NR_PROCS]; child_proc++) {
		if (!(child_proc->mp_flags & IN_USE)) {
			continue;
		}

		if (child_proc->mp_tracer == parent_proc_nr) {
			tracer_died(child_proc);
		}

		if (child_proc->mp_parent == parent_proc_nr) {
			child_proc->mp_parent = INIT_PROC_NR;
			if (child_proc->mp_flags & VFS_CALL) {
				child_proc->mp_flags |= NEW_PARENT;
			}
			if (child_proc->mp_flags & ZOMBIE) {
				check_parent(child_proc, TRUE);
			}
		}
	}
}

static void
signal_session_leader_group(pid_t procgrp)
{
	if (procgrp != 0) {
		check_sig(-procgrp, SIGHUP, FALSE);
	}
}

void
exit_proc(struct mproc *rmp, int exit_status, int dump_core)
{
	const int proc_nr = (int)(rmp - mproc);
	const pid_t procgrp = (rmp->mp_pid == mp->mp_procgrp) ? mp->mp_procgrp : 0;
	int r;

	dump_core = should_dump_core(rmp, dump_core);

	if (rmp->mp_flags & ALARM_ON) {
		set_alarm(rmp, (clock_t)0);
	}

	update_accounting(rmp);
	stop_process_at_kernel(rmp);

	if (rmp->mp_endpoint == INIT_PROC_NR) {
		printf("PM: INIT died with exit status %d; showing stacktrace\n", exit_status);
		sys_diagctl_stacktrace(rmp->mp_endpoint);
		return;
	}
	if (rmp->mp_endpoint == VFS_PROC_NR) {
		panic("exit_proc: VFS died");
	}

	notify_vfs_of_exit(rmp, dump_core);

	if (rmp->mp_flags & PRIV_PROC) {
		if ((r = sys_clear(rmp->mp_endpoint)) != OK) {
			panic("exit_proc: sys_clear failed: %d", r);
		}
	}

	update_proc_state_for_exit(rmp, exit_status);

	if (!dump_core) {
		zombify(rmp);
	}

	disinherit_children(proc_nr);
	signal_session_leader_group(procgrp);
}

/*===========================================================================*
 *				exit_restart				     *
 *===========================================================================*/
void exit_restart(struct mproc *rmp)
{
    int r;

    r = sched_stop(rmp->mp_scheduler, rmp->mp_endpoint);
    if (r != OK) {
        printf("PM: The scheduler did not want to give up "
               "scheduling %s, ret=%d.\n", rmp->mp_name, r);
    }

    rmp->mp_scheduler = NONE;

    if ((rmp->mp_flags & (TRACE_ZOMBIE | ZOMBIE | TOLD_PARENT)) == 0) {
        zombify(rmp);
    }

    if (!(rmp->mp_flags & PRIV_PROC)) {
        r = sys_clear(rmp->mp_endpoint);
        if (r != OK) {
            panic("exit_restart: sys_clear failed: %d", r);
        }
    }

    r = vm_exit(rmp->mp_endpoint);
    if (r != OK) {
        panic("exit_restart: vm_exit failed: %d", r);
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
	int pidarg;
	int options;
	vir_bytes addr;
	int children_found;
	int i;
	int is_parent;
	int is_tracer;

	pidarg  = m_in.m_lc_pm_wait4.pid;
	options = m_in.m_lc_pm_wait4.options;
	addr    = m_in.m_lc_pm_wait4.addr;

	if (pidarg == 0) {
		pidarg = -mp->mp_procgrp;
	}

	children_found = 0;
	for (rp = &mproc[0]; rp < &mproc[NR_PROCS]; rp++) {
		if ((rp->mp_flags & (IN_USE | TOLD_PARENT)) != IN_USE) {
			continue;
		}

		is_parent = (rp->mp_parent == who_p);
		is_tracer = (rp->mp_tracer == who_p);

		if (!is_parent && !is_tracer) {
			continue;
		}

		if (!is_parent && (rp->mp_flags & ZOMBIE)) {
			continue;
		}

		if (pidarg > 0 && pidarg != rp->mp_pid) {
			continue;
		}
		if (pidarg < -1 && -pidarg != rp->mp_procgrp) {
			continue;
		}

		children_found++;

		if (is_tracer) {
			if (rp->mp_flags & TRACE_ZOMBIE) {
				tell_tracer(rp);
				check_parent(rp, TRUE);
				return SUSPEND;
			}
			if (rp->mp_flags & TRACE_STOPPED) {
				int signum = 0;
				for (i = 1; i < _NSIG; i++) {
					if (sigismember(&rp->mp_sigtrace, i)) {
						sigdelset(&rp->mp_sigtrace, i);
						signum = i;
						break;
					}
				}
				if (signum != 0) {
					mp->mp_reply.m_pm_lc_wait4.status = W_STOPCODE(signum);
					return rp->mp_pid;
				}
			}
		}

		if (is_parent && (rp->mp_flags & ZOMBIE)) {
			if (tell_parent(rp, addr)) {
				if (!(rp->mp_flags & (VFS_CALL | EVENT_CALL))) {
					cleanup(rp);
				}
			}
			return SUSPEND;
		}
	}

	if (children_found > 0) {
		if (options & WNOHANG) {
			return 0;
		}
		mp->mp_flags |= WAITING;
		mp->mp_wpid = (pid_t) pidarg;
		mp->mp_waddr = addr;
		return SUSPEND;
	}

	return ECHILD;
}

/*===========================================================================*
 *				wait_test				     *
 *===========================================================================*/
int wait_test(const struct mproc *rmp, const struct mproc *child)
{
    if (rmp == NULL || child == NULL) {
        return 0;
    }

    if ((rmp->mp_flags & WAITING) == 0) {
        return 0;
    }

    const pid_t pid_arg = rmp->mp_wpid;

    return (pid_arg == -1) ||
           (pid_arg == child->mp_pid) ||
           (-pid_arg == child->mp_procgrp);
}

/*===========================================================================*
 *				zombify					     *
 *===========================================================================*/
static void
zombify(struct mproc *rmp)
{
    if (rmp->mp_flags & (TRACE_ZOMBIE | ZOMBIE)) {
        panic("zombify: process was already a zombie");
    }

    const bool is_traced_by_non_parent = (rmp->mp_tracer != NO_TRACER &&
                                          rmp->mp_tracer != rmp->mp_parent);

    if (is_traced_by_non_parent) {
        rmp->mp_flags |= TRACE_ZOMBIE;

        struct mproc *t_mp = &mproc[rmp->mp_tracer];

        if (!wait_test(t_mp, rmp)) {
            return;
        }

        tell_tracer(rmp);
    } else {
        rmp->mp_flags |= ZOMBIE;
    }

    check_parent(rmp, FALSE);
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
	struct mproc *p_mp = &mproc[child->mp_parent];

	if (p_mp->mp_flags & EXITING) {
		return;
	}

	if (wait_test(p_mp, child)) {
		if (tell_parent(child, p_mp->mp_waddr)) {
			if (try_cleanup && !(child->mp_flags & (VFS_CALL | EVENT_CALL))) {
				cleanup(child);
			}
		}
	} else {
		sig_proc(p_mp, SIGCHLD, TRUE, FALSE);
	}
}

/*===========================================================================*
 *				tell_parent				     *
 *===========================================================================*/
static int tell_parent(struct mproc *child, vir_bytes addr)
{
    int mp_parent;
    struct mproc *parent;
    struct rusage r_usage;
    int r;

    mp_parent = child->mp_parent;
    if (mp_parent <= 0) {
        panic("tell_parent: bad value in mp_parent: %d", mp_parent);
    }
    if (!(child->mp_flags & ZOMBIE)) {
        panic("tell_parent: child not a zombie");
    }
    if (child->mp_flags & TOLD_PARENT) {
        panic("tell_parent: telling parent again");
    }

    parent = &mproc[mp_parent];

    if (addr != 0) {
        memset(&r_usage, 0, sizeof(r_usage));
        set_rusage_times(&r_usage, child->mp_child_utime,
            child->mp_child_stime);

        r = sys_datacopy(SELF, (vir_bytes)&r_usage, parent->mp_endpoint,
            addr, sizeof(r_usage));

        if (r != OK) {
            reply(parent->mp_endpoint, r);
            return FALSE;
        }
    }

    parent->mp_reply.m_pm_lc_wait4.status =
        W_EXITCODE(child->mp_exitstatus, child->mp_sigstatus);
    reply(parent->mp_endpoint, child->mp_pid);

    parent->mp_flags &= ~WAITING;
    parent->mp_child_utime += child->mp_child_utime;
    parent->mp_child_stime += child->mp_child_stime;

    child->mp_flags &= ~ZOMBIE;
    child->mp_flags |= TOLD_PARENT;

    return TRUE;
}

/*===========================================================================*
 *				tell_tracer				     *
 *===========================================================================*/
static void
tell_tracer(struct mproc *child)
{
    int mp_tracer;
    struct mproc *tracer;

    if (!(child->mp_flags & TRACE_ZOMBIE)) {
        panic("tell_tracer: child not a zombie");
    }

    mp_tracer = child->mp_tracer;

    if (mp_tracer <= 0 || mp_tracer >= NR_PROCS) {
        panic("tell_tracer: bad value in mp_tracer: %d", mp_tracer);
    }

    tracer = &mproc[mp_tracer];

    tracer->mp_reply.m_pm_lc_wait4.status =
        W_EXITCODE(child->mp_exitstatus, (child->mp_sigstatus & 0xFF));

    reply(mp_tracer, child->mp_pid);

    tracer->mp_flags &= ~WAITING;
    child->mp_flags &= ~TRACE_ZOMBIE;
    child->mp_flags |= ZOMBIE;
}

/*===========================================================================*
 *				tracer_died				     *
 *===========================================================================*/
static void tracer_died(struct mproc *child)
{
    child->mp_tracer = NO_TRACER;
    child->mp_flags &= ~TRACE_EXIT;

    if (!(child->mp_flags & EXITING)) {
        sig_proc(child, SIGKILL, TRUE, FALSE);
    } else if (child->mp_flags & TRACE_ZOMBIE) {
        child->mp_flags = (child->mp_flags & ~TRACE_ZOMBIE) | ZOMBIE;
        check_parent(child, TRUE);
    }
}

/*===========================================================================*
 *				cleanup					     *
 *===========================================================================*/
static void
cleanup(struct mproc *process)
{
	if (process == NULL) {
		return;
	}

	process->mp_pid = 0;
	process->mp_flags = 0;
	process->mp_child_utime = 0;
	process->mp_child_stime = 0;
	procs_in_use--;
}

