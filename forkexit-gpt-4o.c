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
#include <stdio.h>
#include <string.h>
#include <assert.h>
#include <signal.h>

#define NR_PROCS 256
#define LAST_FEW 5
#define IN_USE 0x1
#define DELAY_CALL 0x2
#define TAINTED 0x4
#define PRIV_PROC 0x8
#define NO_TRACER -1
#define SCHED_PROC_NR 1
#define NONE -1
#define NO_EVENTSUB -1
#define NR_ITIMERS 4
#define VFS_PM_FORK 0
#define SUSPEND 0
#define TRUE 1
#define FALSE 0

typedef struct mproc {
    int mp_flags;
    int mp_endpoint;
    int mp_effuid;
    int mp_trace_flags;
    int mp_tracer;
    int mp_scheduler;
    int mp_parent;
    void *mp_sigact;
    int mp_child_utime;
    int mp_child_stime;
    int mp_exitstatus;
    int mp_sigstatus;
    int mp_pid;
    int mp_interval[NR_ITIMERS];
    unsigned long mp_started;
    int mp_eventsub;
} mproc;

typedef struct message {
    int m_type;
    int VFS_PM_ENDPT;
    int VFS_PM_PENDPT;
    int VFS_PM_CPID;
    int VFS_PM_REUID;
    int VFS_PM_REGID;
} message;

typedef unsigned int endpoint_t;
typedef int pid_t;

int procs_in_use = 0;
mproc mproc[NR_PROCS];
void *mpsigact[NR_PROCS];
int mp;
int who_p;
void panic(const char *fmt, ...);
int vm_fork(int parent_ep, unsigned int slot, endpoint_t *child_ep);
unsigned long getticks(void);
pid_t get_free_pid(void);
void tell_vfs(mproc *child, message *m);
void sig_proc(mproc *proc, int sig, int trace, int ksig);
int sigemptyset(void *set);

int do_fork(void) {
    mproc *rmp = &mproc[mp];
    mproc *rmc;
    pid_t new_pid;
    static unsigned int next_child = 0;
    int s;
    endpoint_t child_ep;
    message m;

    if (procs_in_use >= NR_PROCS || (procs_in_use >= NR_PROCS - LAST_FEW && rmp->mp_effuid != 0)) {
        fprintf(stderr, "PM: warning, process table is full!\n");
        return EAGAIN;
    }

    for (int n = 0; n <= NR_PROCS; n++) {
        next_child = (next_child + 1) % NR_PROCS;
        if (!(mproc[next_child].mp_flags & IN_USE)) break;
        if (n == NR_PROCS) panic("do_fork: no free child slot");
    }

    s = vm_fork(rmp->mp_endpoint, next_child, &child_ep);
    if (s != OK) return s;

    rmc = &mproc[next_child];
    procs_in_use++;
    *rmc = *rmp;
    rmc->mp_sigact = mpsigact[next_child];
    memcpy(rmc->mp_sigact, rmp->mp_sigact, sizeof(mpsigact[next_child]));
    rmc->mp_parent = who_p;

    if (!(rmc->mp_trace_flags & TO_TRACEFORK)) {
        rmc->mp_tracer = NO_TRACER;
        rmc->mp_trace_flags = 0;
        sigemptyset(&rmc->mp_sigtrace);
    }

    if (rmc->mp_flags & PRIV_PROC) {
        assert(rmc->mp_scheduler == NONE);
        rmc->mp_scheduler = SCHED_PROC_NR;
    }

    rmc->mp_flags &= (IN_USE | DELAY_CALL | TAINTED);
    rmc->mp_child_utime = 0;
    rmc->mp_child_stime = 0;
    rmc->mp_exitstatus = 0;
    rmc->mp_sigstatus = 0;
    rmc->mp_endpoint = child_ep;
    memset(rmc->mp_interval, 0, sizeof(rmc->mp_interval));
    rmc->mp_started = getticks();
    assert(rmc->mp_eventsub == NO_EVENTSUB);

    new_pid = get_free_pid();
    rmc->mp_pid = new_pid;

    memset(&m, 0, sizeof(m));
    m.m_type = VFS_PM_FORK;
    m.VFS_PM_ENDPT = rmc->mp_endpoint;
    m.VFS_PM_PENDPT = rmp->mp_endpoint;
    m.VFS_PM_CPID = rmc->mp_pid;
    m.VFS_PM_REUID = -1;
    m.VFS_PM_REGID = -1;

    tell_vfs(rmc, &m);

    if (rmc->mp_tracer != NO_TRACER)
        sig_proc(rmc, SIGSTOP, TRUE, FALSE);

    return SUSPEND;
}

/*===========================================================================*
 *				do_srv_fork				     *
 *===========================================================================*/
int do_srv_fork(void) {
    struct mproc *rmp = mp;
    struct mproc *rmc;
    int s;
    pid_t new_pid;
    static unsigned int next_child = 0;
    endpoint_t child_ep;
    message m;

    if (rmp->mp_endpoint != RS_PROC_NR) return EPERM;

    if (procs_in_use >= NR_PROCS || 
        (procs_in_use >= NR_PROCS - LAST_FEW && rmp->mp_effuid != 0)) {
        printf("PM: warning, process table is full!\n");
        return EAGAIN;
    }

    unsigned int n = 0;
    while (n++ < NR_PROCS && (mproc[next_child].mp_flags & IN_USE)) {
        next_child = (next_child + 1) % NR_PROCS;
    }

    if (n > NR_PROCS) panic("do_fork can't find child slot");
    if (next_child >= NR_PROCS || (mproc[next_child].mp_flags & IN_USE))
        panic("do_fork finds wrong child slot: %d", next_child);

    if ((s = vm_fork(rmp->mp_endpoint, next_child, &child_ep)) != OK) {
        return s;
    }

    rmc = &mproc[next_child];
    procs_in_use++;
    *rmc = *rmp;
    rmc->mp_sigact = mpsigact[next_child];
    memcpy(rmc->mp_sigact, rmp->mp_sigact, sizeof(mpsigact[next_child]));
    rmc->mp_parent = who_p;
    if (!(rmc->mp_trace_flags & TO_TRACEFORK)) {
        rmc->mp_tracer = NO_TRACER;
        rmc->mp_trace_flags = 0;
        sigemptyset(&rmc->mp_sigtrace);
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
    for (int i = 0; i < NR_ITIMERS; i++) rmc->mp_interval[i] = 0;
    rmc->mp_started = getticks();

    assert(rmc->mp_eventsub == NO_EVENTSUB);

    new_pid = get_free_pid();
    rmc->mp_pid = new_pid;

    memset(&m, 0, sizeof(m));
    m.m_type = VFS_PM_SRV_FORK;
    m.VFS_PM_ENDPT = rmc->mp_endpoint;
    m.VFS_PM_PENDPT = rmp->mp_endpoint;
    m.VFS_PM_CPID = rmc->mp_pid;
    m.VFS_PM_REUID = m_in.m_lsys_pm_srv_fork.uid;
    m.VFS_PM_REGID = m_in.m_lsys_pm_srv_fork.gid;

    tell_vfs(rmc, &m);

    if (rmc->mp_tracer != NO_TRACER)
        sig_proc(rmc, SIGSTOP, TRUE, FALSE);

    reply(rmc - mproc, OK);

    return rmc->mp_pid;
}

/*===========================================================================*
 *				do_exit					     *
 *===========================================================================*/
int do_exit(void) {
    if (mp->mp_flags & PRIV_PROC) {
        printf("PM: system process %d (%s) attempts to exit(), sending SIGKILL\n",
               mp->mp_endpoint, mp->mp_name);
        if (sys_kill(mp->mp_endpoint, SIGKILL) != 0) {
            fprintf(stderr, "Failed to send SIGKILL to system process %d\n", mp->mp_endpoint);
        }
    } else {
        exit_proc(mp, m_in.m_lc_pm_exit.status, FALSE);
    }
    return SUSPEND;
}

/*===========================================================================*
 *				exit_proc				     *
 *===========================================================================*/
void exit_proc(struct mproc *rmp, int exit_status, int dump_core) {
    int proc_nr, proc_nr_e, r;
    pid_t procgrp = 0;
    clock_t user_time, sys_time;
    message m;

    if (rmp->mp_realuid != rmp->mp_effuid) {
        dump_core = FALSE;
    }

    if (rmp->mp_flags & PRIV_PROC) {
        dump_core = FALSE;
    }

    proc_nr = (int)(rmp - mproc);
    proc_nr_e = rmp->mp_endpoint;

    if (rmp->mp_pid == mp->mp_procgrp) {
        procgrp = mp->mp_procgrp;
    }

    if (rmp->mp_flags & ALARM_ON) {
        set_alarm(rmp, (clock_t)0);
    }

    if ((r = sys_times(proc_nr_e, &user_time, &sys_time, NULL, NULL)) != OK) {
        panic("exit_proc: sys_times failed: %d", r);
    }
    rmp->mp_child_utime += user_time;
    rmp->mp_child_stime += sys_time;

    if (!(rmp->mp_flags & PROC_STOPPED)) {
        if ((r = sys_stop(proc_nr_e)) != OK) {
            panic("sys_stop failed: %d", r);
        }
        rmp->mp_flags |= PROC_STOPPED;
    }

    if ((r = vm_willexit(proc_nr_e)) != OK) {
        panic("exit_proc: vm_willexit failed: %d", r);
    }

    if (proc_nr_e == INIT_PROC_NR) {
        printf("PM: INIT died with exit status %d; showing stacktrace\n", exit_status);
        sys_diagctl_stacktrace(proc_nr_e);
        return;
    }

    if (proc_nr_e == VFS_PROC_NR) {
        panic("exit_proc: VFS died: %d", r);
    }

    memset(&m, 0, sizeof(m));
    m.m_type = dump_core ? VFS_PM_DUMPCORE : VFS_PM_EXIT;
    m.VFS_PM_ENDPT = rmp->mp_endpoint;

    if (dump_core) {
        m.VFS_PM_TERM_SIG = rmp->mp_sigstatus;
        m.VFS_PM_PATH = rmp->mp_name;
    }

    tell_vfs(rmp, &m);

    if (rmp->mp_flags & PRIV_PROC) {
        if ((r = sys_clear(rmp->mp_endpoint)) != OK) {
            panic("exit_proc: sys_clear failed: %d", r);
        }
    }

    rmp->mp_flags &= (IN_USE | VFS_CALL | PRIV_PROC | TRACE_EXIT | PROC_STOPPED);
    rmp->mp_flags |= EXITING;

    rmp->mp_exitstatus = (char)exit_status;

    if (!dump_core) {
        zombify(rmp);
    }

    struct mproc *tmp;
    for (tmp = &mproc[0]; tmp < &mproc[NR_PROCS]; tmp++) {
        if (!(tmp->mp_flags & IN_USE)) continue;
        if (tmp->mp_tracer == proc_nr) {
            tracer_died(tmp);
        }
        if (tmp->mp_parent == proc_nr) {
            tmp->mp_parent = INIT_PROC_NR;
            if (tmp->mp_flags & VFS_CALL) {
                tmp->mp_flags |= NEW_PARENT;
            }
            if (tmp->mp_flags & ZOMBIE) {
                check_parent(tmp, TRUE);
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
#include <stdio.h>
#include <stdlib.h>
#include <errno.h>

#define OK 0
#define NONE -1
#define TRACE_ZOMBIE 0x01
#define ZOMBIE 0x02
#define TOLD_PARENT 0x04
#define PRIV_PROC 0x08
#define TRACE_EXIT 0x10
#define SCHED_PROCESS_STOP_FAILURE -1

struct mproc {
    char *mp_name;
    int mp_scheduler;
    int mp_endpoint;
    int mp_flags;
    int mp_tracer;
    struct {
        int data;
    } mp_reply;
};

void schedule_stop(int scheduler, int endpoint);
void zombify(struct mproc *rmp);
int sys_clear(int endpoint);
int vm_exit(int endpoint);
void panic(const char *format, int code);
void reply(int tracer, int result);
void cleanup(struct mproc *rmp);

void exit_restart(struct mproc *rmp) {
    if (schedule_stop(rmp->mp_scheduler, rmp->mp_endpoint) != OK) {
        printf("PM: Failed to stop scheduling %s.\n", rmp->mp_name);
    }
    rmp->mp_scheduler = NONE;

    if (!(rmp->mp_flags & (TRACE_ZOMBIE | ZOMBIE | TOLD_PARENT))) {
        zombify(rmp);
    }

    if (!(rmp->mp_flags & PRIV_PROC)) {
        if (sys_clear(rmp->mp_endpoint) != OK) {
            panic("exit_restart: sys_clear failed", errno);
        }
    }

    if (vm_exit(rmp->mp_endpoint) != OK) {
        panic("exit_restart: vm_exit failed", errno);
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
int do_wait4(void) {
    struct mproc *rp;
    vir_bytes addr;
    int pidarg, options, children = 0, waited_for = 0;

    pidarg = m_in.m_lc_pm_wait4.pid;
    options = m_in.m_lc_pm_wait4.options;
    addr = m_in.m_lc_pm_wait4.addr;

    if (pidarg == 0) pidarg = -mp->mp_procgrp;

    for (rp = mproc; rp < &mproc[NR_PROCS]; rp++) {
        if ((rp->mp_flags & IN_USE) == 0) continue;
        if (rp->mp_parent != who_p && rp->mp_tracer != who_p) continue;
        if (rp->mp_parent != who_p && (rp->mp_flags & ZOMBIE)) continue;

        if (pidarg > 0 && pidarg != rp->mp_pid) continue;
        if (pidarg < -1 && -pidarg != rp->mp_procgrp) continue;

        children++;

        if (rp->mp_tracer == who_p) {
            if (rp->mp_flags & TRACE_ZOMBIE) {
                tell_tracer(rp);
                check_parent(rp, 1);
                return SUSPEND;
            }
            if (rp->mp_flags & TRACE_STOPPED) {
                for (int i = 1; i < _NSIG; i++) {
                    if (sigismember(&rp->mp_sigtrace, i)) {
                        sigdelset(&rp->mp_sigtrace, i);
                        mp->mp_reply.m_pm_lc_wait4.status = W_STOPCODE(i);
                        return rp->mp_pid;
                    }
                }
            }
        }

        if (rp->mp_parent == who_p && (rp->mp_flags & ZOMBIE)) {
            waited_for = tell_parent(rp, addr);
            if (waited_for && !(rp->mp_flags & (VFS_CALL | EVENT_CALL)))
                cleanup(rp);
            return SUSPEND;
        }
    }

    if (children > 0) {
        if (options & WNOHANG) return 0;
        mp->mp_flags |= WAITING;
        mp->mp_wpid = (pid_t) pidarg;
        mp->mp_waddr = addr;
        return SUSPEND;
    } else {
        return ECHILD;
    }
}

/*===========================================================================*
 *				wait_test				     *
 *===========================================================================*/
int wait_test(struct mproc *rmp, struct mproc *child) {
    pid_t pidarg = rmp->mp_wpid;
    int parent_waiting = (rmp->mp_flags & WAITING) != 0;
    int right_child = (pidarg == -1 || pidarg == child->mp_pid || -pidarg == child->mp_procgrp);
    
    return parent_waiting && right_child;
}

/*===========================================================================*
 *				zombify					     *
 *===========================================================================*/
static void zombify(struct mproc *rmp) {
  struct mproc *t_mp;

  if (rmp == NULL || (rmp->mp_flags & (TRACE_ZOMBIE | ZOMBIE)) != 0) {
    panic("zombify: invalid process state");
    return;
  }

  if (rmp->mp_tracer != NO_TRACER && rmp->mp_tracer != rmp->mp_parent) {
    rmp->mp_flags |= TRACE_ZOMBIE;
    t_mp = &mproc[rmp->mp_tracer];
    
    if (t_mp != NULL && wait_test(t_mp, rmp)) {
      tell_tracer(rmp);
    }
  } else {
    rmp->mp_flags |= ZOMBIE;
  }

  check_parent(rmp, FALSE);
}

/*===========================================================================*
 *				check_parent				     *
 *===========================================================================*/
static void check_parent(struct mproc *child, int try_cleanup) {
    struct mproc *parent_proc = &mproc[child->mp_parent];

    if (parent_proc->mp_flags & EXITING) {
        return;
    }

    if (wait_test(parent_proc, child)) {
        if (!tell_parent(child, parent_proc->mp_waddr)) {
            try_cleanup = 0;
        }

        if (try_cleanup && !(child->mp_flags & (VFS_CALL | EVENT_CALL))) {
            cleanup(child);
        }
    } else {
        sig_proc(parent_proc, SIGCHLD, 1, 0);
    }
}

/*===========================================================================*
 *				tell_parent				     *
 *===========================================================================*/
#include <string.h>
#include <errno.h>

#define CHECK(condition, msg, retval) \
    do { \
        if (!(condition)) { \
            panic(msg); \
            return retval; \
        } \
    } while (0)

#define CHECK_OK(expr, retval) \
    do { \
        if ((expr) != OK) { \
            return retval; \
        } \
    } while (0)

static int tell_parent(struct mproc *child, vir_bytes addr) {
    struct rusage r_usage;
    struct mproc *parent;
    int r, mp_parent = child->mp_parent;

    CHECK(mp_parent > 0, "tell_parent: bad value in mp_parent", FALSE);
    CHECK(child->mp_flags & ZOMBIE, "tell_parent: child not a zombie", FALSE);
    CHECK(!(child->mp_flags & TOLD_PARENT), "tell_parent: telling parent again", FALSE);

    parent = &mproc[mp_parent];

    if (addr) {
        memset(&r_usage, 0, sizeof(r_usage));
        set_rusage_times(&r_usage, child->mp_child_utime, child->mp_child_stime);
        CHECK_OK(sys_datacopy(SELF, (vir_bytes)&r_usage, parent->mp_endpoint, addr, sizeof(r_usage)), FALSE);
    }

    parent->mp_reply.m_pm_lc_wait4.status = W_EXITCODE(child->mp_exitstatus, child->mp_sigstatus);
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
static void tell_tracer(struct mproc *child) {
    if (child == NULL || child->mp_tracer <= 0) {
        panic("tell_tracer: invalid child or bad mp_tracer value");
    }

    if (!(child->mp_flags & TRACE_ZOMBIE)) {
        panic("tell_tracer: child not a zombie");
    }

    struct mproc *tracer = &mproc[child->mp_tracer];

    tracer->mp_reply.m_pm_lc_wait4.status = W_EXITCODE(child->mp_exitstatus, child->mp_sigstatus & 0377);
    reply(child->mp_tracer, child->mp_pid);

    tracer->mp_flags &= ~WAITING;   // tracer no longer waiting
    child->mp_flags &= ~TRACE_ZOMBIE; // child no longer zombie to tracer
    child->mp_flags |= ZOMBIE;      // child is now zombie to parent
}

/*===========================================================================*
 *				tracer_died				     *
 *===========================================================================*/
static void tracer_died(struct mproc *child) {
    if (!child) return; // Check for null pointer

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
void cleanup(struct mproc *rmp) {
    if (rmp == NULL) return;
    rmp->mp_pid = 0;
    rmp->mp_flags = 0;
    rmp->mp_child_utime = 0;
    rmp->mp_child_stime = 0;
    if (procs_in_use > 0) procs_in_use--;
}

