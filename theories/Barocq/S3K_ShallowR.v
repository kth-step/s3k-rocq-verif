From Stdlib Require Import Bool List BinIntDef.
From compcert Require Import Integers.
From RecordUpdate Require Import RecordUpdate.
From S3K.BarocqComp Require Import Option Barray Intop Utils.
From S3K.BarocqComp Require Import ShallowNotations.

(** * Type definitions *)

Inductive Types_reg_t :=
  | Types_Reg_pc
  | Types_Reg_ra
  | Types_Reg_sp
  | Types_Reg_gp
  | Types_Reg_tp
  | Types_Reg_a0
  | Types_Reg_a1
  | Types_Reg_a2
  | Types_Reg_a3
  | Types_Reg_a4
  | Types_Reg_a5
  | Types_Reg_a6
  | Types_Reg_a7
  | Types_Reg_t0
  | Types_Reg_t1
  | Types_Reg_t2
  | Types_Reg_t3
  | Types_Reg_t4
  | Types_Reg_t5
  | Types_Reg_t6
  | Types_Reg_s0
  | Types_Reg_s1
  | Types_Reg_s2
  | Types_Reg_s3
  | Types_Reg_s4
  | Types_Reg_s5
  | Types_Reg_s6
  | Types_Reg_s7
  | Types_Reg_s8
  | Types_Reg_s9
  | Types_Reg_s10
  | Types_Reg_s11.

Inductive Types_capty_t :=
  | Types_Capty_NONE
  | Types_Capty_MEM
  | Types_Capty_TSL
  | Types_Capty_MON
  | Types_Capty_IPC
  | Types_Capty_INVALID.

Record Types_pmp_t := mk_Types_pmp_t {
  types_pmp_t_addr: list u64;
  types_pmp_t_cfg: u64
}.

Record Types_trap_t := mk_Types_trap_t {
  types_trap_t_tpc: u64;
  types_trap_t_tsp: u64;
  types_trap_t_epc: u64;
  types_trap_t_esp: u64;
  types_trap_t_ecause: u64;
  types_trap_t_eval: u64
}.

Record Types_proc_t := mk_Types_proc_t {
  types_proc_t_state: u64;
  types_proc_t_regs: list u64;
  types_proc_t_pmp: Types_pmp_t;
  types_proc_t_trap: Types_trap_t;
  types_proc_t_timeout: u64;
  types_proc_t_pid: u64
}.

Record Types_tsl_t := mk_Types_tsl_t {
  types_tsl_t_owner: u64;
  types_tsl_t_cfree: u64;
  types_tsl_t_csize: u64;
  types_tsl_t_hart: u64;
  types_tsl_t_enabled: bool;
  types_tsl_t_base: u64;
  types_tsl_t_size: u64;
  types_tsl_t_free: u64
}.

Record Types_mem_t := mk_Types_mem_t {
  types_mem_t_owner: u64;
  types_mem_t_cfree: u64;
  types_mem_t_csize: u64;
  types_mem_t_slot: u32;
  types_mem_t_rwx: u32;
  types_mem_t_base: u32;
  types_mem_t_size: u32
}.

Record Types_mon_t := mk_Types_mon_t {
  types_mon_t_owner: u64;
  types_mon_t_cfree: u64;
  types_mon_t_csize: u64;
  types_mon_t_pid: u64
}.

Record Types_ipc_t := mk_Types_ipc_t {
  types_ipc_t_owner: u64;
  types_ipc_t_cfree: u64;
  types_ipc_t_csize: u64;
  types_ipc_t_mode: u32;
  types_ipc_t_flag: u32;
  types_ipc_t_sink: u64;
  types_ipc_t_source: u64;
  types_ipc_t_opt: u32
}.

Record Types_frame_t := mk_Types_frame_t {
  types_frame_t_pid: u64;
  types_frame_t_length: u64
}.

Record Types_kstate := mk_Types_kstate {
  types_kstate_procs: list Types_proc_t;
  types_kstate_tsl_table: list Types_tsl_t;
  types_kstate_mon_table: list Types_mon_t;
  types_kstate_ipc_table: list Types_ipc_t;
  types_kstate_message: list u64;
  types_kstate_active_pid: u64;
  types_kstate_errcode: i64
}.

Inductive Syscall_syscall :=
  | Syscall_Syscall_pid_get
  | Syscall_Syscall_vreg_get
  | Syscall_Syscall_vreg_set
  | Syscall_Syscall_sync
  | Syscall_Syscall_sleep_until
  | Syscall_Syscall_mem_introspect
  | Syscall_Syscall_tsl_introspect
  | Syscall_Syscall_mon_introspect
  | Syscall_Syscall_ipc_introspect
  | Syscall_Syscall_mem_derive
  | Syscall_Syscall_tsl_derive
  | Syscall_Syscall_mon_derive
  | Syscall_Syscall_ipc_derive
  | Syscall_Syscall_mem_revoke
  | Syscall_Syscall_tsl_revoke
  | Syscall_Syscall_mon_revoke
  | Syscall_Syscall_ipc_revoke
  | Syscall_Syscall_mem_delete
  | Syscall_Syscall_tsl_delete
  | Syscall_Syscall_mon_delete
  | Syscall_Syscall_ipc_delete
  | Syscall_Syscall_mem_pmp_get
  | Syscall_Syscall_mem_pmp_set
  | Syscall_Syscall_mem_pmp_clear
  | Syscall_Syscall_tsl_set
  | Syscall_Syscall_mon_suspend
  | Syscall_Syscall_mon_resume
  | Syscall_Syscall_mon_yield
  | Syscall_Syscall_mon_reg_get
  | Syscall_Syscall_mon_reg_set
  | Syscall_Syscall_mon_vreg_get
  | Syscall_Syscall_mon_vreg_set
  | Syscall_Syscall_mon_mem_introspect
  | Syscall_Syscall_mon_tsl_introspect
  | Syscall_Syscall_mon_mon_introspect
  | Syscall_Syscall_mon_ipc_introspect
  | Syscall_Syscall_mon_mem_grant
  | Syscall_Syscall_mon_tsl_grant
  | Syscall_Syscall_mon_mon_grant
  | Syscall_Syscall_mon_ipc_grant
  | Syscall_Syscall_mon_mem_derive
  | Syscall_Syscall_mon_tsl_derive
  | Syscall_Syscall_mon_mon_derive
  | Syscall_Syscall_mon_ipc_derive
  | Syscall_Syscall_mon_mem_pmp_get
  | Syscall_Syscall_mon_mem_pmp_set
  | Syscall_Syscall_mon_mem_pmp_clear
  | Syscall_Syscall_mon_tsl_set
  | Syscall_Syscall_ipc_send
  | Syscall_Syscall_ipc_recv
  | Syscall_Syscall_ipc_call
  | Syscall_Syscall_ipc_reply
  | Syscall_Syscall_ipc_replyrecv
  | Syscall_Syscall_ipc_asend
  | Syscall_Syscall_ipc_arecv
  | Syscall_Syscall_max.

(** * Setters for records *)

Instance eta_Types_pmp_t : Settable Types_pmp_t :=
  settable! mk_Types_pmp_t <types_pmp_t_addr; types_pmp_t_cfg>.

Instance eta_Types_trap_t : Settable Types_trap_t :=
  settable! mk_Types_trap_t <types_trap_t_tpc; types_trap_t_tsp; types_trap_t_epc; types_trap_t_esp; types_trap_t_ecause; types_trap_t_eval>.

Instance eta_Types_proc_t : Settable Types_proc_t :=
  settable! mk_Types_proc_t <types_proc_t_state; types_proc_t_regs; types_proc_t_pmp; types_proc_t_trap; types_proc_t_timeout; types_proc_t_pid>.

Instance eta_Types_tsl_t : Settable Types_tsl_t :=
  settable! mk_Types_tsl_t <types_tsl_t_owner; types_tsl_t_cfree; types_tsl_t_csize; types_tsl_t_hart; types_tsl_t_enabled; types_tsl_t_base; types_tsl_t_size; types_tsl_t_free>.

Instance eta_Types_mem_t : Settable Types_mem_t :=
  settable! mk_Types_mem_t <types_mem_t_owner; types_mem_t_cfree; types_mem_t_csize; types_mem_t_slot; types_mem_t_rwx; types_mem_t_base; types_mem_t_size>.

Instance eta_Types_mon_t : Settable Types_mon_t :=
  settable! mk_Types_mon_t <types_mon_t_owner; types_mon_t_cfree; types_mon_t_csize; types_mon_t_pid>.

Instance eta_Types_ipc_t : Settable Types_ipc_t :=
  settable! mk_Types_ipc_t <types_ipc_t_owner; types_ipc_t_cfree; types_ipc_t_csize; types_ipc_t_mode; types_ipc_t_flag; types_ipc_t_sink; types_ipc_t_source; types_ipc_t_opt>.

Instance eta_Types_frame_t : Settable Types_frame_t :=
  settable! mk_Types_frame_t <types_frame_t_pid; types_frame_t_length>.

Instance eta_Types_kstate : Settable Types_kstate :=
  settable! mk_Types_kstate <types_kstate_procs; types_kstate_tsl_table; types_kstate_mon_table; types_kstate_ipc_table; types_kstate_message; types_kstate_active_pid; types_kstate_errcode>.

(** * Auxiliary functions *)

Lemma Types_reg_t_eq_dec :
  forall (x y: Types_reg_t), {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Definition Types_reg_t_eq (x y: Types_reg_t) : bool :=
  if Types_reg_t_eq_dec x y then true else false.

Definition Types_reg_t_neq (x y: Types_reg_t) : bool :=
  negb (Types_reg_t_eq x y).

Lemma Types_capty_t_eq_dec :
  forall (x y: Types_capty_t), {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Definition Types_capty_t_eq (x y: Types_capty_t) : bool :=
  if Types_capty_t_eq_dec x y then true else false.

Definition Types_capty_t_neq (x y: Types_capty_t) : bool :=
  negb (Types_capty_t_eq x y).

Lemma Syscall_syscall_eq_dec :
  forall (x y: Syscall_syscall), {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Definition Syscall_syscall_eq (x y: Syscall_syscall) : bool :=
  if Syscall_syscall_eq_dec x y then true else false.

Definition Syscall_syscall_neq (x y: Syscall_syscall) : bool :=
  negb (Syscall_syscall_eq x y).

Definition Types_reg_t_to_Z (e: Types_reg_t) : Z :=
  match e with
  | Types_Reg_pc => 0
  | Types_Reg_ra => 1
  | Types_Reg_sp => 2
  | Types_Reg_gp => 3
  | Types_Reg_tp => 4
  | Types_Reg_a0 => 5
  | Types_Reg_a1 => 6
  | Types_Reg_a2 => 7
  | Types_Reg_a3 => 8
  | Types_Reg_a4 => 9
  | Types_Reg_a5 => 10
  | Types_Reg_a6 => 11
  | Types_Reg_a7 => 12
  | Types_Reg_t0 => 13
  | Types_Reg_t1 => 14
  | Types_Reg_t2 => 15
  | Types_Reg_t3 => 16
  | Types_Reg_t4 => 17
  | Types_Reg_t5 => 18
  | Types_Reg_t6 => 19
  | Types_Reg_s0 => 20
  | Types_Reg_s1 => 21
  | Types_Reg_s2 => 22
  | Types_Reg_s3 => 23
  | Types_Reg_s4 => 24
  | Types_Reg_s5 => 25
  | Types_Reg_s6 => 26
  | Types_Reg_s7 => 27
  | Types_Reg_s8 => 28
  | Types_Reg_s9 => 29
  | Types_Reg_s10 => 30
  | Types_Reg_s11 => 31
  end.

Definition Types_capty_t_to_Z (e: Types_capty_t) : Z :=
  match e with
  | Types_Capty_NONE => 0
  | Types_Capty_MEM => 1
  | Types_Capty_TSL => 2
  | Types_Capty_MON => 3
  | Types_Capty_IPC => 4
  | Types_Capty_INVALID => 5
  end.

Definition Syscall_syscall_to_Z (e: Syscall_syscall) : Z :=
  match e with
  | Syscall_Syscall_pid_get => 0
  | Syscall_Syscall_vreg_get => 1
  | Syscall_Syscall_vreg_set => 2
  | Syscall_Syscall_sync => 3
  | Syscall_Syscall_sleep_until => 4
  | Syscall_Syscall_mem_introspect => 5
  | Syscall_Syscall_tsl_introspect => 6
  | Syscall_Syscall_mon_introspect => 7
  | Syscall_Syscall_ipc_introspect => 8
  | Syscall_Syscall_mem_derive => 9
  | Syscall_Syscall_tsl_derive => 10
  | Syscall_Syscall_mon_derive => 11
  | Syscall_Syscall_ipc_derive => 12
  | Syscall_Syscall_mem_revoke => 13
  | Syscall_Syscall_tsl_revoke => 14
  | Syscall_Syscall_mon_revoke => 15
  | Syscall_Syscall_ipc_revoke => 16
  | Syscall_Syscall_mem_delete => 17
  | Syscall_Syscall_tsl_delete => 18
  | Syscall_Syscall_mon_delete => 19
  | Syscall_Syscall_ipc_delete => 20
  | Syscall_Syscall_mem_pmp_get => 21
  | Syscall_Syscall_mem_pmp_set => 22
  | Syscall_Syscall_mem_pmp_clear => 23
  | Syscall_Syscall_tsl_set => 24
  | Syscall_Syscall_mon_suspend => 25
  | Syscall_Syscall_mon_resume => 26
  | Syscall_Syscall_mon_yield => 27
  | Syscall_Syscall_mon_reg_get => 28
  | Syscall_Syscall_mon_reg_set => 29
  | Syscall_Syscall_mon_vreg_get => 30
  | Syscall_Syscall_mon_vreg_set => 31
  | Syscall_Syscall_mon_mem_introspect => 32
  | Syscall_Syscall_mon_tsl_introspect => 33
  | Syscall_Syscall_mon_mon_introspect => 34
  | Syscall_Syscall_mon_ipc_introspect => 35
  | Syscall_Syscall_mon_mem_grant => 36
  | Syscall_Syscall_mon_tsl_grant => 37
  | Syscall_Syscall_mon_mon_grant => 38
  | Syscall_Syscall_mon_ipc_grant => 39
  | Syscall_Syscall_mon_mem_derive => 40
  | Syscall_Syscall_mon_tsl_derive => 41
  | Syscall_Syscall_mon_mon_derive => 42
  | Syscall_Syscall_mon_ipc_derive => 43
  | Syscall_Syscall_mon_mem_pmp_get => 44
  | Syscall_Syscall_mon_mem_pmp_set => 45
  | Syscall_Syscall_mon_mem_pmp_clear => 46
  | Syscall_Syscall_mon_tsl_set => 47
  | Syscall_Syscall_ipc_send => 48
  | Syscall_Syscall_ipc_recv => 49
  | Syscall_Syscall_ipc_call => 50
  | Syscall_Syscall_ipc_reply => 51
  | Syscall_Syscall_ipc_replyrecv => 52
  | Syscall_Syscall_ipc_asend => 53
  | Syscall_Syscall_ipc_arecv => 54
  | Syscall_Syscall_max => 55
  end.

Definition Types_reg_t_of_Z (z: Z) : option Types_reg_t :=
  cast_enum [
    Types_Reg_pc;
    Types_Reg_ra;
    Types_Reg_sp;
    Types_Reg_gp;
    Types_Reg_tp;
    Types_Reg_a0;
    Types_Reg_a1;
    Types_Reg_a2;
    Types_Reg_a3;
    Types_Reg_a4;
    Types_Reg_a5;
    Types_Reg_a6;
    Types_Reg_a7;
    Types_Reg_t0;
    Types_Reg_t1;
    Types_Reg_t2;
    Types_Reg_t3;
    Types_Reg_t4;
    Types_Reg_t5;
    Types_Reg_t6;
    Types_Reg_s0;
    Types_Reg_s1;
    Types_Reg_s2;
    Types_Reg_s3;
    Types_Reg_s4;
    Types_Reg_s5;
    Types_Reg_s6;
    Types_Reg_s7;
    Types_Reg_s8;
    Types_Reg_s9;
    Types_Reg_s10;
    Types_Reg_s11
  ] z.

Definition Types_capty_t_of_Z (z: Z) : option Types_capty_t :=
  cast_enum [
    Types_Capty_NONE;
    Types_Capty_MEM;
    Types_Capty_TSL;
    Types_Capty_MON;
    Types_Capty_IPC;
    Types_Capty_INVALID
  ] z.

Definition Syscall_syscall_of_Z (z: Z) : option Syscall_syscall :=
  cast_enum [
    Syscall_Syscall_pid_get;
    Syscall_Syscall_vreg_get;
    Syscall_Syscall_vreg_set;
    Syscall_Syscall_sync;
    Syscall_Syscall_sleep_until;
    Syscall_Syscall_mem_introspect;
    Syscall_Syscall_tsl_introspect;
    Syscall_Syscall_mon_introspect;
    Syscall_Syscall_ipc_introspect;
    Syscall_Syscall_mem_derive;
    Syscall_Syscall_tsl_derive;
    Syscall_Syscall_mon_derive;
    Syscall_Syscall_ipc_derive;
    Syscall_Syscall_mem_revoke;
    Syscall_Syscall_tsl_revoke;
    Syscall_Syscall_mon_revoke;
    Syscall_Syscall_ipc_revoke;
    Syscall_Syscall_mem_delete;
    Syscall_Syscall_tsl_delete;
    Syscall_Syscall_mon_delete;
    Syscall_Syscall_ipc_delete;
    Syscall_Syscall_mem_pmp_get;
    Syscall_Syscall_mem_pmp_set;
    Syscall_Syscall_mem_pmp_clear;
    Syscall_Syscall_tsl_set;
    Syscall_Syscall_mon_suspend;
    Syscall_Syscall_mon_resume;
    Syscall_Syscall_mon_yield;
    Syscall_Syscall_mon_reg_get;
    Syscall_Syscall_mon_reg_set;
    Syscall_Syscall_mon_vreg_get;
    Syscall_Syscall_mon_vreg_set;
    Syscall_Syscall_mon_mem_introspect;
    Syscall_Syscall_mon_tsl_introspect;
    Syscall_Syscall_mon_mon_introspect;
    Syscall_Syscall_mon_ipc_introspect;
    Syscall_Syscall_mon_mem_grant;
    Syscall_Syscall_mon_tsl_grant;
    Syscall_Syscall_mon_mon_grant;
    Syscall_Syscall_mon_ipc_grant;
    Syscall_Syscall_mon_mem_derive;
    Syscall_Syscall_mon_tsl_derive;
    Syscall_Syscall_mon_mon_derive;
    Syscall_Syscall_mon_ipc_derive;
    Syscall_Syscall_mon_mem_pmp_get;
    Syscall_Syscall_mon_mem_pmp_set;
    Syscall_Syscall_mon_mem_pmp_clear;
    Syscall_Syscall_mon_tsl_set;
    Syscall_Syscall_ipc_send;
    Syscall_Syscall_ipc_recv;
    Syscall_Syscall_ipc_call;
    Syscall_Syscall_ipc_reply;
    Syscall_Syscall_ipc_replyrecv;
    Syscall_Syscall_ipc_asend;
    Syscall_Syscall_ipc_arecv;
    Syscall_Syscall_max
  ] z.

Definition neqb (b1 b2: bool) := negb (eqb b1 b2).

(** * Program *)

Parameter Kernel_ks : Types_kstate.

Parameter Machine_sched_split : u64 -> u64 -> u64 -> u64 -> u64 -> option u64.

Parameter Machine_sched_set_pid : u64 -> u64 -> u64 -> option u64.

Parameter Machine_lock_acquire : bool -> option bool.

Parameter Machine_lock_release : unit -> option u64.

Parameter Machine_rtc_get_time : unit -> option u64.

Parameter Machine_mem_transfer : Types_kstate -> u64 -> u64 -> u64 -> option Types_kstate.

Parameter Machine_mem_valid_access : u64 -> u64 -> option bool.

Parameter Syscall_delegate : Types_kstate -> option Types_kstate.

Definition Platform_num_harts : u64 := 1UL.

Definition Platform_rtchz : u64 := 10000000UL.

Definition Config_ticks_per_us : u64 := 10UL.

Definition Config_uint64_max : u64 := 18446744073709551615UL.

Definition Config_max_pid : u64 := 4UL.

Definition Config_max_time_fuel : u64 := 32UL.

Definition Config_tsl_table_size : u64 := 32UL.

Definition Config_max_mon_fuel : u64 := 8UL.

Definition Config_mon_table_size : u64 := 32UL.

Definition Config_max_ipc_fuel : u64 := 16UL.

Definition Config_ipc_table_size : u64 := 16UL.

Definition Error_success : i64 := 0L.

Definition Error_invalid_access : i64 := (-1)L.

Definition Error_invalid_argument : i64 := (-2)L.

Definition Error_invalid_state : i64 := (-3)L.

Definition Error_slot_in_use : i64 := (-4)L.

Definition Error_timeout : i64 := (-5)L.

Definition Error_continue : i64 := 1L.

Definition Types_invalid_pid : u64 := 0UL.

Definition Types_ipc_MODE_NONE : u32 := 0U.

Definition Types_ipc_MODE_USYNC : u32 := 1U.

Definition Types_ipc_MODE_BSYNC : u32 := 2U.

Definition Types_ipc_MODE_ASYNC : u32 := 3U.

Definition Types_ipc_MODE_MASK : u32 := 3U.

Definition Types_ipc_MODE_REVOKE : u32 := 4U.

Definition Types_ipc_FLAG_YIELD : u32 := 1U.

Definition Types_ipc_FLAG_TSL : u32 := 2U.

Definition Types_ipc_FLAG_MEM : u32 := 4U.

Definition Types_ipc_FLAG_MON : u32 := 8U.

Definition Types_ipc_FLAG_IPC : u32 := 16U.

Definition Types_ipc_FLAG_MASK : u32 := 31U.

Definition Proc_set_reg (ks: Types_kstate) (pid: u64) (regid: Types_reg_t) (value: u64) : option Types_kstate :=
  let pid := pid -₆₄ 1UL in
  let procs := ks.(types_kstate_procs) in
  let* proc := procs.[pid] in
  let* regs := proc.(types_proc_t_regs).[(U64.of_Z (Types_reg_t_to_Z regid)) <- value] in
  let proc := proc <| types_proc_t_regs := regs |> in
  let* procs := procs.[pid <- proc] in
  ret (ks <| types_kstate_procs := procs |>).

Definition Proc_get_reg (ks: Types_kstate) (pid: u64) (regid: Types_reg_t) : option u64 :=
  let* b1 := ks.(types_kstate_procs).[(pid -₆₄ 1UL)] in
  b1.(types_proc_t_regs).[(U64.of_Z (Types_reg_t_to_Z regid))].

Definition Proc_set_timeout (ks: Types_kstate) (pid: u64) (timeout: u64) : option Types_kstate :=
  let pid := pid -₆₄ 1UL in
  let procs := ks.(types_kstate_procs) in
  let* proc :=
    let* b1 := procs.[pid] in
    ret (b1 <| types_proc_t_timeout := timeout |>)
  in
  let* procs := procs.[pid <- proc] in
  ret (ks <| types_kstate_procs := procs |>).

Definition Proc_get_timeout (ks: Types_kstate) (pid: u64) : option u64 :=
  let* b1 := ks.(types_kstate_procs).[(pid -₆₄ 1UL)] in
  ret b1.(types_proc_t_timeout).

Definition Proc_get_state (ks: Types_kstate) (pid: u64) : option u64 :=
  let* b1 := ks.(types_kstate_procs).[(pid -₆₄ 1UL)] in
  ret b1.(types_proc_t_state).

Definition Proc_set_state (ks: Types_kstate) (pid: u64) (state: u64) : option Types_kstate :=
  let pid := pid -₆₄ 1UL in
  let procs := ks.(types_kstate_procs) in
  let* proc :=
    let* b1 := procs.[pid] in
    ret (b1 <| types_proc_t_state := state |>)
  in
  let* procs := procs.[pid <- proc] in
  ret (ks <| types_kstate_procs := procs |>).

Definition Proc_proc_STATE_READY : u64 := 0UL.

Definition Proc_proc_STATE_ACQUIRED : u64 := 1UL.

Definition Proc_proc_STATE_BLOCKED : u64 := 2UL.

Definition Proc_proc_STATE_SUSPENDED : u64 := 4UL.

Definition Proc_ipc_can_acquire (ks: Types_kstate) (pid: u64) (i: u64) : option bool :=
  let* b1 := Proc_get_state ks pid in
  ret (Int64.eq b1 (Proc_proc_STATE_BLOCKED |₆₄ (i <<₆₄ 4UL))).

Definition Proc_ipc_acquire (ks: Types_kstate) (pid: u64) : option Types_kstate :=
  Proc_set_state ks pid Proc_proc_STATE_ACQUIRED.

Definition Proc_ipc_block (ks: Types_kstate) (pid: u64) (i: u64) : option Types_kstate :=
  let* b1 := Proc_get_state ks pid in
  if (Int64.cmpu Cne b1 Proc_proc_STATE_ACQUIRED) then
    ret ks
  else
    Proc_set_state ks pid ((Proc_proc_STATE_BLOCKED |₆₄ Proc_proc_STATE_ACQUIRED) |₆₄ (i <<₆₄ 4UL)).

Definition Proc_release (ks: Types_kstate) (pid: u64) : option Types_kstate :=
  let* state := Proc_get_state ks pid in
  Proc_set_state ks pid (state &₆₄ (Int64.not Proc_proc_STATE_ACQUIRED)).

Definition Exception_handle_mret (proc: Types_proc_t) : option Types_proc_t :=
  let trap := proc.(types_proc_t_trap) in
  let regs := proc.(types_proc_t_regs) in
  let* regs := regs.[(U64.of_Z (Types_reg_t_to_Z Types_Reg_pc)) <- trap.(types_trap_t_epc)] in
  let* regs := regs.[(U64.of_Z (Types_reg_t_to_Z Types_Reg_sp)) <- trap.(types_trap_t_esp)] in
  let proc := proc <| types_proc_t_regs := regs |> in
  let trap := (((trap <| types_trap_t_ecause := 0UL |>) <| types_trap_t_eval := 0UL |>) <| types_trap_t_epc := 0UL |>) <| types_trap_t_esp := 0UL |> in
  ret (proc <| types_proc_t_trap := trap |>).

Definition Exception_handle_delegate (proc: Types_proc_t) (cause: u64) (tval: u64) : option Types_proc_t :=
  let* trap :=
    let* b1 := proc.(types_proc_t_regs).[(U64.of_Z (Types_reg_t_to_Z Types_Reg_pc))] in
    let* b2 := proc.(types_proc_t_regs).[(U64.of_Z (Types_reg_t_to_Z Types_Reg_sp))] in
    ret ((((proc.(types_proc_t_trap) <| types_trap_t_ecause := cause |>) <| types_trap_t_eval := tval |>) <| types_trap_t_epc := b1 |>) <| types_trap_t_esp := b2 |>)
  in
  let proc := proc <| types_proc_t_trap := trap |> in
  let regs := proc.(types_proc_t_regs) in
  let* regs := regs.[(U64.of_Z (Types_reg_t_to_Z Types_Reg_pc)) <- trap.(types_trap_t_tpc)] in
  let* regs := regs.[(U64.of_Z (Types_reg_t_to_Z Types_Reg_sp)) <- trap.(types_trap_t_tsp)] in
  ret (proc <| types_proc_t_regs := regs |>).

Definition Exception_illegal_instruction : u64 := 2UL.

Definition Exception_mret : u64 := 807403635UL.

Definition Exception_handler (ks: Types_kstate) (cause: u64) (tval: u64) : option Types_kstate :=
  let procs := ks.(types_kstate_procs) in
  let i := ks.(types_kstate_active_pid) -₆₄ 1UL in
  let* proc := procs.[i] in
  let* proc :=
    if ((Int64.eq cause Exception_illegal_instruction) && (Int64.eq tval Exception_mret)) then
      Exception_handle_mret proc
    else
      Exception_handle_delegate proc cause tval
  in
  let* procs := procs.[i <- proc] in
  ret (ks <| types_kstate_procs := procs |>).

Definition Tsl_valid_access (ks: Types_kstate) (owner: u64) (i: u64) : option bool :=
  if (Int64.ltu i Config_tsl_table_size) then
    let* b1 := ks.(types_kstate_tsl_table).[i] in
    ret (Int64.eq b1.(types_tsl_t_owner) owner)
  else
    ret false.

Definition Tsl_not_derivable (parent: Types_tsl_t) (csize: u64) (size: u64) : bool :=
  (((Int64.cmpu Cle parent.(types_tsl_t_cfree) csize) || (Int64.cmpu Cgt size parent.(types_tsl_t_free))) || (Int64.eq csize 0UL)) || (Int64.eq size 0UL).

Definition Tsl_delete (ks: Types_kstate) (owner: u64) (i: u64) : option Types_kstate :=
  let* b1 := Tsl_valid_access ks owner i in
  if b1 then
    let tsl_table := ks.(types_kstate_tsl_table) in
    let* cap :=
      let* b2 := tsl_table.[i] in
      ret (b2 <| types_tsl_t_owner := 0UL |>)
    in
    let* dummy :=
      if (Int64.cmpu Cgt cap.(types_tsl_t_free) 0UL) then
        Machine_sched_set_pid cap.(types_tsl_t_hart) 0UL cap.(types_tsl_t_base)
      else
        ret 0UL
    in
    let* tsl_table := tsl_table.[i <- cap] in
    let ks := ks <| types_kstate_tsl_table := tsl_table |> in
    ret (ks <| types_kstate_errcode := Error_success |>)
  else
    ret (ks <| types_kstate_errcode := Error_invalid_access |>).

Definition Tsl_derive (ks: Types_kstate) (owner: u64) (i: u64) (target: u64) (csize: u64) (enable: bool) (size: u64) : option Types_kstate :=
  let* b1 := Tsl_valid_access ks owner i in
  if b1 then
    let tsl_table := ks.(types_kstate_tsl_table) in
    let* cap_i := tsl_table.[i] in
    if (Tsl_not_derivable cap_i csize size) then
      ret (ks <| types_kstate_errcode := Error_invalid_argument |>)
    else
      let cap_i := (cap_i <| types_tsl_t_cfree := cap_i.(types_tsl_t_cfree) -₆₄ csize |>) <| types_tsl_t_free := cap_i.(types_tsl_t_free) -₆₄ size |> in
      let j := i +₆₄ cap_i.(types_tsl_t_cfree) in
      let base := cap_i.(types_tsl_t_base) +₆₄ cap_i.(types_tsl_t_free) in
      let hart := cap_i.(types_tsl_t_hart) in
      let* tsl_table := tsl_table.[i <- cap_i] in
      let* cap_j :=
        let* b2 := tsl_table.[j] in
        ret ((((((((b2 <| types_tsl_t_owner := target |>) <| types_tsl_t_cfree := csize |>) <| types_tsl_t_csize := csize |>) <| types_tsl_t_hart := hart |>) <| types_tsl_t_enabled := enable |>) <| types_tsl_t_base := base |>) <| types_tsl_t_size := size |>) <| types_tsl_t_free := size |>)
      in
      let* tsl_table := tsl_table.[j <- cap_j] in
      let sched_pid :=
        if enable then
          target
        else
          0UL
      in
      let* cap_i := tsl_table.[i] in
      let* dummy := Machine_sched_split cap_i.(types_tsl_t_hart) sched_pid cap_i.(types_tsl_t_base) base (base +₆₄ size) in
      let ks := ks <| types_kstate_tsl_table := tsl_table |> in
      ret (ks <| types_kstate_errcode := I64.of_u64 j |>)
  else
    ret (ks <| types_kstate_errcode := Error_invalid_access |>).

Definition Tsl_set (ks: Types_kstate) (owner: u64) (i: u64) (enable: bool) : option Types_kstate :=
  let* b1 := Tsl_valid_access ks owner i in
  if b1 then
    let tsl_table := ks.(types_kstate_tsl_table) in
    let* cap :=
      let* b2 := tsl_table.[i] in
      ret (b2 <| types_tsl_t_enabled := enable |>)
    in
    let* dummy :=
      if (Int64.cmpu Cgt cap.(types_tsl_t_free) 0UL) then
        let sched_pid :=
          if enable then
            owner
          else
            0UL
        in
        Machine_sched_set_pid cap.(types_tsl_t_hart) sched_pid cap.(types_tsl_t_base)
      else
        ret 0UL
    in
    let* tsl_table := tsl_table.[i <- cap] in
    let ks := ks <| types_kstate_tsl_table := tsl_table |> in
    ret (ks <| types_kstate_errcode := Error_success |>)
  else
    ret (ks <| types_kstate_errcode := Error_invalid_access |>).

Definition Tsl_transfer (ks: Types_kstate) (owner: u64) (i: u64) (new_owner: u64) : option Types_kstate :=
  let* b1 := Tsl_valid_access ks owner i in
  if b1 then
    let tsl_table := ks.(types_kstate_tsl_table) in
    let* cap :=
      let* b2 := tsl_table.[i] in
      ret (b2 <| types_tsl_t_owner := new_owner |>)
    in
    let* dummy :=
      if (Int64.cmpu Cgt cap.(types_tsl_t_free) 0UL) then
        let sched_pid :=
          if cap.(types_tsl_t_enabled) then
            new_owner
          else
            0UL
        in
        Machine_sched_set_pid cap.(types_tsl_t_hart) sched_pid cap.(types_tsl_t_base)
      else
        ret 0UL
    in
    let* tsl_table := tsl_table.[i <- cap] in
    let ks := ks <| types_kstate_tsl_table := tsl_table |> in
    ret (ks <| types_kstate_errcode := Error_success |>)
  else
    ret (ks <| types_kstate_errcode := Error_invalid_access |>).

Definition Tsl_revoke_once (ks: Types_kstate) (i: u64) : option Types_kstate :=
  let tsl_table := ks.(types_kstate_tsl_table) in
  let* b1 := tsl_table.[i] in
  let* b2 := tsl_table.[i] in
  if (Int64.ltu b1.(types_tsl_t_cfree) b2.(types_tsl_t_csize)) then
    let* j :=
      let* b3 := tsl_table.[i] in
      ret (i +₆₄ b3.(types_tsl_t_cfree))
    in
    let* cap_j := tsl_table.[j] in
    let j_cfree := cap_j.(types_tsl_t_cfree) in
    let j_free := cap_j.(types_tsl_t_free) in
    let cap_j := (cap_j <| types_tsl_t_owner := 0UL |>) <| types_tsl_t_cfree := 0UL |> in
    let* tsl_table := tsl_table.[j <- cap_j] in
    let* cap_i := tsl_table.[i] in
    let cap_i := (cap_i <| types_tsl_t_cfree := cap_i.(types_tsl_t_cfree) +₆₄ j_cfree |>) <| types_tsl_t_free := cap_i.(types_tsl_t_free) +₆₄ j_free |> in
    let errcode := cap_i.(types_tsl_t_csize) -₆₄ cap_i.(types_tsl_t_cfree) in
    let* tsl_table := tsl_table.[i <- cap_i] in
    ret ((ks <| types_kstate_tsl_table := tsl_table |>) <| types_kstate_errcode := I64.of_u64 errcode |>)
  else
    ret (ks <| types_kstate_errcode := Error_success |>).

Definition Tsl_revoke (ks: Types_kstate) (owner: u64) (i: u64) : option Types_kstate :=
  let* b1 := Tsl_valid_access ks owner i in
  if b1 then
    Tsl_revoke_once ks i
  else
    ret (ks <| types_kstate_errcode := Error_invalid_access |>).

Definition Mon_valid_access (ks: Types_kstate) (owner: u64) (i: u64) : option bool :=
  if (Int64.ltu i Config_mon_table_size) then
    let* b1 := ks.(types_kstate_mon_table).[i] in
    ret (Int64.eq b1.(types_mon_t_owner) owner)
  else
    ret false.

Definition Mon_get_pid (ks: Types_kstate) (owner: u64) (i: u64) : option u64 :=
  let* b1 := Mon_valid_access ks owner i in
  if b1 then
    let* b2 := ks.(types_kstate_mon_table).[i] in
    ret b2.(types_mon_t_pid)
  else
    ret 0UL.

Definition Mon_delete (ks: Types_kstate) (owner: u64) (i: u64) : option Types_kstate :=
  let* b1 := Mon_valid_access ks owner i in
  if b1 then
    let mon_table := ks.(types_kstate_mon_table) in
    let* cap :=
      let* b2 := mon_table.[i] in
      ret (b2 <| types_mon_t_owner := 0UL |>)
    in
    let* mon_table := mon_table.[i <- cap] in
    let ks := ks <| types_kstate_mon_table := mon_table |> in
    ret (ks <| types_kstate_errcode := Error_success |>)
  else
    ret (ks <| types_kstate_errcode := Error_invalid_access |>).

Definition Mon_derive (ks: Types_kstate) (owner: u64) (i: u64) (target: u64) (csize: u64) : option Types_kstate :=
  let* b1 := Mon_valid_access ks owner i in
  if b1 then
    let mon_table := ks.(types_kstate_mon_table) in
    let* cap_i := mon_table.[i] in
    if ((Int64.eq csize 0UL) || (Int64.cmpu Cle cap_i.(types_mon_t_cfree) csize)) then
      ret (ks <| types_kstate_errcode := Error_invalid_argument |>)
    else
      let cap_i := cap_i <| types_mon_t_cfree := cap_i.(types_mon_t_cfree) -₆₄ csize |> in
      let j := i +₆₄ cap_i.(types_mon_t_cfree) in
      let pid := cap_i.(types_mon_t_pid) in
      let* mon_table := mon_table.[i <- cap_i] in
      let* cap_j :=
        let* b2 := mon_table.[j] in
        ret ((((b2 <| types_mon_t_owner := target |>) <| types_mon_t_cfree := csize |>) <| types_mon_t_csize := csize |>) <| types_mon_t_pid := pid |>)
      in
      let* mon_table := mon_table.[j <- cap_j] in
      let ks := ks <| types_kstate_mon_table := mon_table |> in
      ret (ks <| types_kstate_errcode := I64.of_u64 j |>)
  else
    ret (ks <| types_kstate_errcode := Error_invalid_access |>).

Definition Mon_transfer (ks: Types_kstate) (owner: u64) (i: u64) (new_owner: u64) : option Types_kstate :=
  let* b1 := Mon_valid_access ks owner i in
  if b1 then
    let mon_table := ks.(types_kstate_mon_table) in
    let* cap :=
      let* b2 := mon_table.[i] in
      ret (b2 <| types_mon_t_owner := new_owner |>)
    in
    let* mon_table := mon_table.[i <- cap] in
    let ks := ks <| types_kstate_mon_table := mon_table |> in
    ret (ks <| types_kstate_errcode := Error_success |>)
  else
    ret (ks <| types_kstate_errcode := Error_invalid_access |>).

Definition Mon_revoke_once (ks: Types_kstate) (i: u64) : option Types_kstate :=
  let mon_table := ks.(types_kstate_mon_table) in
  let* b1 := mon_table.[i] in
  let* b2 := mon_table.[i] in
  if (Int64.ltu b1.(types_mon_t_cfree) b2.(types_mon_t_csize)) then
    let* j :=
      let* b3 := mon_table.[i] in
      ret (i +₆₄ b3.(types_mon_t_cfree))
    in
    let* cap_j := mon_table.[j] in
    let j_cfree := cap_j.(types_mon_t_cfree) in
    let cap_j := (cap_j <| types_mon_t_owner := 0UL |>) <| types_mon_t_cfree := 0UL |> in
    let* mon_table := mon_table.[j <- cap_j] in
    let* cap_i := mon_table.[i] in
    let cap_i := cap_i <| types_mon_t_cfree := cap_i.(types_mon_t_cfree) +₆₄ j_cfree |> in
    let errcode := cap_i.(types_mon_t_csize) -₆₄ cap_i.(types_mon_t_cfree) in
    let* mon_table := mon_table.[i <- cap_i] in
    ret ((ks <| types_kstate_mon_table := mon_table |>) <| types_kstate_errcode := I64.of_u64 errcode |>)
  else
    ret (ks <| types_kstate_errcode := Error_success |>).

Definition Mon_revoke (ks: Types_kstate) (owner: u64) (i: u64) : option Types_kstate :=
  let* b1 := Mon_valid_access ks owner i in
  if b1 then
    Mon_revoke_once ks i
  else
    ret (ks <| types_kstate_errcode := Error_invalid_access |>).

Definition Ipc_valid_access (ks: Types_kstate) (owner: u64) (i: u64) : option bool :=
  if (Int64.ltu i Config_ipc_table_size) then
    let* b1 := ks.(types_kstate_ipc_table).[i] in
    ret (Int64.eq b1.(types_ipc_t_owner) owner)
  else
    ret false.

Definition Ipc_valid_derivation (cap: Types_ipc_t) (csize: u64) (mode: u32) (flag: u32) : bool :=
  if ((Int64.cmpu Cge csize cap.(types_ipc_t_cfree)) && (Int64.cmpu Cgt csize 0UL)) then
    false
  else if (Int.cmpu Cne (cap.(types_ipc_t_mode) &₃₂ Types_ipc_MODE_REVOKE) 0U) then
    false
  else if (Int.eq cap.(types_ipc_t_mode) Types_ipc_MODE_NONE) then
    (Int.cmpu Cne mode Types_ipc_MODE_NONE) || (Int.eq flag 0U)
  else
    ((Int.eq cap.(types_ipc_t_mode) mode) && (Int.eq cap.(types_ipc_t_flag) flag)) && (Int64.eq csize 1UL).

Definition Ipc_valid_capability_send (ks: Types_kstate) (owner: u64) (i: u64) (capty: u64) (flag: u32) : option bool :=
  let* b1 := Types_capty_t_of_Z (U64.to_Z capty) in
  match b1 with
  | Types_Capty_NONE =>
      ret true
  | Types_Capty_MEM =>
      let* b2 := Machine_mem_valid_access owner i in
      ret ((U32.to_bool (flag &₃₂ Types_ipc_FLAG_MEM)) && b2)
  | Types_Capty_TSL =>
      let* b3 := Tsl_valid_access ks owner i in
      ret ((U32.to_bool (flag &₃₂ Types_ipc_FLAG_TSL)) && b3)
  | Types_Capty_MON =>
      let* b4 := Mon_valid_access ks owner i in
      ret ((U32.to_bool (flag &₃₂ Types_ipc_FLAG_MON)) && b4)
  | Types_Capty_IPC =>
      let* b5 := Ipc_valid_access ks owner i in
      ret ((U32.to_bool (flag &₃₂ Types_ipc_FLAG_IPC)) && b5)
  | _ =>
      ret false
  end.

Definition Ipc_invoke_valid_access (ks: Types_kstate) (owner: u64) (i: u64) (mode: u32) (sink: bool) : option bool :=
  let* b1 := Ipc_valid_access ks owner i in
  if (negb b1) then
    ret false
  else
    let* b2 := ks.(types_kstate_ipc_table).[i] in
    if (Int.cmpu Cne b2.(types_ipc_t_mode) mode) then
      ret false
    else if sink then
      let* b3 := ks.(types_kstate_ipc_table).[i] in
      ret (Int64.eq b3.(types_ipc_t_sink) i)
    else
      let* b4 := ks.(types_kstate_ipc_table).[i] in
      ret (Int64.cmpu Cne b4.(types_ipc_t_sink) i).

Definition Ipc_delete (ks: Types_kstate) (owner: u64) (i: u64) : option Types_kstate :=
  let* b1 := Ipc_valid_access ks owner i in
  if b1 then
    let ipc_table := ks.(types_kstate_ipc_table) in
    let* cap :=
      let* b2 := ipc_table.[i] in
      ret (b2 <| types_ipc_t_owner := 0UL |>)
    in
    let* ipc_table := ipc_table.[i <- cap] in
    let ks := ks <| types_kstate_ipc_table := ipc_table |> in
    ret (ks <| types_kstate_errcode := Error_success |>)
  else
    ret (ks <| types_kstate_errcode := Error_invalid_access |>).

Definition Ipc_derive (ks: Types_kstate) (owner: u64) (i: u64) (target: u64) (csize: u64) (mode: u32) (flag: u32) : option Types_kstate :=
  let* b1 := Ipc_valid_access ks owner i in
  if b1 then
    let mode := mode &₃₂ Types_ipc_MODE_MASK in
    let flag := flag &₃₂ Types_ipc_FLAG_MASK in
    let ipc_table := ks.(types_kstate_ipc_table) in
    let* cap_i := ipc_table.[i] in
    if (negb (Ipc_valid_derivation cap_i csize mode flag)) then
      ret (ks <| types_kstate_errcode := Error_invalid_argument |>)
    else
      let cap_i := cap_i <| types_ipc_t_cfree := cap_i.(types_ipc_t_cfree) -₆₄ csize |> in
      let j := i +₆₄ cap_i.(types_ipc_t_cfree) in
      let sink_j :=
        if (Int.eq cap_i.(types_ipc_t_mode) Types_ipc_MODE_NONE) then
          j
        else
          cap_i.(types_ipc_t_sink)
      in
      let* ipc_table := ipc_table.[i <- cap_i] in
      let* cap_j :=
        let* b2 := ipc_table.[j] in
        ret ((((((((b2 <| types_ipc_t_owner := target |>) <| types_ipc_t_cfree := csize |>) <| types_ipc_t_csize := csize |>) <| types_ipc_t_mode := mode |>) <| types_ipc_t_flag := flag |>) <| types_ipc_t_sink := sink_j |>) <| types_ipc_t_source := j |>) <| types_ipc_t_opt := 0U |>)
      in
      let* ipc_table := ipc_table.[j <- cap_j] in
      let ks := ks <| types_kstate_ipc_table := ipc_table |> in
      ret (ks <| types_kstate_errcode := I64.of_u64 j |>)
  else
    ret (ks <| types_kstate_errcode := Error_invalid_access |>).

Definition Ipc_transfer (ks: Types_kstate) (owner: u64) (i: u64) (new_owner: u64) : option Types_kstate :=
  let* b1 := Ipc_valid_access ks owner i in
  if b1 then
    let ipc_table := ks.(types_kstate_ipc_table) in
    let* cap :=
      let* b2 := ipc_table.[i] in
      ret (b2 <| types_ipc_t_owner := new_owner |>)
    in
    let* ipc_table := ipc_table.[i <- cap] in
    let ks := ks <| types_kstate_ipc_table := ipc_table |> in
    ret (ks <| types_kstate_errcode := Error_success |>)
  else
    ret (ks <| types_kstate_errcode := Error_invalid_access |>).

Definition Ipc_revoke_once (ks: Types_kstate) (i: u64) : option Types_kstate :=
  let ipc_table := ks.(types_kstate_ipc_table) in
  let* b1 := ipc_table.[i] in
  let* b2 := ipc_table.[i] in
  if (Int64.ltu b1.(types_ipc_t_cfree) b2.(types_ipc_t_csize)) then
    let* j :=
      let* b3 := ipc_table.[i] in
      ret (i +₆₄ b3.(types_ipc_t_cfree))
    in
    let* cap_j := ipc_table.[j] in
    let j_cfree := cap_j.(types_ipc_t_cfree) in
    let cap_j := (cap_j <| types_ipc_t_owner := 0UL |>) <| types_ipc_t_cfree := 0UL |> in
    let* ipc_table := ipc_table.[j <- cap_j] in
    let* cap_i := ipc_table.[i] in
    let cap_i := (cap_i <| types_ipc_t_cfree := cap_i.(types_ipc_t_cfree) +₆₄ j_cfree |>) <| types_ipc_t_mode := Types_ipc_MODE_REVOKE |> in
    let errcode := cap_i.(types_ipc_t_csize) -₆₄ cap_i.(types_ipc_t_cfree) in
    let cap_i :=
      if (Int64.eq errcode 0UL) then
        cap_i <| types_ipc_t_mode := Types_ipc_MODE_NONE |>
      else
        cap_i
    in
    let* ipc_table := ipc_table.[i <- cap_i] in
    ret ((ks <| types_kstate_ipc_table := ipc_table |>) <| types_kstate_errcode := I64.of_u64 errcode |>)
  else
    ret (ks <| types_kstate_errcode := Error_success |>).

Definition Ipc_revoke (ks: Types_kstate) (owner: u64) (i: u64) : option Types_kstate :=
  let* b1 := Ipc_valid_access ks owner i in
  if b1 then
    Ipc_revoke_once ks i
  else
    ret (ks <| types_kstate_errcode := Error_invalid_access |>).

Definition Ipc_do_send (ks: Types_kstate) (receiver: u64) (owner: u64) (capty: Types_capty_t) (i: u64) : option Types_kstate :=
  let* ks := Proc_set_reg ks receiver Types_Reg_a0 (U64.of_i64 Error_success) in
  let* ks :=
    let* b1 := ks.(types_kstate_message).[0UL] in
    Proc_set_reg ks receiver Types_Reg_a1 b1
  in
  let* ks :=
    let* b2 := ks.(types_kstate_message).[1UL] in
    Proc_set_reg ks receiver Types_Reg_a2 b2
  in
  let* ks := Proc_set_reg ks receiver Types_Reg_a3 (U64.of_Z (Types_capty_t_to_Z capty)) in
  let* ks :=
    let b3 :=
      if (Types_capty_t_eq capty Types_Capty_NONE) then
        0UL
      else
        i
    in
    Proc_set_reg ks receiver Types_Reg_a4 b3
  in
  match capty with
  | Types_Capty_NONE =>
      ret ks
  | Types_Capty_MEM =>
      Machine_mem_transfer ks owner i receiver
  | Types_Capty_TSL =>
      Tsl_transfer ks owner i receiver
  | Types_Capty_MON =>
      Mon_transfer ks owner i receiver
  | Types_Capty_IPC =>
      Ipc_transfer ks owner i receiver
  | _ =>
      ret ks
  end.

Definition Ipc_call (ks: Types_kstate) (owner: u64) (i: u64) (capty: u64) (j: u64) : option Types_kstate :=
  let* b1 := Ipc_invoke_valid_access ks owner i Types_ipc_MODE_BSYNC false in
  if (negb b1) then
    ret (ks <| types_kstate_errcode := Error_invalid_access |>)
  else
    let* b2 := ks.(types_kstate_ipc_table).[i] in
    let* b3 := Ipc_valid_capability_send ks owner j capty b2.(types_ipc_t_flag) in
    if (negb b3) then
      ret (ks <| types_kstate_errcode := Error_invalid_argument |>)
    else
      let* sink :=
        let* b4 := ks.(types_kstate_ipc_table).[i] in
        ret b4.(types_ipc_t_sink)
      in
      let* receiver :=
        let* b5 := ks.(types_kstate_ipc_table).[sink] in
        ret b5.(types_ipc_t_owner)
      in
      if (Int64.eq receiver Types_invalid_pid) then
        ret (ks <| types_kstate_errcode := Error_invalid_state |>)
      else
        let* servtime :=
          let* b6 := ks.(types_kstate_ipc_table).[sink] in
          ret b6.(types_ipc_t_opt)
        in
        let* is_yield :=
          let* b7 := ks.(types_kstate_ipc_table).[sink] in
          ret (Int.cmpu Cne (b7.(types_ipc_t_flag) &₃₂ Types_ipc_FLAG_YIELD) 0U)
        in
        let* is_timeout :=
          if is_yield then
            let* curr_time := Machine_rtc_get_time tt in
            let* timeout := Proc_get_timeout ks ks.(types_kstate_active_pid) in
            ret (Int64.cmpu Cge (curr_time +₆₄ ((U64.of_u32 servtime) *₆₄ Config_ticks_per_us)) timeout)
          else
            ret false
        in
        if is_timeout then
          ret (ks <| types_kstate_errcode := Error_invalid_state |>)
        else
          let* b8 := Proc_ipc_can_acquire ks receiver sink in
          if (negb b8) then
            ret (ks <| types_kstate_errcode := Error_invalid_state |>)
          else
            let* ks := Proc_ipc_acquire ks receiver in
            let* ks :=
              let* b9 := Types_capty_t_of_Z (U64.to_Z capty) in
              Ipc_do_send ks receiver owner b9 j
            in
            let ipc_table := ks.(types_kstate_ipc_table) in
            let* cap_sink :=
              let* b10 := ipc_table.[sink] in
              ret ((b10 <| types_ipc_t_source := i |>) <| types_ipc_t_opt := 0U |>)
            in
            let* ipc_table := ipc_table.[sink <- cap_sink] in
            let ks := ks <| types_kstate_ipc_table := ipc_table |> in
            let* ks := Proc_ipc_block ks owner i in
            let sender := ks.(types_kstate_active_pid) in
            let* ks :=
              let* b11 := ks.(types_kstate_ipc_table).[i] in
              if (U32.to_bool (b11.(types_ipc_t_flag) &₃₂ Types_ipc_FLAG_YIELD)) then
                let ks := ks <| types_kstate_active_pid := receiver |> in
                let* b12 := Proc_get_timeout ks sender in
                Proc_set_timeout ks ks.(types_kstate_active_pid) b12
              else
                let* ks := Proc_release ks receiver in
                Proc_set_timeout ks sender Config_uint64_max
            in
            ret (ks <| types_kstate_errcode := Error_timeout |>).

Definition Ipc_replyrecv (ks: Types_kstate) (owner: u64) (i: u64) (capty: u64) (j: u64) (servtime: u32) : option Types_kstate :=
  let* b1 := Ipc_invoke_valid_access ks owner i Types_ipc_MODE_BSYNC true in
  if (negb b1) then
    ret (ks <| types_kstate_errcode := Error_invalid_access |>)
  else
    let* b2 := ks.(types_kstate_ipc_table).[i] in
    let* b3 := Ipc_valid_capability_send ks owner j capty b2.(types_ipc_t_flag) in
    if (negb b3) then
      ret (ks <| types_kstate_errcode := Error_invalid_argument |>)
    else
      let sender := ks.(types_kstate_active_pid) in
      let ks := ks <| types_kstate_active_pid := Types_invalid_pid |> in
      let* source :=
        let* b4 := ks.(types_kstate_ipc_table).[i] in
        ret b4.(types_ipc_t_source)
      in
      let* receiver :=
        let* b5 := ks.(types_kstate_ipc_table).[source] in
        ret b5.(types_ipc_t_owner)
      in
      let* ks :=
        let* b6 := Proc_ipc_can_acquire ks receiver source in
        if (((Int64.cmpu Cne source i) && (Int64.cmpu Cne receiver Types_invalid_pid)) && b6) then
          let* ks := Proc_ipc_acquire ks receiver in
          let* ks :=
            let* b7 := Types_capty_t_of_Z (U64.to_Z capty) in
            Ipc_do_send ks receiver owner b7 j
          in
          let ipc_table := ks.(types_kstate_ipc_table) in
          let* cap_i :=
            let* b8 := ipc_table.[i] in
            ret (b8 <| types_ipc_t_source := i |>)
          in
          let* ipc_table := ipc_table.[i <- cap_i] in
          let ks := ks <| types_kstate_ipc_table := ipc_table |> in
          let* b9 := ks.(types_kstate_ipc_table).[i] in
          if (U32.to_bool (b9.(types_ipc_t_flag) &₃₂ Types_ipc_FLAG_YIELD)) then
            let ks := ks <| types_kstate_active_pid := receiver |> in
            let* b10 := Proc_get_timeout ks sender in
            Proc_set_timeout ks receiver b10
          else
            let* ks := Proc_release ks receiver in
            Proc_set_timeout ks receiver 0UL
        else
          ret ks
      in
      let* ks := Proc_ipc_block ks owner i in
      let ipc_table := ks.(types_kstate_ipc_table) in
      let* cap_i :=
        let* b11 := ipc_table.[i] in
        ret (b11 <| types_ipc_t_opt := servtime |>)
      in
      let* ipc_table := ipc_table.[i <- cap_i] in
      let ks := ks <| types_kstate_ipc_table := ipc_table |> in
      let* ks := Proc_set_timeout ks sender Config_uint64_max in
      ret (ks <| types_kstate_errcode := Error_success |>).

Definition Syscall_pid_get (ks: Types_kstate) (pid: u64) : Types_kstate :=
  ks <| types_kstate_errcode := I64.of_u64 pid |>.

Definition Syscall_set_message (ks: Types_kstate) (data0: u64) (data1: u64) : option Types_kstate :=
  let msg := ks.(types_kstate_message) in
  let* msg := msg.[0UL <- data0] in
  let* msg := msg.[1UL <- data1] in
  ret (ks <| types_kstate_message := msg |>).

Definition Syscall_mon_tsl_grant (ks: Types_kstate) (owner: u64) (i: u64) (j: u64) : option Types_kstate :=
  let* target := Mon_get_pid ks owner i in
  if (Int64.eq target 0UL) then
    ret (ks <| types_kstate_errcode := Error_invalid_access |>)
  else
    Tsl_transfer ks owner j target.

Definition Syscall_mon_mon_grant (ks: Types_kstate) (owner: u64) (i: u64) (j: u64) : option Types_kstate :=
  let* target := Mon_get_pid ks owner i in
  if (Int64.eq target 0UL) then
    ret (ks <| types_kstate_errcode := Error_invalid_access |>)
  else
    Mon_transfer ks owner j target.

Definition Syscall_mon_ipc_grant (ks: Types_kstate) (owner: u64) (i: u64) (j: u64) : option Types_kstate :=
  let* target := Mon_get_pid ks owner i in
  if (Int64.eq target 0UL) then
    ret (ks <| types_kstate_errcode := Error_invalid_access |>)
  else
    Ipc_transfer ks owner j target.

Definition Syscall_mon_tsl_derive (ks: Types_kstate) (owner: u64) (i: u64) (j: u64) (csize: u64) (enable: bool) (size: u64) : option Types_kstate :=
  let* target := Mon_get_pid ks owner i in
  if (Int64.eq target 0UL) then
    ret (ks <| types_kstate_errcode := Error_invalid_access |>)
  else
    Tsl_derive ks owner j target csize enable size.

Definition Syscall_mon_mon_derive (ks: Types_kstate) (owner: u64) (i: u64) (j: u64) (csize: u64) : option Types_kstate :=
  let* target := Mon_get_pid ks owner i in
  if (Int64.eq target 0UL) then
    ret (ks <| types_kstate_errcode := Error_invalid_access |>)
  else
    Mon_derive ks owner j target csize.

Definition Syscall_mon_ipc_derive (ks: Types_kstate) (owner: u64) (i: u64) (j: u64) (csize: u64) (mode: u32) (flag: u32) : option Types_kstate :=
  let* target := Mon_get_pid ks owner i in
  if (Int64.eq target 0UL) then
    ret (ks <| types_kstate_errcode := Error_invalid_access |>)
  else
    Ipc_derive ks owner j target csize mode flag.

Definition Syscall_mon_tsl_set (ks: Types_kstate) (owner: u64) (i: u64) (j: u64) (enable: bool) : option Types_kstate :=
  let* target := Mon_get_pid ks owner i in
  if (Int64.eq target 0UL) then
    ret (ks <| types_kstate_errcode := Error_invalid_access |>)
  else
    Tsl_set ks target j enable.

Definition Syscall_get_ret (ks: Types_kstate) : u64 :=
  U64.of_i64 ks.(types_kstate_errcode).

Definition Syscall_ecall_u : u64 := 8UL.

Definition Syscall_do (ks: Types_kstate) (pid: u64) (call: Syscall_syscall) : option Types_kstate :=
  let* pc := Proc_get_reg ks pid Types_Reg_pc in
  let* ks := Proc_set_reg ks pid Types_Reg_pc (pc +₆₄ 4UL) in
  let* ks :=
    match call with
    | Syscall_Syscall_pid_get =>
        ret (Syscall_pid_get ks pid)
    | Syscall_Syscall_tsl_derive =>
        let* i := Proc_get_reg ks pid Types_Reg_a1 in
        let* csize := Proc_get_reg ks pid Types_Reg_a2 in
        let* enable :=
          let* b1 := Proc_get_reg ks pid Types_Reg_a3 in
          ret (Int64.cmpu Cgt b1 0UL)
        in
        let* size := Proc_get_reg ks pid Types_Reg_a4 in
        Tsl_derive ks pid i pid csize enable size
    | Syscall_Syscall_mon_derive =>
        let* i := Proc_get_reg ks pid Types_Reg_a1 in
        let* csize := Proc_get_reg ks pid Types_Reg_a2 in
        Mon_derive ks pid i pid csize
    | Syscall_Syscall_ipc_derive =>
        let* i := Proc_get_reg ks pid Types_Reg_a1 in
        let* csize := Proc_get_reg ks pid Types_Reg_a2 in
        let* mode :=
          let* b2 := Proc_get_reg ks pid Types_Reg_a3 in
          ret (U32.of_u64 b2)
        in
        let* flag :=
          let* b3 := Proc_get_reg ks pid Types_Reg_a4 in
          ret (U32.of_u64 b3)
        in
        Ipc_derive ks pid i pid csize mode flag
    | Syscall_Syscall_tsl_revoke =>
        let* i := Proc_get_reg ks pid Types_Reg_a1 in
        Tsl_revoke ks pid i
    | Syscall_Syscall_mon_revoke =>
        let* i := Proc_get_reg ks pid Types_Reg_a1 in
        Mon_revoke ks pid i
    | Syscall_Syscall_ipc_revoke =>
        let* i := Proc_get_reg ks pid Types_Reg_a1 in
        Ipc_revoke ks pid i
    | Syscall_Syscall_tsl_delete =>
        let* i := Proc_get_reg ks pid Types_Reg_a1 in
        Tsl_delete ks pid i
    | Syscall_Syscall_mon_delete =>
        let* i := Proc_get_reg ks pid Types_Reg_a1 in
        Mon_delete ks pid i
    | Syscall_Syscall_ipc_delete =>
        let* i := Proc_get_reg ks pid Types_Reg_a1 in
        Ipc_delete ks pid i
    | Syscall_Syscall_tsl_set =>
        let* i := Proc_get_reg ks pid Types_Reg_a1 in
        let* enable :=
          let* b4 := Proc_get_reg ks pid Types_Reg_a2 in
          ret (Int64.cmpu Cgt b4 0UL)
        in
        Tsl_set ks pid i enable
    | Syscall_Syscall_mon_tsl_grant =>
        let* i := Proc_get_reg ks pid Types_Reg_a1 in
        let* j := Proc_get_reg ks pid Types_Reg_a2 in
        Syscall_mon_tsl_grant ks pid i j
    | Syscall_Syscall_mon_mon_grant =>
        let* i := Proc_get_reg ks pid Types_Reg_a1 in
        let* j := Proc_get_reg ks pid Types_Reg_a2 in
        Syscall_mon_mon_grant ks pid i j
    | Syscall_Syscall_mon_ipc_grant =>
        let* i := Proc_get_reg ks pid Types_Reg_a1 in
        let* j := Proc_get_reg ks pid Types_Reg_a2 in
        Syscall_mon_ipc_grant ks pid i j
    | Syscall_Syscall_mon_tsl_derive =>
        let* i := Proc_get_reg ks pid Types_Reg_a1 in
        let* j := Proc_get_reg ks pid Types_Reg_a2 in
        let* csize := Proc_get_reg ks pid Types_Reg_a3 in
        let* enable :=
          let* b5 := Proc_get_reg ks pid Types_Reg_a4 in
          ret (Int64.cmpu Cgt b5 0UL)
        in
        let* size := Proc_get_reg ks pid Types_Reg_a5 in
        Syscall_mon_tsl_derive ks pid i j csize enable size
    | Syscall_Syscall_mon_mon_derive =>
        let* i := Proc_get_reg ks pid Types_Reg_a1 in
        let* j := Proc_get_reg ks pid Types_Reg_a2 in
        let* csize := Proc_get_reg ks pid Types_Reg_a3 in
        Syscall_mon_mon_derive ks pid i j csize
    | Syscall_Syscall_mon_ipc_derive =>
        let* i := Proc_get_reg ks pid Types_Reg_a1 in
        let* j := Proc_get_reg ks pid Types_Reg_a2 in
        let* csize := Proc_get_reg ks pid Types_Reg_a3 in
        let* mode :=
          let* b6 := Proc_get_reg ks pid Types_Reg_a4 in
          ret (U32.of_u64 b6)
        in
        let* flag :=
          let* b7 := Proc_get_reg ks pid Types_Reg_a5 in
          ret (U32.of_u64 b7)
        in
        Syscall_mon_ipc_derive ks pid i j csize mode flag
    | Syscall_Syscall_mon_tsl_set =>
        let* i := Proc_get_reg ks pid Types_Reg_a1 in
        let* j := Proc_get_reg ks pid Types_Reg_a2 in
        let* enable :=
          let* b8 := Proc_get_reg ks pid Types_Reg_a3 in
          ret (Int64.cmpu Cgt b8 0UL)
        in
        Syscall_mon_tsl_set ks pid i j enable
    | Syscall_Syscall_ipc_call =>
        let* i := Proc_get_reg ks pid Types_Reg_a1 in
        let* ks :=
          let* b9 := Proc_get_reg ks pid Types_Reg_a2 in
          let* b10 := Proc_get_reg ks pid Types_Reg_a3 in
          Syscall_set_message ks b9 b10
        in
        let* capty := Proc_get_reg ks pid Types_Reg_a4 in
        let* j := Proc_get_reg ks pid Types_Reg_a5 in
        Ipc_call ks pid i capty j
    | Syscall_Syscall_ipc_replyrecv =>
        let* i := Proc_get_reg ks pid Types_Reg_a1 in
        let* ks :=
          let* b11 := Proc_get_reg ks pid Types_Reg_a2 in
          let* b12 := Proc_get_reg ks pid Types_Reg_a3 in
          Syscall_set_message ks b11 b12
        in
        let* capty := Proc_get_reg ks pid Types_Reg_a4 in
        let* j := Proc_get_reg ks pid Types_Reg_a5 in
        let* servtime := Proc_get_reg ks pid Types_Reg_a6 in
        Ipc_replyrecv ks pid i capty j (U32.of_u64 servtime)
    | _ =>
        Syscall_delegate ks
    end
  in
  Proc_set_reg ks pid Types_Reg_a0 (U64.of_i64 ks.(types_kstate_errcode)).

Definition Syscall_handler (ks: Types_kstate) : option Types_kstate :=
  let pid := ks.(types_kstate_active_pid) in
  let* call := Proc_get_reg ks pid Types_Reg_a0 in
  if (Int64.cmpu Cge call (U64.of_Z (Syscall_syscall_to_Z Syscall_Syscall_max))) then
    let ks := ks <| types_kstate_errcode := Error_invalid_access |> in
    Exception_handler ks Syscall_ecall_u call
  else
    let* b1 := Machine_lock_acquire true in
    if (negb b1) then
      ret (ks <| types_kstate_active_pid := Types_invalid_pid |>)
    else
      let* ks :=
        let* b2 := Syscall_syscall_of_Z (U64.to_Z call) in
        Syscall_do ks pid b2
      in
      let* dummy := Machine_lock_release tt in
      ret ks.
