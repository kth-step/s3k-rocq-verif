From stdpp Require Import prelude gmap.
From RecordUpdate Require Import RecordUpdate.
From compcert Require Import Integers.
From S3K.ExecSem Require Import util config cap proc sched kernel.
From BarocqComp Require Import Intop.

Import IntopNotations.

(** * Executable semantics for S3K *)

(** ** Error code definitions *)

(** Syscall status values use zero/nonnegative words for success payloads and
    two's-complement negative words for modeled failures. *)

Definition err_success (n : nat) : int64 :=
  nat_to_int64 n.

Definition err_invalid_syscall : int64 :=
  Int64.repr (-1).

Definition err_invalid_access : int64 :=
  Int64.repr (-2).

Definition err_invalid_argument : int64 :=
  Int64.repr (-3).

Definition err_invalid_state : int64 :=
  Int64.repr (-4).

Definition cap_header_pack (owner free size : int64) : int64 :=
  owner |₆₄ (free <<₆₄ Int64.repr 16) |₆₄ (size <<₆₄ Int64.repr 32).

(** Executable operations are partial only when a referenced table index is
    absent or inconsistent. Authorization failures return an [err_*] value. *)

Definition exec_release (ks : kernel_t) (owner : nat) : option kernel_t :=
  match ptable_busy_upd owner false ks.(kptable) with
  | None => None
  | Some ptbl => Some (ks <| kptable := ptbl |>)
  end.

(** ** Monitor operations *)

(** Introspection packs owner, free extent, total extent, and monitor pid into
    four 16-bit fields. Owner zero means unowned; process ids are one-based. *)
Definition exec_mon_introspect (ks : kernel_t) (owner i j : nat)
  : option (int64 * int64) :=
  match cap_owner_get ks.(kmon_tbl) owner i with
  | None => Some (err_invalid_access, Int64.zero)
  | Some ci =>
      if decide (i ≤ j ∧ j < i + ci.(csize)) then
        match cap_get ks.(kmon_tbl) j with
        | None => None
        | Some None => Some (err_success 0, Int64.zero)
        | Some (Some cj) =>
            let wowner := match cj.(cowner) with
                          | None => Int64.zero
                          | Some v => nat_to_int64 (S v)
                          end in
            let wpid := nat_to_int64 (S cj.(cdata).(mpid)) <<₆₄ Int64.repr 48 in
            let raw := cap_header_pack wowner (nat_to_int64 cj.(cfree))
                         (nat_to_int64 cj.(csize)) |₆₄ wpid in
            Some (err_success 0, raw)
        end
      else
        Some (err_invalid_access, Int64.zero)
  end.

Definition exec_mon_transfer (ks : kernel_t) (owner i target : nat)
  : kernel_t * int64 :=
  match cap_owner_get ks.(kmon_tbl) owner i with
  | None => (ks, err_invalid_access)
  | Some ci =>
      let ci' := ci <| (@cowner mon_t) := Some target |> in
      let tbl' := cap_set ks.(kmon_tbl) (i, Some ci') in
      (ks <| kmon_tbl := tbl' |>, err_success 0)
  end.

Definition exec_mon_derive (ks : kernel_t) (owner i csize : nat)
  : option (kernel_t * int64) :=
  match cap_owner_get ks.(kmon_tbl) owner i with
  | None => Some (ks, err_invalid_access)
  | Some ci =>
      let j := i + ci.(cfree) - csize in
      if decide (csize = 0 ∨ ci.(cfree) ≤ csize) then
        Some (ks, err_invalid_argument)
      else if decide (j < ctable_size ks.(kmon_tbl)) then
        let ci' := ci <| (@cfree mon_t) := ci.(cfree) - csize |> in
        let cj := {| cowner := Some owner;
                     cfree := csize;
                     csize := csize;
                     cdata := ci.(cdata) |} in
        let tbl' := cap_set (cap_set ks.(kmon_tbl) (i, Some ci')) (j, Some cj) in
        Some (ks <| kmon_tbl := tbl' |>, err_success j)
      else None
  end.

Definition exec_mon_revoke (ks : kernel_t) (owner i : nat)
  : option (kernel_t * int64) :=
  match cap_owner_get ks.(kmon_tbl) owner i with
  | None => Some (ks, err_invalid_access)
  | Some ci =>
      if decide (ci.(cfree) < ci.(csize)) then
        let j := i + ci.(cfree) in
        match cap_get ks.(kmon_tbl) j with
        | None => None
        | Some None => None
        | Some (Some cj) =>
            let ci' := ci <| (@cfree mon_t) := ci.(cfree) + cj.(cfree) |> in
            let tbl' := cap_set (cap_set ks.(kmon_tbl) (i, Some ci')) (j, None) in
            let rem := ci.(csize) - ci.(cfree) - cj.(cfree) in
            Some (ks <| kmon_tbl := tbl' |>, err_success rem)
        end
      else
        Some (ks, err_success 0)
  end.

Definition exec_mon_delete (ks : kernel_t) (owner i : nat) : kernel_t * int64 :=
  match cap_owner_get ks.(kmon_tbl) owner i with
  | None => (ks, err_invalid_access)
  | Some ci =>
      let ci' := ci <| (@cowner mon_t) := None |> in
      let tbl' := cap_set ks.(kmon_tbl) (i, Some ci') in
      (ks <| kmon_tbl := tbl' |>, err_success 0)
  end.

(** ** Time slice operations *)

(** The first word describes capability metadata and hart; the second describes
    the base, free length, and total length of the inspected time slice. *)
Definition exec_tsl_introspect (ks : kernel_t) (owner i j : nat)
  : option (int64 * int64 * int64) :=
  match cap_owner_get ks.(ktsl_tbl) owner i with
  | None => Some (err_invalid_access, Int64.zero, Int64.zero)
  | Some ci =>
      if decide (i ≤ j ∧ j < i + ci.(csize)) then
        match cap_get ks.(ktsl_tbl) j with
        | None => None
        | Some None => Some (err_success 0, Int64.zero, Int64.zero)
        | Some (Some cj) =>
            let wcowner := match cj.(cowner) with
                           | None => Int64.zero
                           | Some v => nat_to_int64 (S v)
                           end in
            let wthart := nat_to_int64 cj.(cdata).(thart) <<₆₄ Int64.repr 48 in
            let raw0 := cap_header_pack wcowner (nat_to_int64 cj.(cfree))
                          (nat_to_int64 cj.(csize)) |₆₄ wthart in
            let wtbase := nat_to_int64 cj.(cdata).(tbase) in
            let wtfree := nat_to_int64 cj.(cdata).(tfree) <<₆₄ Int64.repr 16 in
            let wtsize := nat_to_int64 cj.(cdata).(tsize) <<₆₄ Int64.repr 32 in
            let raw1 := wtbase |₆₄ wtfree |₆₄ wtsize in
            Some (err_success 0, raw0, raw1)
        end
      else
        Some (err_invalid_access, Int64.zero, Int64.zero)
  end.

Definition exec_tsl_transfer (ks : kernel_t) (owner i target : nat)
  : kernel_t * int64 :=
  match cap_owner_get ks.(ktsl_tbl) owner i with
  | None => (ks, err_invalid_access)
  | Some ci =>
      let ci' := ci <| (@cowner tsl_t) := Some target |> in
      let tbl' := cap_set ks.(ktsl_tbl) (i, Some ci') in
      let ksched' :=
        if decide (ci.(cdata).(tfree) ≠ 0) then
          sched_set ks.(ksched)
            (ci.(cdata).(thart), ci.(cdata).(tbase), Some target, ci.(cdata).(tfree))
        else
          ks.(ksched) in
      (ks <| ktsl_tbl := tbl' |> <| ksched := ksched' |>, err_success 0)
  end.

Definition exec_tsl_derive (ks : kernel_t) (owner i csize tsize : nat)
  : option (kernel_t * int64) :=
  match cap_owner_get ks.(ktsl_tbl) owner i with
  | None => Some (ks, err_invalid_access)
  | Some ci =>
      if decide (csize = 0 ∨ ci.(cfree) ≤ csize ∨ tsize = 0 ∨ ci.(cdata).(tfree) < tsize) then
        Some (ks, err_invalid_argument)
      else
        let j := i + ci.(cfree) - csize in
        if decide (j < ctable_size ks.(ktsl_tbl)) then
          let di' := ci.(cdata) <| tfree := ci.(cdata).(tfree) - tsize |> in
          let ci' := ci <| (@cfree tsl_t) := ci.(cfree) - csize |>
                        <| (@cdata tsl_t) := di' |> in
          let dj := {| thart := ci.(cdata).(thart);
                       tbase := ci.(cdata).(tbase) + ci.(cdata).(tfree) - tsize;
                       tfree := tsize;
                       tsize := tsize |} in
          let cj := {| cowner := Some owner;
                       cfree := csize;
                       csize := csize;
                       cdata := dj |} in
          let tbl' := cap_set (cap_set ks.(ktsl_tbl) (i, Some ci')) (j, Some cj) in
          let sched' :=
            sched_set
              (sched_set ks.(ksched)
                 (ci'.(cdata).(thart), ci'.(cdata).(tbase), ci'.(cowner), ci'.(cdata).(tfree)))
              (cj.(cdata).(thart), cj.(cdata).(tbase), cj.(cowner), cj.(cdata).(tfree)) in
          Some (ks <| ktsl_tbl := tbl' |> <| ksched := sched' |>, err_success j)
        else None
  end.

Definition exec_tsl_revoke (ks : kernel_t) (owner i : nat)
  : option (kernel_t * int64) :=
  match cap_owner_get ks.(ktsl_tbl) owner i with
  | None => Some (ks, err_invalid_access)
  | Some ci =>
      if decide (ci.(cfree) < ci.(csize)) then
        let j := i + ci.(cfree) in
        match cap_get ks.(ktsl_tbl) j with
        | None => None
        | Some None => None
        | Some (Some cj) =>
            let di' := ci.(cdata) <| tfree := ci.(cdata).(tfree) + cj.(cdata).(tfree) |> in
            let ci' := ci <| (@cfree tsl_t) := ci.(cfree) + cj.(cfree) |>
                          <| (@cdata tsl_t) := di' |> in
            let tbl' := cap_set (cap_set ks.(ktsl_tbl) (i, Some ci')) (j, None) in
            let sched' :=
              if decide (cj.(cdata).(tfree) ≠ 0) then
                sched_set
                  (sched_set ks.(ksched) (cj.(cdata).(thart), cj.(cdata).(tbase), None, 0))
                  (ci'.(cdata).(thart), ci'.(cdata).(tbase), ci'.(cowner), ci'.(cdata).(tfree))
              else
                ks.(ksched) in
            let rem := ci.(csize) - ci.(cfree) - cj.(cfree) in
            Some (ks <| ktsl_tbl := tbl' |> <| ksched := sched' |>, err_success rem)
        end
      else
        Some (ks, err_success 0)
  end.

Definition exec_tsl_delete (ks : kernel_t) (owner i : nat) : kernel_t * int64 :=
  match cap_owner_get ks.(ktsl_tbl) owner i with
  | None => (ks, err_invalid_access)
  | Some ci =>
      let ci' := ci <| (@cowner tsl_t) := None |> in
      let tbl' := cap_set ks.(ktsl_tbl) (i, Some ci') in
      let sched' :=
        if decide (ci.(cdata).(tfree) ≠ 0) then
          sched_set ks.(ksched)
            (ci'.(cdata).(thart), ci'.(cdata).(tbase), ci'.(cowner), ci'.(cdata).(tfree))
        else
          ks.(ksched) in
      (ks <| ktsl_tbl := tbl' |> <| ksched := sched' |>, err_success 0)
  end.

(** ** Memory operations *)

(** Base and size occupy separate words to preserve the full address range. *)
Definition exec_mem_introspect (ks : kernel_t) (owner i j : nat)
  : option (int64 * int64 * int64 * int64) :=
  match cap_owner_get ks.(kmem_tbl) owner i with
  | None => Some (err_invalid_access, Int64.zero, Int64.zero, Int64.zero)
  | Some ci =>
      if decide (i ≤ j ∧ j < i + ci.(csize)) then
        match cap_get ks.(kmem_tbl) j with
        | None => None
        | Some None => Some (err_success 0, Int64.zero, Int64.zero, Int64.zero)
        | Some (Some cj) =>
            let wcowner := match cj.(cowner) with
                           | None => Int64.zero
                           | Some v => nat_to_int64 (S v)
                           end in
            let wmperm := byte_to_int64 (rwx_encode cj.(cdata).(mperm)) <<₆₄ Int64.repr 48 in
            let raw0 := cap_header_pack wcowner (nat_to_int64 cj.(cfree))
                          (nat_to_int64 cj.(csize)) |₆₄ wmperm in
            let wmbase := nat_to_int64 cj.(cdata).(mbase) in
            let wmsize := nat_to_int64 cj.(cdata).(msize) in
            Some (err_success 0, raw0, wmbase, wmsize)
        end
      else
        Some (err_invalid_access, Int64.zero, Int64.zero, Int64.zero)
  end.

Definition exec_mem_transfer (ks : kernel_t) (owner i target : nat)
  : option (kernel_t * int64) :=
  match cap_owner_get ks.(kmem_tbl) owner i with
  | None => Some (ks, err_invalid_access)
  | Some ci =>
      let di' := ci.(cdata) <| mslot := None |> in
      let ci' := ci <| (@cowner mem_t) := Some target |> <| (@cdata mem_t) := di' |> in
      let memtbl' := cap_set ks.(kmem_tbl) (i, Some ci') in
      match ptable_pmp_try_clear ci.(cowner) ci.(cdata).(mslot) ks.(kptable) with
      | None => None
      | Some ptbl =>
          Some (ks <| kmem_tbl := memtbl' |> <| kptable := ptbl |>, err_success 0)
      end
  end.

(** The parameters [mbase], [msize] and [mperm] of HOL4 are renamed to
    [base], [size] and [perm] so that they do not shadow the projections
    of [mem_t]. *)
Definition exec_mem_derive (ks : kernel_t) (owner i csize base size : nat)
  (perm : gset perm_t) : option (kernel_t * int64) :=
  match cap_owner_get ks.(kmem_tbl) owner i with
  | None => Some (ks, err_invalid_access)
  | Some ci =>
      if decide (0 < csize ∧ csize < ci.(cfree) ∧ 0 < size ∧
                 ci.(cdata).(mbase) ≤ base ∧
                 base + size < ci.(cdata).(mbase) + ci.(cdata).(msize) ∧
                 perm ⊆ ci.(cdata).(mperm)) then
        let j := i + ci.(cfree) - csize in
        if decide (j < ctable_size ks.(kmem_tbl)) then
          let ci' := ci <| (@cfree mem_t) := ci.(cfree) - csize |> in
          let dj := {| mbase := base; msize := size; mperm := perm; mslot := None |} in
          let cj := {| cowner := Some owner; cfree := csize; csize := csize; cdata := dj |} in
          let memtbl' := cap_set (cap_set ks.(kmem_tbl) (i, Some ci')) (j, Some cj) in
          Some (ks <| kmem_tbl := memtbl' |>, err_success j)
        else
          None
      else
        Some (ks, err_invalid_argument)
  end.

Definition exec_mem_revoke (ks : kernel_t) (owner i : nat)
  : option (kernel_t * int64) :=
  match cap_owner_get ks.(kmem_tbl) owner i with
  | None => Some (ks, err_invalid_access)
  | Some ci =>
      if decide (ci.(cfree) < ci.(csize)) then
        match cap_get ks.(kmem_tbl) (i + ci.(cfree)) with
        | None => None
        | Some None => None
        | Some (Some cj) =>
            let ci' := ci <| (@cfree mem_t) := ci.(cfree) + cj.(cfree) |> in
            let memtbl' := cap_set (cap_set ks.(kmem_tbl) (i, Some ci'))
                             (i + ci.(cfree), None) in
            let rem := ci.(csize) - ci.(cfree) - cj.(cfree) in
            match ptable_pmp_try_clear cj.(cowner) cj.(cdata).(mslot) ks.(kptable) with
            | None => None
            | Some ptbl =>
                Some (ks <| kmem_tbl := memtbl' |> <| kptable := ptbl |>, err_success rem)
            end
        end
      else
        Some (ks, err_success 0)
  end.

Definition exec_mem_delete (ks : kernel_t) (owner i : nat)
  : option (kernel_t * int64) :=
  match cap_owner_get ks.(kmem_tbl) owner i with
  | None => Some (ks, err_invalid_access)
  | Some ci =>
      let ci' := ci <| (@cowner mem_t) := None |> in
      let memtbl' := cap_set ks.(kmem_tbl) (i, Some ci') in
      match ptable_pmp_try_clear ci.(cowner) ci.(cdata).(mslot) ks.(kptable) with
      | None => None
      | Some ptbl =>
          Some (ks <| kmem_tbl := memtbl' |> <| kptable := ptbl |>, err_success 0)
      end
  end.

Definition exec_mem_pmp_set (ks : kernel_t) (owner i : nat)
  (pmpreg : option pmpreg_t) (pmpconf : pmpconf_t) : option (kernel_t * int64) :=
  match cap_owner_get ks.(kmem_tbl) owner i with
  | None => Some (ks, err_invalid_access)
  | Some ci =>
      match pmpreg with
      | None =>
          let di := ci.(cdata) <| mslot := None |> in
          let ci' := ci <| (@cdata mem_t) := di |> in
          let kmem_tbl' := cap_set ks.(kmem_tbl) (i, Some ci') in
          match ptable_pmp_try_clear ci.(cowner) ci.(cdata).(mslot) ks.(kptable) with
          | None => None
          | Some ptbl =>
              Some (ks <| kmem_tbl := kmem_tbl' |> <| kptable := ptbl |>, err_success 0)
          end
      | Some pmpreg =>
          match ci.(cdata).(mslot) with
          | Some _ => Some (ks, err_invalid_state)
          | None =>
              match ptable_get owner ks.(kptable) with
              | None => None
              | Some proc =>
                  if decide (length proc.(ppmp) ≤ pmpreg_t2num pmpreg) then None else
                  match proc_pmp_get proc pmpreg with
                  | Some _ => Some (ks, err_invalid_state)
                  | None =>
                      let '(pperm, pbase, psize) := pmp_decode pmpconf in
                      if decide (
                           pmpconf.(wpmp_conf) ≠ Byte.zero ∧
                           ci.(cdata).(mbase) ≤ pbase ∧
                           pbase + psize ≤ ci.(cdata).(mbase) + ci.(cdata).(msize) ∧
                           pperm ⊆ ci.(cdata).(mperm) ∧
                           (PERM_WRITE ∈ pperm → PERM_READ ∈ pperm) ∧
                           (PERM_EXEC ∈ pperm → PERM_READ ∈ pperm))
                      then
                        match ptable_pmp_upd owner pmpreg (Some pmpconf) ks.(kptable) with
                        | None => None
                        | Some ptbl =>
                            let di := ci.(cdata) <| mslot := Some pmpreg |> in
                            let ci' := ci <| (@cdata mem_t) := di |> in
                            let kmem_tbl' := cap_set ks.(kmem_tbl) (i, Some ci') in
                            let ks' := ks <| kmem_tbl := kmem_tbl' |> <| kptable := ptbl |> in
                            Some (ks', err_success 0)
                        end
                      else Some (ks, err_invalid_argument)
                  end
              end
          end
      end
  end.

(** ** Process operations *)

Definition exec_mon_suspend (ks : kernel_t) (owner i : nat) (b : bool)
  : option (kernel_t * int64) :=
  match cap_owner_get ks.(kmon_tbl) owner i with
  | None => Some (ks, err_invalid_access)
  | Some ci =>
      match ptable_suspend_upd ci.(cdata).(mpid) b ks.(kptable) with
      | None => None
      | Some ptbl => Some (ks <| kptable := ptbl |>, err_success 0)
      end
  end.

Definition exec_mon_reg_get (ks : kernel_t) (p i reg : nat)
  : option (int64 * int64) :=
  match cap_owner_get ks.(kmon_tbl) p i with
  | None => Some (err_invalid_access, Int64.zero)
  | Some ci =>
      match ptable_get ci.(cdata).(mpid) ks.(kptable) with
      | None => None
      | Some proc =>
          if decide (length proc.(pregs) ≠ REG_CNT) then None
          else if proc_busy_get proc then
            Some (err_invalid_state, Int64.zero)
          else
            Some (err_success 0, proc_reg_get proc reg)
      end
  end.

Definition exec_mon_reg_set (ks : kernel_t) (p i reg : nat) (value : int64)
  : option (kernel_t * int64) :=
  match cap_owner_get ks.(kmon_tbl) p i with
  | None => Some (ks, err_invalid_access)
  | Some ci =>
      match ptable_get ci.(cdata).(mpid) ks.(kptable) with
      | None => None
      | Some proc =>
          if decide (length proc.(pregs) ≠ REG_CNT) then None
          else if proc_busy_get proc then
            Some (ks, err_invalid_state)
          else
            match ptable_reg_upd ci.(cdata).(mpid) reg value ks.(kptable) with
            | None => None
            | Some ptbl => Some (ks <| kptable := ptbl |>, err_success 0)
            end
      end
  end.

(** Trap entry snapshots the live hart registers into the calling process. *)
Definition exec_trap_entry (ks : kernel_t) (p : nat) (regs : regs_t)
  : option kernel_t :=
  if decide (length regs ≠ REG_CNT) then None else
  match ptable_upd p (λ proc, proc <| pregs := regs |>) ks.(kptable) with
  | None => None
  | Some ptbl => Some (ks <| kptable := ptbl |>)
  end.

(** ** System calls *)

(** Skip the ecall, apply return-register updates, and select the next process.
    The boolean result tells the system semantics whether to reload PMP state. *)
Definition exec_syscall_retl (ks : kernel_t) (p : nat) (p_opt : option nat)
  (b : bool) (upd : regs_t -> regs_t) : option (kernel_t * option nat * bool) :=
  match ptable_get p ks.(kptable) with
  | None => None
  | Some proc =>
      if decide (length proc.(pregs) ≠ REG_CNT ∨ length (upd proc.(pregs)) ≠ REG_CNT)
      then None
      else
        let ptbl := ptable_set p
              (proc <| pregs := (<[ reg_pc := (proc.(pregs) !!! reg_pc) +₆₄ Int64.repr 4 ]>
                                   (upd proc.(pregs))) |>)
              ks.(kptable) in
        Some (ks <| kptable := ptbl |>, p_opt, b)
  end.

Definition exec_syscall_ret1 (ks : kernel_t) (p : nat) (b : bool) (a0 : int64)
  : option (kernel_t * option nat * bool) :=
  exec_syscall_retl ks p (Some p) b (<[ reg_a0 := a0 ]>).

Definition exec_syscall_ret2 (ks : kernel_t) (p : nat) (b : bool) (a0 a1 : int64)
  : option (kernel_t * option nat * bool) :=
  exec_syscall_retl ks p (Some p) b ((<[ reg_a0 := a0 ]>) ∘ (<[ reg_a1 := a1 ]>)).

Definition exec_syscall_ret3 (ks : kernel_t) (p : nat) (b : bool) (a0 a1 a2 : int64)
  : option (kernel_t * option nat * bool) :=
  exec_syscall_retl ks p (Some p) b
    ((<[ reg_a0 := a0 ]>) ∘ (<[ reg_a1 := a1 ]>) ∘ (<[ reg_a2 := a2 ]>)).

Definition exec_syscall_ret4 (ks : kernel_t) (p : nat) (b : bool) (a0 a1 a2 a3 : int64)
  : option (kernel_t * option nat * bool) :=
  exec_syscall_retl ks p (Some p) b
    ((<[ reg_a0 := a0 ]>) ∘ (<[ reg_a1 := a1 ]>) ∘
     (<[ reg_a2 := a2 ]>) ∘ (<[ reg_a3 := a3 ]>)).

Definition exec_syscall_finish (p : nat) (result : option (kernel_t * int64))
  : option (kernel_t * option nat * bool) :=
  match result with
  | None => None
  | Some (ks, status) => exec_syscall_ret1 ks p false status
  end.

Definition exec_syscall_pid_get (ks : kernel_t) (p : nat)
  : option (kernel_t * option nat * bool) :=
  exec_syscall_ret1 ks p false (err_success (S p)).

(** Reloads the hart pmp from the caller's entry in the kernel process table. *)
Definition exec_syscall_sync (ks : kernel_t) (p : nat)
  : option (kernel_t * option nat * bool) :=
  exec_syscall_ret1 ks p true (err_success 0).

Definition exec_syscall_yield (ks : kernel_t) (p : nat)
  : option (kernel_t * option nat * bool) :=
  match exec_release ks p with
  | None => None
  | Some ks' => exec_syscall_retl ks' p None false (<[ reg_a0 := err_success 0 ]>)
  end.

Definition exec_syscall_mon_introspect (ks : kernel_t) (p : nat) (i_word j_word : int64)
  : option (kernel_t * option nat * bool) :=
  let i := int64_to_nat i_word in
  let j := int64_to_nat j_word in
  match exec_mon_introspect ks p i j with
  | None => None
  | Some (err, raw0) => exec_syscall_ret2 ks p false err raw0
  end.

Definition exec_syscall_mon_grant (ks : kernel_t) (p : nat) (i_word j_word : int64)
  : option (kernel_t * option nat * bool) :=
  let i := int64_to_nat i_word in
  let j := int64_to_nat j_word in
  match cap_owner_get ks.(kmon_tbl) p i with
  | None => exec_syscall_ret1 ks p false err_invalid_access
  | Some ci =>
      let '(ks', err) := exec_mon_transfer ks p j ci.(cdata).(mpid) in
      exec_syscall_ret1 ks' p false err
  end.

Definition exec_syscall_mon_delete (ks : kernel_t) (p : nat) (i_word : int64)
  : option (kernel_t * option nat * bool) :=
  let i := int64_to_nat i_word in
  let '(ks', err) := exec_mon_delete ks p i in
  exec_syscall_ret1 ks' p false err.

Definition exec_syscall_mon_derive (ks : kernel_t) (p : nat) (i_word csize_word : int64)
  : option (kernel_t * option nat * bool) :=
  let i := int64_to_nat i_word in
  let csize := int64_to_nat csize_word in
  exec_syscall_finish p (exec_mon_derive ks p i csize).

Definition exec_syscall_mon_revoke (ks : kernel_t) (p : nat) (i_word : int64)
  : option (kernel_t * option nat * bool) :=
  let i := int64_to_nat i_word in
  exec_syscall_finish p (exec_mon_revoke ks p i).

Definition exec_syscall_mon_yield (ks : kernel_t) (p : nat) (i_word : int64)
  : option (kernel_t * option nat * bool) :=
  let i := int64_to_nat i_word in
  match cap_owner_get ks.(kmon_tbl) p i with
  | None => exec_syscall_ret1 ks p false err_invalid_access
  | Some ci =>
      if decide (ci.(cdata).(mpid) < length ks.(kptable)) then
        match ptable_get ci.(cdata).(mpid) ks.(kptable) with
        | None => None
        | Some proc =>
            if (proc_busy_get proc || proc_suspend_get proc)%bool then
              exec_syscall_ret1 ks p false err_invalid_state
            else
              match ptable_busy_upd ci.(cdata).(mpid) true ks.(kptable) with
              | None => None
              | Some ptable' =>
                  match ptable_busy_upd p false ptable' with
                  | None => None
                  | Some ptable'' =>
                      exec_syscall_retl (ks <| kptable := ptable'' |>) p
                        (Some ci.(cdata).(mpid)) true (<[ reg_a0 := err_success 0 ]>)
                  end
              end
        end
      else None
  end.

Definition exec_syscall_tsl_introspect (ks : kernel_t) (p : nat) (i_word j_word : int64)
  : option (kernel_t * option nat * bool) :=
  let i := int64_to_nat i_word in
  let j := int64_to_nat j_word in
  match exec_tsl_introspect ks p i j with
  | None => None
  | Some (err, raw0, raw1) => exec_syscall_ret3 ks p false err raw0 raw1
  end.

Definition exec_syscall_tsl_grant (ks : kernel_t) (p : nat) (i_word j_word : int64)
  : option (kernel_t * option nat * bool) :=
  let i := int64_to_nat i_word in
  let j := int64_to_nat j_word in
  match cap_owner_get ks.(kmon_tbl) p i with
  | None => exec_syscall_ret1 ks p false err_invalid_access
  | Some ci =>
      let '(ks', err) := exec_tsl_transfer ks p j ci.(cdata).(mpid) in
      exec_syscall_ret1 ks' p false err
  end.

Definition exec_syscall_tsl_delete (ks : kernel_t) (p : nat) (i_word : int64)
  : option (kernel_t * option nat * bool) :=
  let i := int64_to_nat i_word in
  let '(ks', err) := exec_tsl_delete ks p i in
  exec_syscall_ret1 ks' p false err.

Definition exec_syscall_tsl_derive (ks : kernel_t) (p : nat)
  (i_word csize_word tsize_word : int64) : option (kernel_t * option nat * bool) :=
  let i := int64_to_nat i_word in
  let csize := int64_to_nat csize_word in
  let tsize := int64_to_nat tsize_word in
  exec_syscall_finish p (exec_tsl_derive ks p i csize tsize).

Definition exec_syscall_tsl_revoke (ks : kernel_t) (p : nat) (i_word : int64)
  : option (kernel_t * option nat * bool) :=
  let i := int64_to_nat i_word in
  exec_syscall_finish p (exec_tsl_revoke ks p i).

Definition exec_syscall_mem_introspect (ks : kernel_t) (p : nat) (i_word j_word : int64)
  : option (kernel_t * option nat * bool) :=
  let i := int64_to_nat i_word in
  let j := int64_to_nat j_word in
  match exec_mem_introspect ks p i j with
  | None => None
  | Some (err, raw0, base, size) => exec_syscall_ret4 ks p false err raw0 base size
  end.

Definition exec_syscall_mem_delete (ks : kernel_t) (p : nat) (i_word : int64)
  : option (kernel_t * option nat * bool) :=
  let i := int64_to_nat i_word in
  exec_syscall_finish p (exec_mem_delete ks p i).

Definition exec_syscall_mem_derive (ks : kernel_t) (p : nat)
  (i_word csize_word mbase_word msize_word mperm_word : int64)
  : option (kernel_t * option nat * bool) :=
  if decide (int64_to_byte mperm_word &₈ Byte.repr 7 ≠ int64_to_byte mperm_word) then
    exec_syscall_ret1 ks p false err_invalid_argument
  else
    let i := int64_to_nat i_word in
    let csize := int64_to_nat csize_word in
    let mbase := int64_to_nat mbase_word in
    let msize := int64_to_nat msize_word in
    let mperm := rwx_decode (int64_to_byte mperm_word) in
    exec_syscall_finish p (exec_mem_derive ks p i csize mbase msize mperm).

Definition exec_syscall_mem_revoke (ks : kernel_t) (p : nat) (i_word : int64)
  : option (kernel_t * option nat * bool) :=
  let i := int64_to_nat i_word in
  exec_syscall_finish p (exec_mem_revoke ks p i).

Definition exec_syscall_mem_grant (ks : kernel_t) (p : nat) (i_word j_word : int64)
  : option (kernel_t * option nat * bool) :=
  let i := int64_to_nat i_word in
  let j := int64_to_nat j_word in
  match cap_owner_get ks.(kmon_tbl) p i with
  | None => exec_syscall_ret1 ks p false err_invalid_access
  | Some ci => exec_syscall_finish p (exec_mem_transfer ks p j ci.(cdata).(mpid))
  end.

Definition exec_syscall_mem_set (ks : kernel_t) (p : nat)
  (i_word pmpreg_word pmpconf_word : int64) : option (kernel_t * option nat * bool) :=
  let i := int64_to_nat i_word in
  let pmpconf := pmpconf_unpack pmpconf_word in
  match word2pmpreg_opt pmpreg_word with
  | None => exec_syscall_ret1 ks p false err_invalid_argument
  | Some pmpreg => exec_syscall_finish p (exec_mem_pmp_set ks p i pmpreg pmpconf)
  end.

Definition exec_syscall_mon_suspend (ks : kernel_t) (p : nat) (i_word b_word : int64)
  : option (kernel_t * option nat * bool) :=
  let i := int64_to_nat i_word in
  let b := bool_decide (b_word ≠ Int64.zero) in
  exec_syscall_finish p (exec_mon_suspend ks p i b).

Definition exec_syscall_mon_reg_get (ks : kernel_t) (p : nat) (i_word reg_word : int64)
  : option (kernel_t * option nat * bool) :=
  let i := int64_to_nat i_word in
  if Int64.cmpu Cle (nat_to_int64 REG_CNT) reg_word then
    exec_syscall_ret1 ks p false err_invalid_argument
  else
    match exec_mon_reg_get ks p i (int64_to_nat reg_word) with
    | None => None
    | Some (err, value) => exec_syscall_ret2 ks p false err value
    end.

Definition exec_syscall_mon_reg_set (ks : kernel_t) (p : nat)
  (i_word reg_word value : int64) : option (kernel_t * option nat * bool) :=
  let i := int64_to_nat i_word in
  if Int64.cmpu Cle (nat_to_int64 REG_CNT) reg_word then
    exec_syscall_ret1 ks p false err_invalid_argument
  else
    exec_syscall_finish p (exec_mon_reg_set ks p i (int64_to_nat reg_word) value).

Definition exec_syscall_mon_mem_set (ks : kernel_t) (p : nat)
  (i_word j_word pmpreg_word pmpconf_word : int64)
  : option (kernel_t * option nat * bool) :=
  let i := int64_to_nat i_word in
  let j := int64_to_nat j_word in
  let pmpconf := pmpconf_unpack pmpconf_word in
  match cap_owner_get ks.(kmon_tbl) p i with
  | None => exec_syscall_ret1 ks p false err_invalid_access
  | Some ci =>
      match word2pmpreg_opt pmpreg_word with
      | None => exec_syscall_ret1 ks p false err_invalid_argument
      | Some pmpreg =>
          exec_syscall_finish p (exec_mem_pmp_set ks ci.(cdata).(mpid) j pmpreg pmpconf)
      end
  end.

Definition exec_syscall_invalid (ks : kernel_t) (p : nat)
  : option (kernel_t * option nat * bool) :=
  exec_syscall_ret1 ks p false err_invalid_syscall.

(** ** Syscall handler definitions *)

Inductive systemcall_enum :=
  | SYSCALL_PID_GET
  | SYSCALL_YIELD
  | SYSCALL_SYNC
  | SYSCALL_MEM_INTROSPECT
  | SYSCALL_MEM_DERIVE
  | SYSCALL_MEM_REVOKE
  | SYSCALL_MEM_DELETE
  | SYSCALL_MEM_GRANT
  | SYSCALL_TSL_INTROSPECT
  | SYSCALL_TSL_DERIVE
  | SYSCALL_TSL_REVOKE
  | SYSCALL_TSL_DELETE
  | SYSCALL_TSL_GRANT
  | SYSCALL_MON_INTROSPECT
  | SYSCALL_MON_DERIVE
  | SYSCALL_MON_REVOKE
  | SYSCALL_MON_DELETE
  | SYSCALL_MON_GRANT
  | SYSCALL_MEM_SET
  | SYSCALL_MON_SUSPEND
  | SYSCALL_MON_YIELD
  | SYSCALL_MON_REG_GET
  | SYSCALL_MON_REG_SET
  | SYSCALL_MON_MEM_SET
  | SYSCALL_INVALID.

Definition exec_syscall_decode (syscall_nr : int64) : systemcall_enum :=
  match int64_to_nat syscall_nr with
  | 0 => SYSCALL_PID_GET
  | 1 => SYSCALL_YIELD
  | 2 => SYSCALL_SYNC
  | 3 => SYSCALL_MEM_INTROSPECT
  | 4 => SYSCALL_MEM_DERIVE
  | 5 => SYSCALL_MEM_REVOKE
  | 6 => SYSCALL_MEM_DELETE
  | 7 => SYSCALL_MEM_GRANT
  | 8 => SYSCALL_TSL_INTROSPECT
  | 9 => SYSCALL_TSL_DERIVE
  | 10 => SYSCALL_TSL_REVOKE
  | 11 => SYSCALL_TSL_DELETE
  | 12 => SYSCALL_TSL_GRANT
  | 13 => SYSCALL_MON_INTROSPECT
  | 14 => SYSCALL_MON_DERIVE
  | 15 => SYSCALL_MON_REVOKE
  | 16 => SYSCALL_MON_DELETE
  | 17 => SYSCALL_MON_GRANT
  | 18 => SYSCALL_MEM_SET
  | 19 => SYSCALL_MON_SUSPEND
  | 20 => SYSCALL_MON_YIELD
  | 21 => SYSCALL_MON_REG_GET
  | 22 => SYSCALL_MON_REG_SET
  | 23 => SYSCALL_MON_MEM_SET
  | _ => SYSCALL_INVALID
  end.

(** Decode A7 and pass raw argument-register words to the selected sub-handler. *)
Definition exec_syscall_handler (ks : kernel_t) (p : nat)
  : option (kernel_t * option nat * bool) :=
  match ptable_get p ks.(kptable) with
  | None => None
  | Some proc =>
      match proc_get_args proc with
      | None => None
      | Some args =>
          match exec_syscall_decode args.(args_a7) with
          | SYSCALL_PID_GET => exec_syscall_pid_get ks p
          | SYSCALL_YIELD => exec_syscall_yield ks p
          | SYSCALL_SYNC => exec_syscall_sync ks p
          | SYSCALL_MEM_INTROSPECT =>
              exec_syscall_mem_introspect ks p args.(args_a0) args.(args_a1)
          | SYSCALL_MEM_DERIVE =>
              exec_syscall_mem_derive ks p args.(args_a0) args.(args_a1)
                args.(args_a2) args.(args_a3) args.(args_a4)
          | SYSCALL_MEM_REVOKE =>
              exec_syscall_mem_revoke ks p args.(args_a0)
          | SYSCALL_MEM_DELETE =>
              exec_syscall_mem_delete ks p args.(args_a0)
          | SYSCALL_MEM_GRANT =>
              exec_syscall_mem_grant ks p args.(args_a0) args.(args_a1)
          | SYSCALL_TSL_INTROSPECT =>
              exec_syscall_tsl_introspect ks p args.(args_a0) args.(args_a1)
          | SYSCALL_TSL_DERIVE =>
              exec_syscall_tsl_derive ks p args.(args_a0) args.(args_a1)
                args.(args_a2)
          | SYSCALL_TSL_REVOKE =>
              exec_syscall_tsl_revoke ks p args.(args_a0)
          | SYSCALL_TSL_DELETE =>
              exec_syscall_tsl_delete ks p args.(args_a0)
          | SYSCALL_TSL_GRANT =>
              exec_syscall_tsl_grant ks p args.(args_a0) args.(args_a1)
          | SYSCALL_MON_INTROSPECT =>
              exec_syscall_mon_introspect ks p args.(args_a0) args.(args_a1)
          | SYSCALL_MON_DERIVE =>
              exec_syscall_mon_derive ks p args.(args_a0) args.(args_a1)
          | SYSCALL_MON_REVOKE =>
              exec_syscall_mon_revoke ks p args.(args_a0)
          | SYSCALL_MON_DELETE =>
              exec_syscall_mon_delete ks p args.(args_a0)
          | SYSCALL_MON_GRANT =>
              exec_syscall_mon_grant ks p args.(args_a0) args.(args_a1)
          | SYSCALL_MEM_SET =>
              exec_syscall_mem_set ks p args.(args_a0) args.(args_a1)
                args.(args_a2)
          | SYSCALL_MON_SUSPEND =>
              exec_syscall_mon_suspend ks p args.(args_a0) args.(args_a1)
          | SYSCALL_MON_YIELD =>
              exec_syscall_mon_yield ks p args.(args_a0)
          | SYSCALL_MON_REG_GET =>
              exec_syscall_mon_reg_get ks p args.(args_a0) args.(args_a1)
          | SYSCALL_MON_REG_SET =>
              exec_syscall_mon_reg_set ks p args.(args_a0) args.(args_a1)
                args.(args_a2)
          | SYSCALL_MON_MEM_SET =>
              exec_syscall_mon_mem_set ks p args.(args_a0) args.(args_a1)
                args.(args_a2) args.(args_a3)
          | SYSCALL_INVALID => exec_syscall_invalid ks p
          end
      end
  end.

(** ** Scheduler *)

(** [t] is measured in abstract schedule slots. The result time is the first
    slot after the selected run, or the next slot for an explicit idle entry. *)
Definition exec_sched (ks : kernel_t) (h t : nat)
  : option (kernel_t * option nat * nat) :=
  let tslot := t `mod` TSLOT_CNT in
  match sched_get ks.(ksched) h tslot with
  | None => None
  | Some (None, len) => Some (ks, None, t + 1)
  | Some (Some p, len) =>
      match ptable_get p ks.(kptable) with
      | None => None
      | Some proc =>
          if (proc_busy_get proc || proc_suspend_get proc)%bool then
            Some (ks, None, t + len)
          else
            match ptable_busy_upd p true ks.(kptable) with
            | None => None
            | Some ptbl => Some (ks <| kptable := ptbl |>, Some p, t + len)
            end
      end
  end.

Definition exec_sched_yield (ks : kernel_t) (p : nat) : option kernel_t :=
  exec_release ks p.
