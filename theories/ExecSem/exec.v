From stdpp Require Import prelude.
From RecordUpdate Require Import RecordUpdate.
From compcert Require Import Integers.
From S3K.ExecSem Require Import cap kstate util sched proc ctx.
From S3K.BarocqComp Require Import Intop.

Import IntopNotations.

(** * Executable semantics for S3K *)

(** ** Error code definitions *)

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

(** ** Monitor operations *)

Definition exec_mon_introspect (kstate: kstate_t) (owner i j: nat) : option (int64 * int64) :=
  match cap_owner_get kstate.(kmon_tbl) owner i with
  | None => Some (err_invalid_access, Int64.zero)
  | Some ci =>
    if decide (i ≤ j ∧ j < i + ci.(cfree)) then
      match cap_get kstate.(kmon_tbl) j with
      | None => None
      | Some cj => 
        let wowner := match cj.(cowner) with None => Int64.zero | Some v => nat_to_int64 (S v) end in
        let wfree := (nat_to_int64 cj.(cfree)) <<₆₄ (Int64.repr 16) in
        let wsize := (nat_to_int64 cj.(csize)) <<₆₄ (Int64.repr 32) in
        let wpid  := (nat_to_int64 cj.(cdata).(mpid)) <<₆₄ (Int64.repr 48) in
        let raw := wowner |₆₄ wfree |₆₄ wsize |₆₄ wpid in
        Some (err_success 0, raw)
      end
    else
      Some (err_invalid_access, Int64.zero)
  end.

Definition exec_mon_revoke (kstate : kstate_t) (owner : nat) (i : nat) : option (kstate_t * int64) :=
  match cap_owner_get kstate.(kmon_tbl) owner i with
  | None => Some (kstate, err_invalid_access)
  | Some ci =>
    if decide (ci.(cfree) < ci.(csize)) then
      let j := i + ci.(cfree) in
      match cap_get kstate.(kmon_tbl) j with
      | None => None
      | Some cj =>
        let ci' := ci <| (@cfree mon_t) := ci.(cfree) + cj.(cfree) |> in
        let kmon_tbl' := cap_set (cap_set kstate.(kmon_tbl) (i, (Some ci'))) (j, None) in
        let kstate' := kstate <| kmon_tbl := kmon_tbl' |> in
        Some (kstate', err_success (ci'.(csize) - ci'.(cfree)))
      end
    else 
      Some (kstate, err_success 0)
  end.

Definition exec_mon_delete (kstate : kstate_t) (owner : nat) (i : nat) : (kstate_t * int64):=
  match cap_owner_get kstate.(kmon_tbl) owner i with
  | None => (kstate, err_invalid_access)
  | Some ci => 
      let ci' := ci <| (@cowner mon_t) := None |> in
      let kmon_tbl' := cap_set kstate.(kmon_tbl) (i, (Some ci')) in
      let kstate' := kstate <| kmon_tbl := kmon_tbl' |> in
      (kstate', err_success 0)
  end.

(** ** Time slice operations *)

Definition exec_tsl_revoke (kstate : kstate_t) (owner : nat) (i : nat) : option (kstate_t * int64) :=
  match cap_owner_get kstate.(ktsl_tbl) owner i with
  | None => Some (kstate, err_invalid_access)
  | Some ci =>
    if decide (ci.(cfree) < ci.(csize)) then
      let j := i + ci.(cfree) in
      match cap_get kstate.(ktsl_tbl) j with
      | None => None
      | Some cj =>
        let di' := ci.(cdata) <| tfree := ci.(cdata).(tfree) + cj.(cdata).(tfree) |> in
        let ci' := ci <| (@cfree tsl_t) := ci.(cfree) + cj.(cfree) |>
                      <| (@cdata tsl_t) := di' |> in
        let ktsl_tbl' := cap_set (cap_set kstate.(ktsl_tbl) (i, (Some ci'))) (j, None) in
        let ksched' :=
          if decide (cj.(cdata).(tfree) ≠ 0) then
            sched_set
              (sched_set kstate.(ksched) cj.(cdata).(thart) cj.(cdata).(tbase) None 0)
              ci'.(cdata).(thart) ci'.(cdata).(tbase) ci'.(cowner) ci'.(cdata).(tfree)
          else 
            kstate.(ksched)
        in
        let kstate' := kstate <| ktsl_tbl := ktsl_tbl' |> <| ksched := ksched' |> in
        Some (kstate', err_success (ci'.(csize) - ci'.(cfree)))
      end
    else 
      Some (kstate, err_success 0)
  end.


(** ** Memory operations *)
Definition exec_mem_pmp_set (kstate : kstate_t) (owner : nat) (i : nat)
  (pmpreg : pmpreg_t) (pmpconf : pmpconf_t)
  : kstate_t * int64 :=
  match cap_owner_get kstate.(kmem_tbl) owner i with
  | None => (kstate, err_invalid_access)
  | Some ci =>
      match ptable_pmp_get kstate.(kptable) (owner, pmpreg) with
      | Some _ => (kstate, err_invalid_state)
      | None =>
          let '(pperm, pbase, psize) := pmp_decode pmpconf in
          if decide (
               ci.(cdata).(mbase) ≤ pbase ∧
               pbase + psize < ci.(cdata).(mbase) + ci.(cdata).(msize) ∧
               pperm ⊆ ci.(cdata).(mperm) ∧
               (PERM_WRITE ∈ pperm → PERM_READ ∈ pperm) ∧
               (PERM_EXEC ∈ pperm → PERM_READ ∈ pperm)
             )
          then
            let di := ci.(cdata)<| mslot := Some pmpreg |> in
            let ci' := ci <| (@cdata mem_t) := di |> in
            let kmem_tbl' := cap_set kstate.(kmem_tbl) (i, Some ci') in
            let kptable' :=
              ptable_pmp_try_set kstate.(kptable) (ci.(cowner), (Some pmpreg), (Some pmpconf))
            in
            let kstate' := kstate <| kmem_tbl := kmem_tbl' |> <| kptable := kptable' |> in
            (kstate', err_success 0)
          else
            (kstate, err_invalid_argument)
      end
  end.

Definition exec_mon_reg_get '(kstate, ctx) (p : nat) (i : nat) (reg : reg_t)
  : option (int64 * int64) :=
  match cap_owner_get kstate.(kmon_tbl) p i with
  | None => Some (err_invalid_access, Int64.zero)
  | Some ci =>
      match kstate.(kptable) !! ci.(cdata).(mpid) with
      | None => None
      | Some proc =>
          if ctx_busy_at ci.(cdata).(mpid) ctx then
            Some (err_invalid_state, Int64.zero)
          else
            Some (err_success 0, proc_reg_get proc reg)
      end
  end.

(** ** System calls *)

(** ** Syscall handler definitions *)

