From stdpp Require Import prelude.
From compcert Require Import Integers.
From RecordUpdate Require Import RecordUpdate.
From S3K.Barocq Require Import S3K_ShallowR.
From S3K.ExecSem Require Import kstate cap ctx exec util config.
From S3K.Verif Require Import axioms refine_util refine_tactics refine_map bridge.

Section S3KRefine.

Variable ka : kstate_t.
Variable kb : Types_kstate.

(** * Kernel well-formedness properties *)

(** Capability size is a constant. *)
Hypothesis mon_table_size : ctable_size ka.(kmon_tbl) = MON_SZ.

(** Capability field [cfree] upper bound. *)
Hypothesis cfree_range :
  forall l i v,
  l !! i = Some (Some v) ->
  ka.(kmon_tbl) = CapTable l ->
  (v.(cfree) <= MON_SZ)%nat.

(** Capability field [csize] upper bound. *)
Hypothesis csize_range :
  forall l i v,
  l !! i = Some (Some v) ->
  ka.(kmon_tbl) = CapTable l ->
  (v.(csize) <= MON_SZ)%nat.

(** A capability's next child is within its own range. *)
Hypothesis next_child_range :
  forall l i vi vj,
  l !! i = Some (Some vi) ->
  l !! (i + vi.(cfree))%nat = Some (Some vj) ->
  ka.(kmon_tbl) = CapTable l ->
  (vi.(cfree) + vj.(cfree) <= vi.(csize))%nat.

(** FIXME Assume memory table has no effect on refinement for now. *)
Hypothesis mem_table_correct :
  ka.(kmem_tbl) = dummy_mem_table.

(** * Refinement proofs for capability operations *)

Theorem mon_delele_safe_refine :
  forall ownera ownerb ia ib,
  Rkstate ka kb ->
  Rpid_opt (Some ownera) ownerb ->
  Rnat ia ib ->
  safe_refine Rkstate_with_err (exec_mon_delete ka ownera ia) (Mon_delete kb ownerb ib).
Proof.
  prepare_corres exec_mon_delete Mon_delete.
  gen_corres; solve_corres.
Qed.

Theorem mon_transfer_safe_refine :
  forall ownera ownerb ia ib new_ownera new_ownerb,
  Rkstate ka kb ->
  Rpid_opt (Some ownera) ownerb ->
  Rnat ia ib ->
  Rpid_opt (Some new_ownera) new_ownerb ->
  safe_refine Rkstate_with_err (exec_mon_transfer ka ownera ia new_ownera) (Mon_transfer kb ownerb ib new_ownerb).
Proof.
  prepare_corres exec_mon_transfer Mon_transfer.
  gen_corres; solve_corres.
Qed.

Theorem mon_derive_safe_refine :
  forall ownera ownerb ia ib csizea csizeb,
  Rkstate ka kb ->
  Rpid_opt (Some ownera) ownerb ->
  Rnat ia ib ->
  Rnat csizea csizeb ->
  safe_refine_opt Rkstate_with_err (exec_mon_derive ka ownera ia csizea) (Mon_derive kb ownerb ib ownerb csizeb).
Proof.
  prepare_corres exec_mon_derive Mon_derive.
  gen_corres; solve_corres.
Qed.

Theorem mon_revoke_safe_refine :
  forall ownera ownerb ia ib,
  Rkstate ka kb ->
  Rpid_opt (Some ownera) ownerb ->
  Rnat ia ib ->
  safe_refine_opt Rkstate_with_err (exec_mon_revoke' ka ownera ia) (Mon_revoke kb ownerb ib).
Proof.
  prepare_corres exec_mon_revoke' Mon_revoke Mon_revoke_once.
  gen_corres; solve_corres.
Qed.

End S3KRefine.
