From stdpp Require Import prelude.
From RecordUpdate Require Import RecordUpdate.
From compcert Require Import Integers.
From S3K.ExecSem Require Import kstate cap exec.
From S3K.Verif Require Import gen_tactics.

(** * Definitions bridging the concrete and abstract semantics *)

(** [exec_mon_revoke'] mimics the in-place update semantics at the concrete level,
which works better with automated refinement. We prove it is equivalent to [exec_mon_revoke]
under well-formedness. *)
Definition exec_mon_revoke' (kstate : kstate_t) (owner : nat) (i : nat) : option (kstate_t * int64) :=
  match cap_owner_get kstate.(kmon_tbl) owner i with
  | None => Some (kstate, err_invalid_access)
  | Some ci =>
    if decide (ci.(cfree) < ci.(csize)) then
      let j := i + ci.(cfree) in
      match cap_get kstate.(kmon_tbl) j with
      | None => None
      | Some cj =>
        let ci' := ci <| (@cfree mon_t) := ci.(cfree) + cj.(cfree) |> in
        let kmon_tbl' := cap_set kstate.(kmon_tbl) (i, (Some ci')) in
        match cap_get kmon_tbl' j with
        | None => None
        | Some cj =>
          let kmon_tbl'' := cap_set kmon_tbl' (j, None) in
          let kstate' := kstate <| kmon_tbl := kmon_tbl'' |> in
          Some (kstate', err_success (ci'.(csize) - ci'.(cfree)))
        end
      end
    else 
      Some (kstate, err_success 0)
  end.

Section Bridge.

(** ** Equivalence proofs *)

Variable k : kstate_t.

Hypothesis cfree_gt_0 :
  forall i v, cap_get k.(kmon_tbl) i = Some v ->
  v.(cfree) > 0.

Theorem mon_revoke_bridge :
  forall owner i,
  exec_mon_revoke' k owner i = exec_mon_revoke k owner i.
Proof.
  intros.
  unfold exec_mon_revoke, exec_mon_revoke'.
  repeat case_match; try reflexivity.
  unfold cap_set in H2.
  case_match in H2.
  simpl in H2.
  rewrite list_lookup_insert_ne in H2.
  - by simpl in H1; simplify_eq.
  - unfold cap_owner_get in H.
    repeat case_match in H; try discriminate.
    simplify_eq.
    apply cfree_gt_0 in Heqo.
    by lia.
Qed.

End Bridge.
