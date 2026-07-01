From stdpp Require Import prelude.
From compcert Require Import Integers.
From S3K.Barocq Require Import S3K_ShallowR.
From S3K.ExecSem Require Import kstate cap ctx exec util.
From S3K.Verif Require Import repr tactics aux.
From S3K.BarocqComp Require Import Option Barray Intop Utils.
From S3K.BarocqComp Require Import ShallowNotations.
From RecordUpdate Require Import RecordUpdate.

Set Implicit Arguments.

(* Mon_valid_access safe execution theorem,
   with post condition, only one direction (b = true) is needed *)
Theorem mon_valid_access_safe :
  forall kb owner i,
  exists b, Mon_valid_access kb owner i = Some b /\
    (b = true -> (usize_to_nat i < length kb.(types_kstate_mon_table))%nat).
Proof.
  unfold Mon_valid_access.
  intros.
  find_if.
  - solve_get.
    + rewrite mon_table_len.
      apply nat_lt_iff_int64_ltu.
      assumption.
    + by eexists.
  - by eexists.
Qed.

(* TODO this is not helping
Hint Resolve Rkstate_equiv : mon.
Hint Resolve Rmon_equiv : mon.
 *)

(* Mon_valid_access is correct with regard to cap_owner_get,
   safe execution is implied. *)
Theorem mon_valid_access_safe_correct :
  forall kb ka ownera ownerb ia ib cap_opt,
  Rkstate ka kb ->
  Rpid ownera ownerb ->
  Rnat ia ib ->
  cap_owner_get ka.(kmon_tbl) ownera ia = cap_opt ->
  Mon_valid_access kb ownerb ib =
    Some (match cap_opt with
          | Some _ => true
          | None => false
          end).
Proof.
  intros until 3.
  unfold cap_owner_get, Mon_valid_access.
  case_match. (* cap_get *)
  - edestruct Rmon_table_bget as [vb [Hvb HRmonvb]]; eauto.
    eapply Rkstate_equiv; eauto.
    (* Need to get Int64.ltu ib Config_mon_table_size = false from Hvb,
       more generally, a tactic that finds the first conditional in the
       Barocq function and resolves its result from the hypotheses *)
    replace (Int64.ltu ib Config_mon_table_size) with true; cycle 1.
    { apply barray_get_Some_cond in Hvb. 
      rewrite mon_table_len in Hvb.
      symmetry; by apply nat_lt_iff_int64_ltu. }
      rewrite Hvb; simpl.
    case_decide. (* owner equal? *)
    + intros.
      subst.
      f_equal.
      replace (types_mon_t_owner vb) with ownerb.
      apply Int64.eq_true.
      { symmetry. eapply Rpid_opt_eq; eauto. apply Rmon_equiv. auto. }
    + intros. subst. f_equal.
      apply Int64.eq_false.
      eapply Rpid_opt_neq; eauto. apply Rmon_equiv. auto.
  - replace (Int64.ltu ib Config_mon_table_size) with false; cycle 1.
    { admit. (* similar process as above *) }
    intros.
    f_equal.
    by subst.
Admitted.

Theorem mon_delete_safe :
  forall kb ownerb ib,
  exists kb', Mon_delete kb ownerb ib = Some kb'.
Proof.
  unfold Mon_delete.
  intros.
  edestruct mon_valid_access_safe as [b [Hb Hva]].
  rewrite Hb.
  destruct b.
  - specialize (Hva eq_refl).
    solve_get.
    solve_set.
    by eexists.
  - by eexists.
Qed.

Opaque cap_set.

Theorem mon_delete_corres :
  forall ka kb ownera ownerb ia ib ka' kb' erra,
  Rkstate ka kb ->
  Rpid ownera ownerb ->
  Rnat ia ib ->
  exec_mon_delete ka ownera ia = (ka', erra) ->
  Mon_delete kb ownerb ib = Some kb' ->
  Rkstate_with_err (ka', erra) kb'.
Proof.
  unfold exec_mon_delete, Mon_delete.
  intros until 3.
  case_match. (* case analysis on result of cap_owner_get *)
  - erewrite mon_valid_access_safe_correct by eauto.
    simpl.
    (* post conditions for cap_owner_get ... = Some x *)
    edestruct cap_owner_get_Some; eauto.
    (* consequences in Barocq of the above post conditions *)
    edestruct Rmon_table_bget as [vb [Hvb HRmon]]; eauto.
    { apply Rkstate_equiv; eauto. }
    rewrite Hvb; simpl.
    (* Barray set operation guaranteed to succeed *)
    break_bind.
    intros.
    inv_all.
    apply Rkstate_with_err_equiv.
    split.
    + apply Rkstate_equiv.
      apply Rkstate_equiv in H.
      simpl.
      intuition.
      eapply Rmon_table_bset; eauto.
      apply set_owner_None_preserve_Rmon; auto.
    + done.
  - (* cap_owner_get = None *)
    erewrite mon_valid_access_safe_correct by eauto.
    simpl.
    intros.
    inv_all.
    apply Rkstate_with_err_equiv.
    split.
    + done.
    + admit. (* FIXME this is just because errcode is incorrect for now ... *)
Admitted.

Theorem mon_delete_safe_corres :
  forall ka kb ownera ownerb ia ib ka' erra,
    Rkstate ka kb ->
    Rpid ownera ownerb ->
    Rnat ia ib ->
    exec_mon_delete ka ownera ia = (ka', erra) ->
    (exists kb', Mon_delete kb ownerb ib = Some kb' /\
      Rkstate_with_err (ka', erra) kb').
Proof.
  intros. 
  edestruct mon_delete_safe as [kb' Hkb'].
  rewrite Hkb'.
  eexists.
  split.
  - reflexivity.
  - eapply mon_delete_corres; eauto.
Qed.

(* Alternatively, one can prove mon_delete_safe_corres in one shot *)
Theorem mon_delete_safe_corres' :
  forall ka kb ownera ownerb ia ib ka' erra,
    Rkstate ka kb ->
    Rpid ownera ownerb ->
    Rnat ia ib ->
    exec_mon_delete ka ownera ia = (ka', erra) ->
    (exists kb', Mon_delete kb ownerb ib = Some kb' /\
      Rkstate_with_err (ka', erra) kb').
Proof.
Admitted.

