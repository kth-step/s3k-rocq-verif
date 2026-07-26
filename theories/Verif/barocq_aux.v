From stdpp Require Import prelude.
From compcert Require Import Integers.
From S3K.BarocqComp Require Import Intop Barray.
From S3K.BarocqComp Require Import ShallowNotations.
From S3K.Verif Require Import tactics.
From VST Require Import Zlist.

Set Implicit Arguments.

(** * Barray helper lemmas  *)

(** Usize integer (architecture specific) to natural number. *)
Definition usize_to_nat (i : usize) : nat := Z.to_nat (USIZE.to_Z i).

Section Barray.

Variable A : Type.

Lemma bget_lookup :
  forall (t : list A) i, t.[i] = t !! (usize_to_nat i).
Proof.
  intros.
  unfold get, usize_to_nat, USIZE.to_Z.
  set (z := Intsize.unsigned i).
  assert (0 <= z) by rep_lia.
  rewrite <- (Z2Nat.id z H).
  rewrite Nat2Z.id.
  generalize (Z.to_nat z) as n.
  clear z H.
  revert t.
  induction t.
  - reflexivity.
  - destruct n.
    + reflexivity.
    + simpl; rewrite <- Nat2Z.inj_pred; [ done | by lia ].
Qed.

Lemma valid_index_true_length (t : list A) i :
  valid_index t i = true -> (usize_to_nat i < length t)%nat.
Proof.
  intros.
  unfold valid_index in H.
  apply Z.ltb_lt in H.
  change Barray.Zlength with Zlength in H.
  rewrite <- ZtoNat_Zlength.
  unfold usize_to_nat, USIZE.to_Z.
  rep_lia.
Qed.

Lemma bget_Some :
  forall (t : list A) i,
  t.[i] <> None <-> (usize_to_nat i < length t)%nat.
Proof.
  intros.
  unfold get, usize_to_nat, USIZE.to_Z.
  set (z := Intsize.unsigned i) in *.
  assert (0 <= z) by rep_lia.
  rewrite ZlistPlus.list_nth_z_Some.
  rewrite <- ZtoNat_Zlength.
  lia.
Qed.

(** TODO this one is tricky *)
Lemma bset_Some_insert :
  forall (t t' : list A) i v,
  t.[i <- v] = Some t' ->
  t' = <[ usize_to_nat i := v ]> t.
Proof.
  (* setSPEC is insufficient for this proof since it only specifies
     indices within the usize range are unchanged. *)
  intros.
  unfold set in H; case_match; try discriminate.
  pose proof valid_index_true_length _ _ H0.
  inv H.
  unfold usize_to_nat, USIZE.to_Z in *.
  set (z := Intsize.unsigned i) in *.
  assert (0 <= z) by rep_lia.
  rewrite <- (Z2Nat.id z H).
  rewrite Nat2Z.id.
  set (n := Z.to_nat z) in *.
  apply list_eq.
  intros n'.
  assert (n' < n \/ n' = n \/ n < n')%nat by lia.
  destruct_or?.
  - (* n' < n *)
Admitted.

Lemma bget_Some_bset_Some :
  forall (t : list A) i v v',
  t.[i] = Some v ->
  exists t', t.[i <- v'] = Some t'.
Proof.
Admitted.


Lemma bset_length :
  forall (t : list A) i v t',
  t.[i <- v] = Some t' ->
  length t' = length t.
Proof.
  intros.
  rewrite (bset_Some_insert _ _ _ H).
  apply length_insert.
Qed.
End Barray.

