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

(** Barocq list get lemmas. *)
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

Lemma bget_Some_lt :
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

(** Barocq list set lemmas. *)

Lemma valid_index_true_lt (t : list A) i :
  valid_index t i = true <-> (usize_to_nat i < length t)%nat.
Proof.
  unfold valid_index, Barray.Zlength, usize_to_nat, USIZE.to_Z.
  rewrite <- ZtoNat_Zlength.
  rep_lia.
Qed.

(* Credit: Karl Palmskog. *)
Lemma bset_Some_insert :
  forall (t t' : list A) i v,
  t.[i <- v] = Some t' ->
  t' = <[ usize_to_nat i := v ]> t.
Proof.
  intros.
  unfold set in H; case_match; try discriminate.
  apply valid_index_true_lt in H0.
  inv H.
  rewrite insert_take_drop; last done.
  assert (Htake: sublist 0 (Intsize.unsigned i) t = take (usize_to_nat i) t). {
    by rewrite sublist_firstn.
  }
  assert (Hdrop: sublist (Intsize.unsigned i + 1) (Barray.Zlength t) t =
   drop (S (usize_to_nat i)) t). {
    rewrite sublist_skip; last by rep_lia.
    unfold usize_to_nat, USIZE.to_Z.
    repeat f_equal; rep_lia.
  }
  by rewrite Htake, Hdrop.
Qed.

Lemma bget_Some_bset_Some :
  forall (t : list A) i v v',
  t.[i] = Some v ->
  exists t', t.[i <- v'] = Some t'.
Proof.
  intros.
  assert (Hnone: t.[i] <> None) by congruence.
  apply bget_Some_lt in Hnone.
  apply valid_index_true_lt in Hnone.
  unfold set.
  eexists.
  by rewrite Hnone.
Qed.

Lemma bset_length_same :
  forall (t : list A) i v t',
  t.[i <- v] = Some t' ->
  length t' = length t.
Proof.
  intros.
  rewrite (bset_Some_insert _ _ _ H).
  apply length_insert.
Qed.

End Barray.

