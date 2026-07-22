From stdpp Require Import prelude.
From compcert Require Import Coqlib Integers.

(** * Tactics *)

(** Normalize Int64 comparisons into Z comparisons *)
Lemma ltu_true :
  forall x y, Int64.ltu x y = true <-> (Int64.unsigned x) < (Int64.unsigned y).
Proof.
  split; intros.
  - unfold Int64.ltu in H. destruct zlt in H; [ assumption | discriminate ].
  - unfold Int64.ltu. destruct zlt; [ reflexivity | contradiction ].
Qed.

Lemma ltu_false :
  forall x y, Int64.ltu x y = false  <-> (Int64.unsigned x) >= (Int64.unsigned y).
Proof.
  split; intros.
  - unfold Int64.ltu in H. destruct zlt in H; [ discriminate | assumption ].
  - unfold Int64.ltu. destruct zlt; [ contradiction | reflexivity ].
Qed.

Lemma eq_true :
  forall x y, Int64.eq x y = true <-> (Int64.unsigned x) = (Int64.unsigned y).
Proof.
  split; intros.
  - unfold Int64.eq in H. destruct zeq in H; [ assumption | discriminate ].
  - unfold Int64.eq. destruct zeq; [ reflexivity | contradiction ].
Qed.

Lemma eq_false :
  forall x y, Int64.eq x y = false <-> (Int64.unsigned x) <> (Int64.unsigned y).
Proof.
  split; intros.
  - unfold Int64.eq in H. destruct zeq in H; [ discriminate | assumption ].
  - unfold Int64.eq. destruct zeq; [ contradiction | reflexivity ].
Qed.

Ltac norm_cmp :=
  unfold Int64.cmpu, Int64.cmp;
  repeat rewrite ?negb_true_iff, ?negb_false_iff;
  repeat rewrite ?eq_true, ?eq_false, ?ltu_true, ?ltu_false.

Tactic Notation "norm_cmp" "in" hyp(H) :=
  unfold Int64.cmpu, Int64.cmp in H;
  repeat rewrite ?negb_true_iff, ?negb_false_iff in H;
  repeat rewrite ?eq_true, ?eq_false, ?ltu_true, ?ltu_false in H.

Tactic Notation "norm_cmp" "in" "*" :=
  repeat_on_hyps (fun H => norm_cmp in H); norm_cmp.

(** rep_lia from VST *)

Ltac Zground X :=
  match X with
  | Z0 => idtac
  | Zpos ?y => Zground y
  | Zneg ?y => Zground y 
  | xH => idtac
  | xO ?y => Zground y
  | xI ?y => Zground y
 end.

Ltac pose_const_equation X :=
 match goal with
 | H: X = ?Y |- _ => Zground Y
 | _ => let z := eval compute in X in 
            match z with context C [Archi.ptr64] =>
                       first [
                           unify Archi.ptr64 false; let u := context C [false] in let u := eval compute in u in change X with u in *
                          |unify Archi.ptr64 true; let u := context C [true] in let u := eval compute in u in change X with u in *
                      ]
              | _ => change X with z in *
            end
 end.

Ltac perhaps_post_const_equation X :=
 lazymatch goal with 
 | H: context [X] |- _ => pose_const_equation X
(* | H:= context [X] |- _ => pose_const_equation X *)
 | |- context [X] => pose_const_equation X
 | |- _ => idtac
 end.

Ltac pose_const_equations L :=
 match L with
 | ?X :: ?Y => perhaps_post_const_equation X; pose_const_equations Y
 | nil => idtac
 end.

Import ListNotations.

Ltac pose_standard_const_equations :=
pose_const_equations
  [
  Int.zwordsize; Int.modulus; Int.half_modulus; Int.max_unsigned; Int.max_signed; Int.min_signed;
  Int64.zwordsize; Int64.modulus; Int64.half_modulus; Int64.max_unsigned; Int64.max_signed; Int64.min_signed;
  Ptrofs.zwordsize; Ptrofs.modulus; Ptrofs.half_modulus; Ptrofs.max_unsigned; Ptrofs.max_signed; Ptrofs.min_signed;
  Byte.min_signed; Byte.max_signed; Byte.max_unsigned; Byte.modulus
  ];
 pose_const_equations [Int.wordsize; Int64.wordsize; Ptrofs.wordsize].

Ltac pose_lemma F A L :=
  match type of (L A) with ?T =>
     lazymatch goal with
      | H:  T |- _ => fail
      | H:  T /\ _ |- _ => fail
      | |- _ => pose proof (L A)
     end
  end.

Ltac pose_lemmas F L :=
 repeat
  match goal with
  | |- context [F ?A] => pose_lemma F A L
  | H: context [F ?A] |- _ => pose_lemma F A L
 end.

Ltac rep_lia_setup := 
 repeat match goal with
            | x := _ : ?T |- _ => lazymatch T with Z => fail | nat => fail | _ => clearbody x end
            end;
 zify;
  try autorewrite with rep_lia in *;
  try autounfold with rep_lia in *;
  pose_lemmas Byte.unsigned Byte.unsigned_range;
  pose_lemmas Byte.signed Byte.signed_range;
  pose_lemmas Int.unsigned Int.unsigned_range;
  pose_lemmas Int.signed Int.signed_range;
  pose_lemmas Int64.unsigned Int64.unsigned_range;
  pose_lemmas Int64.signed Int64.signed_range;
  pose_lemmas Ptrofs.unsigned Ptrofs.unsigned_range;
  pose_standard_const_equations.

Ltac rep_lia_setup2 := idtac.

Ltac rep_lia :=
   rep_lia_setup;
   rep_lia_setup2;
   lia.

(** Rewrite Int64.unsigned (Int64.repr z) into z *)

Ltac repr_elim :=
  rewrite ?Int64.unsigned_repr by rep_lia.

Tactic Notation "repr_elim" "in" hyp(H) :=
  rewrite ?Int64.unsigned_repr in H by rep_lia.

Tactic Notation "repr_elim" "in" "*" :=
  repeat_on_hyps (fun H => repr_elim in H); repr_elim.

