From stdpp Require Import prelude.
From S3K.BarocqComp Require Import Barray.
From compcert Require Import Integers Coqlib.

Local Open Scope Z.


Ltac find_if:=
  match goal with
    | [ |- context[if ?X then _ else _] ] => destruct X eqn:?
  end.

Ltac find_if_in H :=
  match type of H with
    | context[if ?X then _ else _] => destruct X eqn:? in H
  end.

Ltac use H :=
  rewrite H; clear H; simpl.

Ltac assert_if b :=
  let H := fresh "H" in
  match goal with |- context[if ?e then _ else _]
    => assert (e = b) as H; only 2 : use H
  end.

(** Turn boolean connectives into propositions *)
Ltac bool_to_prop :=
  repeat rewrite ?Bool.andb_true_iff,
                 ?Bool.orb_true_iff,
                 ?Bool.negb_true_iff,
                 ?Bool.andb_false_iff,
                 ?Bool.orb_false_iff,
                 ?Bool.negb_false_iff.

Ltac bool_to_prop_in H :=
  repeat rewrite ?Bool.andb_true_iff,
                 ?Bool.orb_true_iff,
                 ?Bool.negb_true_iff,
                 ?Bool.andb_false_iff,
                 ?Bool.orb_false_iff,
                 ?Bool.negb_false_iff in H.

Ltac bool_to_prop_in_all :=
  repeat rewrite ?Bool.andb_true_iff,
                 ?Bool.orb_true_iff,
                 ?Bool.negb_true_iff,
                 ?Bool.andb_false_iff,
                 ?Bool.orb_false_iff,
                 ?Bool.negb_false_iff in *.

(*
Ltac solve_len :=
  assumption.

Ltac solve_get :=
  match goal with
  | [ |- context[get ?a ?i] ] =>
    let Hlen := fresh "Hlen" in
      match goal with
      | [ H : (U64.to_nat i < length a)%nat |- _ ] => solve_get_with H
      | _ => assert (U64.to_nat i < length a)%nat as Hlen by solve_len; solve_get_with Hlen
      | _ => assert (U64.to_nat i < length a)%nat as Hlen; only 2: solve_get_with Hlen
      end
  end.
  
(** Tactics dealing with Barocq get/set operations *)
Ltac solve_get_with H :=
  match goal with |- context[get ?a ?i] =>
  let res := fresh "res" in
  let Hres := fresh "Hres" in
  let v := fresh "v" in
  let Hv := fresh "Hv" in
  let Hok := fresh "Hok" in
    set (res:=(get a i)); assert (get a i = res) as Hres by reflexivity;
    destruct (barray_get _ _ _ Hres H) as [v [Hv Hok]];
    rewrite Hok; clear Hres Hok res; simpl
  end.

Ltac solve_set_with H :=
  match goal with |- context[set ?a ?i ?x] =>
    let a' := fresh "a" in
    rewrite barray_set by apply H; set (a':=set_rec a (U64.to_nat i) x); simpl
  end.

Ltac solve_get :=
  match goal with
  | [ |- context[get ?a ?i] ] =>
    let Hlen := fresh "Hlen" in
      match goal with
      | [ H : (U64.to_nat i < length a)%nat |- _ ] => solve_get_with H
      | _ => assert (U64.to_nat i < length a)%nat as Hlen by solve_len; solve_get_with Hlen
      | _ => assert (U64.to_nat i < length a)%nat as Hlen; only 2: solve_get_with Hlen
      end
  end.

Ltac solve_set :=
  match goal with
  | [ |- context[set ?a ?i ?x] ] =>
    match goal with
    | [ H : (U64.to_nat i < length a)%nat |- _ ] => solve_set_with H
    | _ => assert (U64.to_nat i < length a)%nat as Hlen by solve_len; solve_set_with Hlen
    | _ => assert (U64.to_nat i < length a)%nat as Hlen; only 2: solve_set_with Hlen
    end
  end.
 *)

(** Normalize Int64 comparisons into Z comparisons 
*)
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

Ltac norm_cmp_in H :=
  unfold Int64.cmpu, Int64.cmp in H;
  repeat rewrite ?negb_true_iff, ?negb_false_iff in H;
  repeat rewrite ?eq_true, ?eq_false, ?ltu_true, ?ltu_false in H.

Ltac norm_cmp_in_all :=
  unfold Int64.cmpu, Int64.cmp in *;
  repeat rewrite ?negb_true_iff, ?negb_false_iff in *;
  repeat rewrite ?eq_true, ?eq_false, ?ltu_true, ?ltu_false in *.

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

(*Hint Unfold U64.to_nat : rep_lia.*)

Ltac repr_elim :=
  try autorewrite with rep_lia;
  try autounfold with rep_lia;
  replace (Int64.repr 0) with Int64.zero by reflexivity;
  rewrite ?Int64.unsigned_zero;
  rewrite ?Int64.unsigned_repr by rep_lia.

Ltac repr_elim_in H :=
  try autorewrite with rep_lia in H;
  try autounfold with rep_lia in H;
  replace (Int64.repr 0) with Int64.zero in H by reflexivity;
  rewrite ?Int64.unsigned_zero in H;
  rewrite ?Int64.unsigned_repr in H by rep_lia.

Ltac repr_elim_in_all :=
  try autorewrite with rep_lia in *;
  try autounfold with rep_lia in *;
  replace (Int64.repr 0) with Int64.zero in * by reflexivity;
  rewrite ?Int64.unsigned_zero in *;
  rewrite ?Int64.unsigned_repr in * by rep_lia.

Ltac norm_in H :=
  bool_to_prop_in H; norm_cmp_in H; repr_elim_in H.

