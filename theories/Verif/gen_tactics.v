From stdpp Require Import prelude.
From compcert Require Import Coqlib Integers.
From Ltac2 Require Ltac2.

(** * General tactics *)

Tactic Notation "case_match" "in" ident(H) :=
  match type of H with
  | context [ match ?x with _ => _ end ] => destruct x eqn:?
  end.

(** Rewrite boolean algebra into propositions. *)
Ltac norm_bool :=
  repeat rewrite
    ?negb_true_iff, ?negb_false_iff,
    ?orb_true_iff, ?orb_false_iff,
    ?andb_true_iff, ?andb_false_iff.

(** ** CompCert Integer arithmetic related tactics *)

(** Normalize Int64 comparisons into integer comparisons *)
Local Lemma ltu_true :
  forall x y, Int64.ltu x y = true <-> (Int64.unsigned x) < (Int64.unsigned y).
Proof.
  split; intros.
  - unfold Int64.ltu in H. destruct zlt in H; [ assumption | discriminate ].
  - unfold Int64.ltu. destruct zlt; [ reflexivity | contradiction ].
Qed.

Local Lemma ltu_false :
  forall x y, Int64.ltu x y = false  <-> (Int64.unsigned x) >= (Int64.unsigned y).
Proof.
  split; intros.
  - unfold Int64.ltu in H. destruct zlt in H; [ discriminate | assumption ].
  - unfold Int64.ltu. destruct zlt; [ contradiction | reflexivity ].
Qed.

Local Lemma eq_true :
  forall x y, Int64.eq x y = true <-> (Int64.unsigned x) = (Int64.unsigned y).
Proof.
  split; intros.
  - unfold Int64.eq in H. destruct zeq in H; [ assumption | discriminate ].
  - unfold Int64.eq. destruct zeq; [ reflexivity | contradiction ].
Qed.

Local Lemma eq_false :
  forall x y, Int64.eq x y = false <-> (Int64.unsigned x) <> (Int64.unsigned y).
Proof.
  split; intros.
  - unfold Int64.eq in H. destruct zeq in H; [ discriminate | assumption ].
  - unfold Int64.eq. destruct zeq; [ contradiction | reflexivity ].
Qed.

Ltac norm_cmp :=
  unfold Int64.cmpu, Int64.cmp;
  repeat rewrite ?eq_true, ?eq_false, ?ltu_true, ?ltu_false.

Tactic Notation "norm_cmp" "in" hyp(H) :=
  unfold Int64.cmpu, Int64.cmp in H;
  repeat rewrite ?eq_true, ?eq_false, ?ltu_true, ?ltu_false in H.

Tactic Notation "norm_cmp" "in" "*" :=
  repeat_on_hyps (fun H => norm_cmp in H); norm_cmp.

Ltac norm_bool_cmp := norm_bool; norm_cmp.

(** ** rep_lia from VST *)

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

(** ** Ltac2 utilities *)

Module ltac2_tactics.

Import Ltac2 Message.

(** use [Ltac2 Set ltac2_debug_flag := true.] to turn on debugging. *)
Ltac2 mutable ltac2_debug_flag := false.

Ltac2 Notation "debug_printf" fmt(format) :=
  Format.kfprintf
    (fun msg =>
       if ltac2_debug_flag
       then print msg
       else ())
    fmt.

Ltac2 fail_with_msg (s : string) := Control.backtrack_tactic_failure s.

Ltac2 Notation "lia" := ltac1:(lia).
Ltac2 Notation "rep_lia" := ltac1:(rep_lia).

Ltac2 Notation "destruct_decide" dec(constr) :=
  ltac1:(dec |- destruct_decide dec) (Ltac1.of_constr dec).

Ltac2 Notation "destruct_and" "?" h(opt(ident)) := 
  match h with
  | Some h => ltac1:(h |- destruct_and? h) (Ltac1.of_ident h)
  | None => ltac1:(destruct_and?)
  end.

Ltac2 Notation "destruct_or" "?" h(opt(ident)) :=
  match h with
  | Some h => ltac1:(h |- destruct_or? h) (Ltac1.of_ident h)
  | None => ltac1:(destruct_or?)
  end.

Ltac2 Notation "trivial_erewrite"
  rw(list1(rewriting, ","))
  cl(opt(clause))
  tac(opt(seq("by", thunk(tactic)))) :=
  unshelve (rewrite0 true rw cl tac); auto; Control.assert_true (Int.equal (Control.numgoals ()) 1).

Ltac2 has_hyp_of_type (ty : constr) : bool :=
  List.exist
    (fun (_, _, hyp_ty) => Constr.equal hyp_ty ty)
    (Control.hyps ()).

Ltac2 Notation "assert_if_new" t(open_constr) :=
  if has_hyp_of_type t then fail
  else assert $t by eauto.

Ltac2 pose_proof (id : ident option) (t : constr) :=
  match id with
  | Some id => pose ($id := $t); Std.clearbody [id]
  | None =>
    let h := Fresh.in_goal @H in
    pose ($h := $t); Std.clearbody [h]
  end.

Ltac2 Notation "pose" "proof" t(open_constr) id(opt(seq("as", ident))):= pose_proof id t.

Ltac2 extend (t : constr) :=
  if has_hyp_of_type (Constr.type t) then 
    fail
  else
    pose_proof None t.

Ltac2 Notation "extend" t(open_constr) := extend t.

(** Simplify Z <-> Int64 transformation. *)
Ltac2 repr_elim1 () :=
  match! goal with
  | [ |- context[Int64.unsigned (Int64.repr ?z)]] =>
    rewrite Int64.unsigned_repr with (z:=$z) by rep_lia
  | [ h : context[Int64.unsigned (Int64.repr ?z)] |- _ ] =>
    rewrite Int64.unsigned_repr with (z:=$z) in $h by rep_lia
  | [ |- Int64.repr _ = Int64.repr _] => f_equal
  end.

Ltac2 Notation "repr_elim" := repeat (repr_elim1 ()).

Ltac2 get_constr (x : Ltac1.t) :=
  Option.get (Ltac1.to_constr x).

Ltac2 get_constr_list (xs : Ltac1.t) :=
  let xs := Option.get (Ltac1.to_list xs) in
  List.map get_constr xs.

Ltac2 run_ltac1_on_constr (tac : Ltac1.t) (x : constr) :=
  Ltac1.apply tac [Ltac1.of_constr x] Ltac1.run.

Ltac2 iter_unfold (refs : constr list) :=
  List.iter (run_ltac1_on_constr ltac1val:(fun x => unfold x)) refs.

End ltac2_tactics.

Import ltac2_tactics.

Ltac repr_elim := ltac2:(repr_elim).
