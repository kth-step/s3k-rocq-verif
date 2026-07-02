From stdpp Require Import prelude.
From compcert Require Import Integers.
From S3K.ExecSem Require Import cap.
From S3K.Verif Require Import repr.
From S3K.Barocq Require Import S3K_ShallowR.
From S3K.BarocqComp Require Import Option Barray Intop Utils.
From S3K.BarocqComp Require Import ShallowNotations.
From RecordUpdate Require Import RecordUpdate.

Set Implicit Arguments.

Axiom mon_table_len :
  forall kb,
  length kb.(types_kstate_mon_table) = usize_to_nat Config_mon_table_size.

(* NOTE : true only when usize = int64 *)
Lemma nat_lt_iff_int64_ltu:
  forall x y,
  Int64.ltu x y = true <->
  (usize_to_nat x < usize_to_nat y)%nat. 
Proof.
Admitted.

(** Barocq Barray helper lemmas *)

Theorem barray_get {A} :
  forall (l : list A) (ia : nat) (ib : int64),
  Rnat ia ib ->
  l.[ib] = l !! ia.
Proof.
Admitted.

Theorem barray_get_Some {A} :
  forall (l : list A) (i : usize),
  (usize_to_nat i < length l)%nat ->
  exists v, l.[i] = Some v.
Proof.
Admitted.

Theorem barray_get_Some_cond {A} :
  forall (l : list A) (i : usize) v,
  l.[i] = Some v ->
  (usize_to_nat i < length l)%nat.
Proof.
Admitted.

Theorem barray_set_Some {A} :
  forall (l : list A) (i : usize) v,
  (usize_to_nat i < length l)%nat ->
  l.[i <- v] = Some (<[ usize_to_nat i := v ]> l).
Proof.
Admitted.

Theorem barray_set_Some' {A} :
  forall (l : list A) ia ib v,
  Rnat ia ib ->
  (ia < length l)%nat ->
  l.[ib <- v] = Some (<[ ia := v ]> l).
Proof.
Admitted.

Theorem barray_set_Some_cond {A} :
  forall (l l' : list A) i v,
  l.[i <- v] = Some l' ->
  (usize_to_nat i < length l)%nat.
Proof.
Admitted.

(* Should be improved *)
Ltac solve_len :=
  assumption.

Ltac solve_get_with H :=
  match goal with |- context[Barray.get ?a ?i] =>
    let v := fresh "v" in
    let Hv := fresh "Hv" in
    destruct (barray_get_Some a i H) as [v Hv]; rewrite Hv; simpl
  end.
  
Ltac solve_get :=
  match goal with
  | [ |- context[Barray.get ?a ?i] ] =>
    let Hlen := fresh "Hlen" in
    match goal with
    | [ H : (usize_to_nat i < length a)%nat |- _ ] => solve_get_with H
    | _ => assert (usize_to_nat i < length a)%nat as Hlen by solve_len; solve_get_with Hlen
    | _ => assert (usize_to_nat i < length a)%nat as Hlen; only 2: solve_get_with Hlen
    end
  end.

Ltac solve_set_with H :=
  match goal with
  | [ |- context[Barray.set ?a ?i ?v] ] =>
    rewrite (barray_set_Some a i v H); simpl
  end.

Ltac solve_set :=
  match goal with
  | [ |- context[Barray.set ?a ?i ?v] ] =>
    let Hlen := fresh "Hlen" in
    match goal with
    | [ H : (usize_to_nat i < length a)%nat |- _ ] => solve_set_with H
    | _ => assert (usize_to_nat i < length a)%nat as Hlen by solve_len; solve_set_with Hlen
    | _ => assert (usize_to_nat i < length a)%nat as Hlen; only 2: solve_set_with Hlen
    end
  end.

(*Ltac solve_set_in H :=
  match type of H with
  | context[Barray.set ?a ?i ?v] =>
    let Hlen := fresh "Hlen" in
    assert (usize_to_nat i < length a)%nat as Hlen by solve_len;
    rewrite (barray_set_Some' a i v Hlen) in H
  end.*)

(** ExecSem operations *)
 
(* Post condition for cap_owner_get,
   conditions in the Barocq layer should follow from these *)
Theorem cap_owner_get_Some :
  forall (A : Type) (t : cap_table_t A) p i v, cap_owner_get t p i = Some v ->
  cap_get t i = Some v /\ v.(cowner) = Some p.
Proof.
Admitted.

Theorem cap_owner_get_None {A} :
  forall (t : cap_table_t A) p i, cap_owner_get t p i = None ->
  cap_get t i = None \/ (exists v, cap_get t i = Some v /\ v.(cowner) <> Some p).
Proof.
Admitted.

(** Refinement relation results *)

Lemma Rmon_table_set :
  forall ta tb ia ib va vb,
  Rmon_table ta tb ->
  Rmon va vb ->
  ia = ib ->
  Rmon_table (cap_set ta (ia, va)) (<[ ib := vb ]> tb).
Proof.
Admitted.

Lemma Rmon_table_bget :
  forall ta tb ia ib va,
  Rmon_table ta tb ->
  Rnat ia ib ->
  cap_get ta ia = Some va ->
  exists vb, tb.[ib] = Some vb /\ Rmon (Some va) vb.
Proof.
Admitted.

Theorem Rmon_table_bset :
  forall ta tb ia ib va vb tb',
  Rmon_table ta tb ->
  Rmon va vb ->
  Rnat ia ib ->
  tb.[ib <- vb] = Some tb' ->
  Rmon_table (cap_set ta (ia, va)) tb'.
Proof.
Admitted.

Theorem set_owner_None_preserve_Rmon :
  forall mona monb,
  Rmon (Some mona) monb ->
  let monb' := monb <| types_mon_t_owner := 0 L|> in
  let mona' := mona <| (@cowner mon_t) := None |> in
  Rmon (Some mona') monb'.
Proof.
Admitted.

Lemma Rnat_lt :
  forall ia ib ja jb,
  Rnat ia ib ->
  Rnat ja jb ->
  (ia < ja)%nat -> Int64.ltu ib jb = true.
Proof.
Admitted.

Lemma Rpid_opt_eq :
  forall pa_opt pa pb pb',
  pa_opt = Some pa ->
  Rpid_opt pa_opt pb ->
  Rpid pa pb' ->
  pb = pb'.
Proof.
Admitted.

Lemma Rpid_opt_neq :
  forall pa_opt pa pb pb',
  pa_opt <> Some pa ->
  Rpid_opt pa_opt pb ->
  Rpid pa pb' ->
  pb <> pb'.
Proof.
Admitted.

Ltac break_bind :=
  lazymatch goal with
  | |- context[bind ?A] =>
    let Heq := fresh "Heq" in
    destruct A eqn:Heq; try discriminate
  end;
  simpl.


Ltac inv_all :=
  repeat match goal with
  | H : Some _ = Some _ |- _ => inv H
  | H : (_, _) = (_, _) |- _ => inv H
  | H : ret _ = Some _ |- _ => inv H
  end.


