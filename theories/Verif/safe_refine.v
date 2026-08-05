From stdpp Require Import prelude.

Set Implicit Arguments.

(** * Refinement with safe execution *)
Section SafeRefine.

(** A: abstract type, B: concrete type *)
Variable A B : Type.

(** R: Refinement mapping *)
Variable R : A -> B -> Prop.

(** Concrete code is safe while preserving refinement mapping. *)
Definition safe_refine (a : A) (ob : option B) :=
  exists b, ob = Some b /\ R a b.

(** Concrete code is safe given that abstract code is safe, also maintaining
refinement mapping. *)
Definition safe_refine_opt (oa : option A) (ob : option B) :=
  forall a, oa = Some a -> exists b, ob = Some b /\ R a b.

Lemma safe_refine_opt_None : forall b, safe_refine_opt None b.
Proof. done. Qed.

Lemma safe_refine_opt_Some : forall a ob,
  safe_refine a ob ->
  safe_refine_opt (Some a) ob.
Proof. unfold safe_refine_opt; intros; by inv H0. Qed.

Lemma safe_refine_Some : forall a b,
  R a b ->
  safe_refine a (Some b).
Proof. unfold safe_refine; intros; by exists b. Qed.

End SafeRefine.

