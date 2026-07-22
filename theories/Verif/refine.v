From stdpp Require Import prelude.
From compcert Require Import Integers.
From RecordUpdate Require Import RecordUpdate.
From S3K.Barocq Require Import S3K_ShallowR.
From S3K.ExecSem Require Import kstate cap ctx exec util config.
From S3K.Verif Require Import repr barocq_aux tactics.
From S3K.BarocqComp Require Import Option Barray Intop Utils.
From S3K.BarocqComp Require Import ShallowNotations.

Set Implicit Arguments.

(** * Refinement proofs *)

(** ** Refinement with safe execution *)
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

(** ** Hints and tactics *)

From Ltac2 Require Import Ltac2 Printf.

Create HintDb s3k_unfold.
(** Abstract helper functions to unfold *)
Hint Unfold cap_get : s3k_unfold.
Hint Unfold cap_owner_get : s3k_unfold.

(** Barocq helper functions to unfold *)
Hint Unfold Mon_valid_access : s3k_unfold.

(** Hint database for backward reasoning about data correspondence between
the abstract and concrete models. *)
Create HintDb s3k_inv.

Hint Resolve safe_refine_opt_None safe_refine_opt_Some safe_refine_Some : s3k_inv.
Hint Resolve Rkstate_inv Rkstate_with_err_inv : s3k_inv.
Hint Resolve Rmon_table_set Rmon_set_owner : s3k_inv.
Hint Resolve Rmon_table_inv_Rkstate Rtsl_table_inv_Rkstate Rptable_inv_Rkstate : s3k_inv.

Hint Extern 10 (Rpid_opt _ _) => reflexivity : s3k_inv.
Hint Extern 10 (_ = _) => reflexivity : s3k_inv.
Hint Extern 1 (Rmon_table _ _) => progress simpl : s3k_inv.
Hint Extern 1 (Rtsl_table _ _) => progress simpl : s3k_inv.
Hint Extern 1 (Rptable _ _) => progress simpl : s3k_inv.
(** Replace CapTable l with canonical form *)
Hint Extern 1 (Rmon_table (CapTable _) _) =>
  match! goal with | [ h : _ = CapTable _ |- _ ] => let h := Control.hyp h in rewrite <- $h end
  : s3k_inv.

Opaque cap_set.

Ltac2 fail_with_msg (s : string) := Control.backtrack_tactic_failure s.

Ltac2 Notation "trivial_erewrite"
  rw(list1(rewriting, ","))
  cl(opt(clause))
  tac(opt(seq("by", thunk(tactic)))) :=
  unshelve (rewrite0 true rw cl tac); auto; Control.assert_true (Int.equal (Control.numgoals ()) 1).

(** Solve R correspondence using backward reasoning *)
Ltac2 solve_corres () :=
  eauto 15 with s3k_inv.

(* Try solve correspondence term t and return the hypothesis, may fail. *)
Ltac2 get_or_solve_corres (t : constr) : constr :=
  printf "solving %t" t;
  let oh := List.find_opt (fun (_,_,ty) => Constr.equal t ty) (Control.hyps ()) in
  match oh with
  (* if in goal already *)
  | Some (h_ident, _, _) => Control.hyp h_ident
  (* try solve it if not *)
  | None => 
    let h := Fresh.in_goal @HR in
    assert $t as $h by solve_corres () ; printf "solved"; Control.hyp h
  end.

(** Case analysis on whether an abstract capability is physically deleted or not. *)
Ltac2 forward_abstract_opt_cap (t : constr) :=
  destruct $t >
  [ (* Some case, do nothing. *)
    ()
  |
    (* None case *)
    (* Since in principle a system call should never touch a physically deleted
       capability, we can be sure that the concrete level must return invalid
       access. This is ensured since Int64.eq vb.(types_mon_t_owner) owner is alway
       false in this case. *)
    erewrite Rmon_None_corres by eauto
  ].

(* Forward reasoning on the result of abstract capability lookup,
derive the corresponding conditions in the concrete model. *)
Ltac2 forward_abstract_lookup (h : constr) :=
  lazy_match! (Constr.type h) with
  | ?ta !! ?ia = ?ova =>
    (* find corresponding tb.[ib] in the concrete layer *)
    lazy_match! goal with
    | [ |- context[?tb.[USIZE.of_u64 ?ib]]] =>
      (* try solve R ta tb and R ia ib *)
      let htable := get_or_solve_corres '(Rmon_table (CapTable $ta) $tb) in
      let hi := get_or_solve_corres '(Rnat $ia $ib) in
      lazy_match! ova with
      (* if abstract lookup returns Some *)
      | Some ?va =>
        let vb := Fresh.in_goal @vb in
        let hvb := Fresh.in_goal @Hvb in
        let hrmon := Fresh.in_goal @HRmon in
        destruct (mon_get_Some_corres $htable $hi $h) as [$vb [$hvb $hrmon]];
        printf "destructed";
        let hvb:= Control.hyp hvb in
        (* Rewrite the result of barocq get *)
        trivial_erewrite ?($hvb), ?(mon_lookup_Some_len _ _ $h $hi); simpl;
        (* destruct abstract optional capability *)
        printf "Case analysis on whether abstract capability is physically deleted or not ";
        Control.enter (fun _ => forward_abstract_opt_cap va)
      (* if abstract lookup returns None *)
      | None =>
        (* If abstract model fails, holds vacuously.
           Otherwise abstract model handles the lookup error, simplify in concrete. *)
        trivial_erewrite ?(mon_lookup_None_len _ _ $h $hi); simpl; auto with s3k_inv
      end
    | [ |- _] => fail_with_msg "Found no correspondence for abstract lookup in concrete model."
    end
  end.

(** Derive finer correspondence results from the hypotheses. *)
Ltac2 forward_corres () :=
  match! goal with
  | [ h : Rmon (Some ?va) ?vb |- context[?vb] ] =>
      apply Rmon_Some_corres in $h; ltac1:(h |- destruct_and? h) (Ltac1.of_ident h)
  | [ h : Rnat ?va ?vb |- context[?vb] ] =>
      unfold Rnat, fun_hrel in $h
  | [ h1 : Rpid_opt ?ova ?vb,
      h2 : Rpid_opt ?ova' ?vb' |- context[?vb] ] =>
      let h1 := Control.hyp h1 in
      let h2 := Control.hyp h2 in
      rewrite (Rpid_opt_inj $h1 $h2) in *
  end.

(** Solve concrete condition. *)
Ltac2 solve_concrete_cond () :=
  printf "Trying to solve concrete condition: %t" (Control.goal ());
  repeat (forward_corres ());
  unfold int64_to_nat in *;
  ltac1:(norm_cmp);
  ltac1:(rep_lia).

(** Find head concrete condition and try simplifying it. *)
Ltac2 forward_concrete_cond () :=
  match! goal with
  | [ |- safe_refine _ _ (if ?b then _ else _)] =>
    (* Try simplify the if branch *)
    let hcond := Fresh.in_goal @Hcond in
    first [
      assert ($b = true) as $hcond by solve_concrete_cond () |
      assert ($b = false) as $hcond by solve_concrete_cond () ];
    let hcond := Control.hyp hcond in
    rewrite! $hcond; simpl
  | [ |- _ ] => printf "Failed to solve any concrete condition."
  end.

(** Reason Barocq set success and simplify. *)
Ltac2 forward_concrete_map_set () :=
  lazy_match! goal with
  | [ h: ?tb.[?ib] = Some _ |- context[?tb.[?ib <- ?v]]] =>
    (* Rewrite the result of barocq set at the same index *)
    let h := Control.hyp h in
    let tb' := Fresh.in_goal @tb in
    let htb' := Fresh.in_goal @Htb in
    destruct (bget_Some_bset_Some $tb $ib $v $h) as [$tb' $htb'];
    let htb' := Control.hyp htb' in
    rewrite $htb'; simpl
  end.
  
(** Find decision in abstract model, do case analysis and try simplifying and
synchronizing the concrete model. *)
Ltac2 forward_abstract () :=
  match! goal with
  | [ |- context[match ?t with  _ => _ end ] ] =>
      first [
        lazy_match! (Constr.type t) with
        (* Destruct cap table of single construtor CapTable *)
        | mon_table_t => destruct $t eqn:?; printf "Getting rid of CapTable"
        end |
        (* Destruct result of table get *)
        lazy_match! t with
          ?l !! ?ia =>
            let h := Fresh.in_goal @Hlookup in
            printf "Case analysis on capability table lookup";
            destruct $t eqn:$h; Control.enter (fun () => forward_abstract_lookup (Control.hyp h))
        end |
        (* Find decide P *)
        ltac1:(case_decide); Control.enter (fun () => forward_concrete_cond () )
      ]
  end.


(** ** Refinement proofs for capability operations. *)

Section S3KRefine.

Variable ka : kstate_t.
Variable kb : Types_kstate.

(** This should be evident from abstract kernel well-formedness, however
since it's not ported yet use hypothesis for now. *)
Hypothesis mon_table_size : ctable_size ka.(kmon_tbl) = MON_SZ.

Theorem mon_delele_safe_refine :
  forall ownera ownerb ia ib,
  Rkstate ka kb ->
  Rpid_opt (Some ownera) ownerb ->
  Rnat ia ib ->
  safe_refine Rkstate_with_err (exec_mon_delete ka ownera ia) (Mon_delete kb ownerb ib).
Proof.
  intros.
  unfold exec_mon_delete, Mon_delete.
  ltac1:(autounfold with s3k_unfold).
  repeat (forward_abstract ()).
  forward_concrete_map_set ().
  all: solve_corres ().
Qed.

Theorem mon_transfer_safe_refine :
  forall ownera ownerb ia ib new_ownera new_ownerb,
  Rkstate ka kb ->
  Rpid_opt (Some ownera) ownerb ->
  Rnat ia ib ->
  Rpid_opt (Some new_ownera) new_ownerb ->
  safe_refine Rkstate_with_err (exec_mon_transfer ka ownera ia new_ownera) (Mon_transfer kb ownerb ib new_ownerb).
Proof.
  intros.
  unfold exec_mon_transfer, Mon_transfer.
  ltac1:(autounfold with s3k_unfold).
  repeat (forward_abstract ()).
  forward_concrete_map_set ().
  all: solve_corres ().
Qed.

End S3KRefine.

