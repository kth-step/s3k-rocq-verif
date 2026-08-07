From stdpp Require Import prelude.
From Ltac2 Require Ltac2.
From compcert Require Import Integers.
From S3K.ExecSem Require Import cap util exec config.
From S3K.Barocq Require Import S3K_ShallowR.
From S3K.Verif Require Import gen_tactics invariants barocq_aux refine_util refine_map.
From S3K.BarocqComp Require Import Option Barray Intop Utils.
From S3K.BarocqComp Require Import ShallowNotations.

(** * Tactics and hints for refinement proofs *)

(** ** Hints *)

(** Unfold hints *)
Create HintDb s3k_unfold.
(** Abstract helper functions to unfold *)
Hint Unfold cap_get : s3k_unfold.
Hint Unfold cap_owner_get : s3k_unfold.
Hint Unfold cap_idx_valid : s3k_unfold.

(** Barocq helper functions to unfold *)
Hint Unfold Mon_valid_access : s3k_unfold.

(** Hints for proof search. *)

(** s3k_inv is the hint database for backward reasoning about data
correspondence between the abstract and concrete models. *)
Create HintDb s3k_inv.

Hint Resolve safe_refine_opt_None safe_refine_opt_Some safe_refine_Some : s3k_inv.
Hint Resolve Rkstate_inv Rkstate_with_err_inv : s3k_inv.
Hint Resolve Rmon_table_set : s3k_inv.
Hint Resolve Rmon_table_inv_Rkstate Rtsl_table_inv_Rkstate Rptable_inv_Rkstate Rsched_inv_Rkstate : s3k_inv.
Hint Resolve Rmon_Some_inv Rmon_None_inv : s3k_inv.

Hint Extern 0 (Rpid_opt _ _) => reflexivity : s3k_inv.
Hint Extern 0 => progress simpl : s3k_inv.
(** Replace CapTable l with canonical form *)
Hint Extern 0 (Rmon_table (CapTable _) _) =>
  match goal with | [ H : _ = CapTable _ |- _ ] => rewrite <- H end
  : s3k_inv.
Hint Extern 0 (_ <> O) => lia : s3k_inv.

#[global] Opaque cap_set.

(** Hint database for arithmetic reasoning. *)
Create HintDb s3k_arith.

Hint Unfold Rnat fun_hrel ofun_hrel int64_to_nat nat_to_int64 : s3k_arith.
Hint Unfold Int64.add Int64.sub I64.of_u64 : s3k_arith.
Hint Unfold err_success : s3k_arith.
Hint Rewrite Int64.repr_unsigned : s3k_arith.

(** ** Tactics *)

Module ltac2_tactics.

Import Ltac2 ltac2_tactics.

(** Normalize length expressions into configured number. *)
Ltac2 norm_length1 () :=
  match! goal with
  | [h : ?tb.[?i <- ?v] = Some ?tb' |- context[length ?tb'] ] =>
    (* Barocq set doesn't change length. *)
    let h := Control.hyp h in rewrite (bset_length_same $tb $i $v $h)
  | [h : Rmon_table (CapTable ?ta) ?tb |- context[length ?tb]] =>
    (* Normalize concrete table size into abstract table size. *)
    let h := Control.hyp h in
    rewrite <- (Rmon_table_len_same $h)
  | [h : ctable_size (CapTable _) = _ |- _] =>
    (* Normalize capability table size into configured number. *)
    simpl in $h;
    let h := Control.hyp h in
    rewrite $h in *
  end.

Ltac2 Notation "norm_length" := repeat (norm_length1 ()).

(** Introduce range constraints for variables involved in goal. *)
Ltac2 forward_range1 () :=
  match! goal with
  | [ h : ?l !! ?ia = Some _ |- context[?ia]] =>
    (* Range for valid index *)
    let h := Control.hyp h in
    extend (lookup_lt_Some _ _ _ $h)
  | [ |- context[cfree ?c]] =>
    (* Range for capability field cfree - always <= table size if wellformed *)
    assert_if_new (cfree $c <= MON_SZ)%nat
  | [ |- context[csize ?c]] =>
    assert_if_new (csize $c <= MON_SZ)%nat
  | [ |- context[(cfree ?ci + cfree ?cj)%nat]] =>
      assert_if_new ($ci.(cfree) + $cj.(cfree) <= $ci.(csize))%nat
  | [ |- _] => extend mon_sz_upper_bound
  end.

Ltac2 Notation "forward_range" :=
  repeat (forward_range1 ()); norm_length.

(** Solve R correspondence using backward reasoning *)
Ltac2 solve_corres () :=
  eauto 22 with s3k_inv.

(** Derive finer correspondence results from the hypotheses. *)
Ltac2 forward_hyp_corres1 () :=
  match! goal with
  | [ h1 : Rpid_opt ?ova ?vb,
      h2 : Rpid_opt ?ova' ?vb' |- context[?vb] ] =>
      let h1 := Control.hyp h1 in
      let h2 := Control.hyp h2 in
      rewrite (Rpid_opt_inj $h1 $h2) in *
  end.

Ltac2 Notation "forward_hyp_corres" := repeat (forward_hyp_corres1 ()).

(** Solve arithmetic goal with CompCert integers. *)
Ltac2 solve_arith () :=
  debug_printf "Trying to solve arithmetic goal: %t" (Control.goal ());
  forward_range;
  forward_hyp_corres;
  ltac1:(autounfold with s3k_arith in *);
  ltac1:(autorewrite with s3k_arith in *);
  repr_elim;
  rep_lia.

(** Try solve correspondence goal t and return the hypothesis, may fail. *)
Ltac2 get_or_solve_corres (t : constr) : constr :=
  debug_printf "solving corres %t" t;
  let oh := List.find_opt (fun (_,_,ty) => Constr.equal t ty) (Control.hyps ()) in
  match oh with
  (* if in goal already *)
  | Some (h_ident, _, _) => Control.hyp h_ident
  (* try solve it if not *)
  | None => 
    let h := Fresh.in_goal @Hcorres in
    lazy_match! t with
    (* if arithmetic goal *)
    | Rnat _ _ => assert $t as $h by solve_arith ()
    | _ => assert $t as $h by solve_corres ()
    end;
    Control.hyp h
  end.

(** Case analysis on whether an abstract capability is physically deleted or not. *)
Ltac2 forward_abstract_opt_cap (t : constr) :=
  destruct $t eqn:? >
  [ (* Some case, introduce capability field correspondence.results. *)
    match! goal with
    | [ hget : ?tlookup = Some ?va,
        h : Rmon (Some ?va) ?vb |- _ ] =>
      Control.assert_true (Constr.equal t tlookup);
      let h := Control.hyp h in
      let h' := @HRmon_corres in
      pose proof (Rmon_Some_corres $h) as $h'; destruct_and? $h'
    end
  |
    (* None case *)
    (* Since in principle a system call should never touch a physically deleted
       capability, we can be sure that the concrete level must return invalid
       access. This is ensured since Int64.eq vb.(types_mon_t_owner) owner is alway
       false in this case. *)
    try (erewrite Rmon_None_corres by eauto)
  ].

(** Reason about Barocq list set success and simplify. *)
Ltac2 forward_concrete_map_set () :=
  match! goal with
  | [ h: ?tb.[?ib] = Some _ |- context[?tb.[?ib <- ?v]]] =>
    (* Rewrite the result of barocq set at the same index *)
    let h := Control.hyp h in
    let tb' := Fresh.in_goal @tb in
    let htb' := Fresh.in_goal @Htb in
    destruct (bget_Some_bset_Some $tb $ib $v $h) as [$tb' $htb'];
    let htb' := Control.hyp htb' in
    rewrite $htb'; simpl
  end.

(** Forward reasoning on abstract lookup failure case. *)
Ltac2 forward_abstract_lookup_None (h : constr) :=
  simpl;
  lazy_match! goal with
  | [ |- safe_refine_opt _ None _] =>
    (* If abstract model fails, holds vacuously by safe_refine_opt. *)
    auto with s3k_inv
  | [ |- _] =>
    (* Otherwise abstract model handles the lookup error, simplify in concrete. *)
    lazy_match! (Constr.type h) with ?ta !! ?ia = None =>
      match! goal with
      | [ |- context[?tb.[USIZE.of_u64 ?ib]]] =>
        let hi := get_or_solve_corres '(Rnat $ia $ib) in
        trivial_erewrite ?(mon_lookup_None_len _ _ $h $hi); simpl
      | [ |- _] => fail_with_msg "Found no correspondence for abstract lookup in concrete model."
      end
    end
  end.

(** Forward reasoning on abstract lookup success case. *)
Ltac2 forward_abstract_lookup_Some (h : constr) :=
  lazy_match! (Constr.type h) with ?ta !! ?ia = Some ?va =>
    match! goal with
    | [ |- context[?tb.[USIZE.of_u64 ?ib]]] =>
      (* Case for both index and table correspondence *)
      (* Solve table correspondence *)
      let htable := get_or_solve_corres '(Rmon_table (CapTable $ta) $tb) in
      (* Solve index correspondence *)
      let hi := get_or_solve_corres '(Rnat $ia $ib) in
      (* 1. Rewrite the result of barocq get *)
      let vb := Fresh.in_goal @vb in
      let hvb := Fresh.in_goal @Hvb in
      let hrmon := Fresh.in_goal @HRmon in
      destruct (mon_get_Some_corres $htable $hi $h) as [$vb [$hvb $hrmon]];
      let hvb:= Control.hyp hvb in
      trivial_erewrite ?($hvb), ?(mon_lookup_Some_len _ _ $h $hi); simpl;
      (* 2. Destruct abstract optional capability *)
      debug_printf "Case analysis on whether abstract capability is physically deleted or not ";
      Control.enter (fun _ => forward_abstract_opt_cap va);
      (* 3. Forward barocq set at the same index *)
      try (forward_concrete_map_set ())
    | [ |- context[?tb.[USIZE.of_u64 ?ib]]] =>
      (* Case for only index correspondence. Since barocq has in-place-update semantic,
         table may be different. Can still simplify for safe execution. *)
      debug_printf "trying to just solve hi: %t" '(Rnat $ia $ib); 
      let hi := get_or_solve_corres '(Rnat $ia $ib) in
      (* 1. Barocq get safe *)
      let hlen := Fresh.in_goal @Hlen in
      (*assert (length $ta = length $tb) as $hlen by solve_length ();*)
      assert (length $ta = length $tb) as $hlen by (norm_length; congruence);
      let hlen := Control.hyp hlen in
      let vb := Fresh.in_goal @vb in
      let hvb := Fresh.in_goal @Hvb in
      destruct (lookup_Some_bget_safe $ta $tb $h $hi $hlen) as [$vb $hvb];
      let hvb := Control.hyp hvb in
      rewrite ?($hvb); simpl;
      (* 2. Barocq set safe *)
      try (forward_concrete_map_set ())
    end
  end.

(** Case analysis on abstract lookup result h, h is hypothesis of form l !! i = v . *)
Ltac2 forward_abstract_lookup (h : constr) :=
  lazy_match! (Constr.type h) with
  | _ !! _ = Some _ => forward_abstract_lookup_Some h
  | _ !! _ = None => forward_abstract_lookup_None h
  end.

(** Solve concrete condition. *)
Ltac2 solve_concrete_cond () :=
  debug_printf "Trying to solve concrete condition: %t" (Control.goal ());
  (* normalize hypotheses *)
  destruct_and?; destruct_or?;
  forward_hyp_corres;
  (* normalize goal *)
  ltac1:(autounfold with s3k_arith in *);
  ltac1:(norm_bool_cmp);
  repr_elim;
  rep_lia.

(** Find head concrete condition and try simplifying it. *)
Ltac2 forward_concrete_cond () :=
  match! goal with
  | [ |- _ _ _ (if ?b then _ else _)] =>
    (* Try simplify the if branch *)
    let hcond := Fresh.in_goal @Hcond in
    first [
      assert ($b = true) as $hcond by solve_concrete_cond () |
      assert ($b = false) as $hcond by solve_concrete_cond () ];
    let hcond := Control.hyp hcond in
    rewrite! $hcond; simpl
  | [ |- _ ] => debug_printf "Failed to solve any concrete condition."
  end.
  
(** Find decision in abstract model, do case analysis and try simplifying and
synchronizing the concrete model. *)
Ltac2 forward_abstract () :=
  match! goal with
  | [ |- context[match ?t with  _ => _ end ] ] =>
      first [
        lazy_match! (Constr.type t) with
        (* Destruct cap table of single construtor CapTable *)
        | mon_table_t => destruct $t eqn:?; debug_printf "Getting rid of CapTable"
        | cap_table_t _  => destruct $t eqn:?; debug_printf "Getting rid of CapTable"
        end |
        lazy_match! t with
        |  ?l !! ?ia =>
          (* Destruct result of abstract lookup *)
            let h := Fresh.in_goal @Hlookup in
            debug_printf "Case analysis on capability table lookup";
            destruct $t eqn:$h; Control.enter (fun () => forward_abstract_lookup (Control.hyp h))
        | @decide ?p ?d =>
          (* Destruct abstract decision, also try derive facts for concrete level  *)
          destruct_decide (@decide $p $d); Control.enter (fun () => forward_concrete_cond () )
        end
      ]
  end.

End ltac2_tactics.

Import ltac2_tactics.

(** Finally wrap in Ltac1. *)

Ltac solve_arith := ltac2:(solve_arith ()).

Hint Extern 100 (Rnat _ _) => solve_arith : s3k_inv.
Hint Extern 10 (err_success _ = _) => solve_arith : s3k_inv.

Ltac forward_abstract := ltac2:(forward_abstract ()).

Ltac prepare_corres :=
 intros; autounfold with s3k_unfold.

Ltac gen_corres := repeat forward_abstract.

Ltac solve_corres := ltac2:(solve_corres ()).
