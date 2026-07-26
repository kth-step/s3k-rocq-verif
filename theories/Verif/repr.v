From stdpp Require Import prelude.
From compcert Require Import Integers.
From S3K.Barocq Require Import S3K_ShallowR.
From S3K.ExecSem Require Import kstate cap ctx exec util proc sched config.
From S3K.BarocqComp Require Import Option Barray Intop Utils.
From S3K.BarocqComp Require Import ShallowNotations.
From S3K.Verif Require Import barocq_aux tactics.
From RecordUpdate Require Import RecordUpdate.

Import IntopNotations.

Set Implicit Arguments.

(** * Refinement mapping definitions. *)

(** [a] [b] are related by total specification function [f]. *)
Definition fun_hrel {A} {B} (f : B -> A) : A -> B -> Prop :=
  fun a b => f b = a.

(** [a] [b] are related by partial specification function [f]. *)
Definition ofun_hrel {A} {B} (f : B -> option A) : A -> B -> Prop :=
  fun a b => f b = Some a.

(** Int64 integer to abstract process ID. 0UL encodes empty PID. *)
Definition int64_to_pid (i : int64) : option nat :=
  if Int64.eq i 0UL then None else Some ((int64_to_nat i) - 1)%nat.

(** Partial mapping from capability fields to a capability slot (may be empty).
Disallow the case where [cfree] is zero while [owner] is not [None].
Essentially this is encoding one of the well-formedness properties, however
it is necessary since otherwise concrete capability delete operation could physically
delete a capability. *)
Definition mk_cap_opt {A} (owner : option nat) (free size : nat) (data : A) : option (option (cap_t A)) :=
  match free with
  | O => match owner with
         | None => Some None (* physically deleted *)
         | Some _ => None (* Invalid state, when owner exists, cfree must be greater than 0 *)
         end
  | S _ => Some
             (Some {| cowner := owner;
                      cfree := free;
                      csize := size;
                      cdata := data; |})
  end.

(** Mappings from concrete capability to abstract capability. *)
Definition tsl_up (tsl : Types_tsl_t) : option (option (cap_t tsl_t)) :=
  let owner := int64_to_pid tsl.(types_tsl_t_owner) in
  let free := int64_to_nat tsl.(types_tsl_t_cfree) in
  let size := int64_to_nat tsl.(types_tsl_t_csize) in
  let data := {| thart := int64_to_nat tsl.(types_tsl_t_hart);
                 tbase := int64_to_nat tsl.(types_tsl_t_base);
                 tsize := int64_to_nat tsl.(types_tsl_t_size);
                 tfree := int64_to_nat tsl.(types_tsl_t_free); |} in
  mk_cap_opt owner free size data.

Definition mon_up (mon : Types_mon_t) : option (option (cap_t mon_t)) :=
  pid ← int64_to_pid mon.(types_mon_t_pid);
  let owner := int64_to_pid mon.(types_mon_t_owner) in
  let free := int64_to_nat mon.(types_mon_t_cfree) in
  let size := int64_to_nat mon.(types_mon_t_csize) in
  let data := {| mpid := pid; |} in
  mk_cap_opt owner free size data.

(** Mappings from concrete capability table to abstract capability table.
Using stdpp list monad operation [mapM]:
   https://plv.mpi-sws.org/coqdoc/stdpp/stdpp.list_monad.html *)
Definition tsl_table_up (l : list Types_tsl_t) : option tsl_table_t :=
  tsl_table ← mapM tsl_up l; mret (CapTable tsl_table).

Definition mon_table_up (l : list Types_mon_t) : option mon_table_t :=
  mon_table ← mapM mon_up l; mret (CapTable mon_table).

(* TODO complete refinement mappings *)
Parameter mem_up : Types_mem_t -> mem_t.

Definition mem_table_up := map mem_up.
Parameter some_mem_table : mem_table_t.


(** Process control block  mappings. *)
Parameter regs_up : list int64 -> regs_t.
Parameter pmp_up : Types_pmp_t -> pmp_t.
(** psuspend and busy flag *)
Parameter pstate_to_flags : int64 -> (bool * bool).

Definition proc_up (p : Types_proc_t) : proc_t :=
  {| pregs := regs_up p.(types_proc_t_regs);
     ppmp := pmp_up p.(types_proc_t_pmp);
     psuspend := fst (pstate_to_flags p.(types_proc_t_state)); |}.

Definition ptable_up := map proc_up.

(** Scheduler mappings. *)
Parameter some_sched : sched_t.

Definition kstate_up (k : Types_kstate) : option kstate_t :=
  mon_table ← mon_table_up k.(types_kstate_mon_table);
  tsl_table ← tsl_table_up k.(types_kstate_tsl_table);
  mret {|
    kptable := ptable_up k.(types_kstate_procs);
    ktsl_tbl := tsl_table;
    kmon_tbl := mon_table;
    kmem_tbl := some_mem_table;
    ksched := some_sched;
  |}.

Definition kstate_to_kstate_err (k : Types_kstate) : option (kstate_t * int64) :=
  k' ← kstate_up k; mret (k', k.(types_kstate_errcode)).

(** Relational version of refinement mappings. *)
Definition Rnat : nat -> int64 -> Prop := fun_hrel int64_to_nat.

Definition Rpid : nat -> int64 -> Prop := ofun_hrel int64_to_pid.

Definition Rpid_opt : option nat -> int64 -> Prop := fun_hrel int64_to_pid.

Definition Rtsl := ofun_hrel tsl_up.

Definition Rmon := ofun_hrel mon_up.

Definition Rtsl_table := ofun_hrel tsl_table_up.

Definition Rmon_table := ofun_hrel mon_table_up.

Definition Rptable := fun_hrel ptable_up.

Parameter kstate_to_ctx : Types_kstate -> ctx_t.

Definition Rctx := fun_hrel kstate_to_ctx.

Definition Rkstate := ofun_hrel kstate_up.

Definition Rkstate_with_err := ofun_hrel kstate_to_kstate_err.

Create HintDb s3k_repr_unfold.
Hint Unfold mbind option_bind : s3k_repr_unfold.
Hint Unfold fun_hrel ofun_hrel : s3k_repr_unfold.
Hint Unfold kstate_up kstate_to_kstate_err : s3k_repr_unfold.
Hint Unfold Rtsl_table Rmon_table Rptable Rctx Rkstate Rkstate_with_err : s3k_repr_unfold.

(** ** Helper lemmas *)

(** Lemmas used for backward reasoning. *)
(* FIXME this is ignoring memory table and scheduler for now. *)
Lemma Rkstate_inv :
  forall ka kb,
  Rmon_table ka.(kmon_tbl) kb.(types_kstate_mon_table) ->
  Rtsl_table ka.(ktsl_tbl) kb.(types_kstate_tsl_table) ->
  Rptable ka.(kptable) kb.(types_kstate_procs) ->
  Rkstate ka kb.
Proof.
  autounfold with s3k_repr_unfold.
  intros.
  rewrite H0, H, H1.
Admitted.

Lemma Rmon_table_inv_Rkstate :
  forall ka kb, Rkstate ka kb ->
  Rmon_table ka.(kmon_tbl) kb.(types_kstate_mon_table).
Proof.
  autounfold with s3k_repr_unfold.
  intros; repeat case_match; try discriminate; by inv H.
Qed.

Lemma Rtsl_table_inv_Rkstate :
  forall ka kb, Rkstate ka kb ->
  Rtsl_table ka.(ktsl_tbl) kb.(types_kstate_tsl_table).
Proof.
  autounfold with s3k_repr_unfold.
  intros; repeat case_match; try discriminate; by inv H.
Qed.

Lemma Rptable_inv_Rkstate :
  forall ka kb, Rkstate ka kb ->
  Rptable ka.(kptable) kb.(types_kstate_procs).
Proof.
  autounfold with s3k_repr_unfold.
  intros; repeat case_match; try discriminate; by inv H.
Qed.

Lemma Rkstate_with_err_inv :
  forall ka kb erra,
  (Rkstate ka kb /\ erra = kb.(types_kstate_errcode)) ->
  Rkstate_with_err (ka, erra) kb.
Proof.
  unfold Rkstate_with_err, Rkstate, kstate_to_kstate_err, fun_hrel, ofun_hrel.
  intros.
  destruct H.
  by rewrite H, H0.
Qed.


Local Transparent Archi.ptr64 Wordsize_Ptrofs.wordsize.

Lemma int64_to_usize_to_nat_same ia ib:
  Rnat ia ib ->
  usize_to_nat (USIZE.of_u64 ib) = ia.
Proof.
  unfold Rnat, fun_hrel.
  intros.
  rewrite <- H.
  unfold usize_to_nat, int64_to_nat, USIZE.to_Z, USIZE.of_u64.
  f_equal.
  apply Ptrofs.unsigned_repr.
  replace Ptrofs.max_unsigned with Int64.max_unsigned by reflexivity.
  apply Int64.unsigned_range_2.
Qed.

Lemma Rmon_table_set :
  forall ta tb ia (ib : int64) va vb tb',
  tb.[ib <- vb] = Some tb' ->
  Rmon_table ta tb ->
  Rmon va vb ->
  Rnat ia ib ->
  Rmon_table (cap_set ta (ia, va)) tb'.
Proof.
  autounfold with s3k_repr_unfold.
  intros.
  unfold mon_table_up, mbind in *.
  (* Avoid unfolding the implicit argument to mapM. *)
  unfold option_bind at 1.
  unfold option_bind in H0.
  case_match; try discriminate.
  apply mapM_Some_1 in H3.
  unfold Rmon, ofun_hrel in H1.
  pose proof Forall2_insert _ _ _ _ _ ia H3 H1.
  rewrite (bset_Some_insert tb ib vb H).
  rewrite (int64_to_usize_to_nat_same H2).
  unfold cap_set.
  inv H0.
  apply mapM_Some_2 in H4.
  by rewrite H4.
Qed.

Lemma Rmon_set_owner :
  forall mona monb ownera ownerb,
  Rmon (Some mona) monb ->
  Rpid_opt ownera ownerb ->
  let monb' := monb <| types_mon_t_owner := ownerb |> in
  let mona' := mona <| (@cowner mon_t) := ownera |> in
  Rmon (Some mona') monb'.
Proof.
  unfold Rmon, ofun_hrel, mon_up, mbind, option_bind, mk_cap_opt.
  intros.
  case_match; try discriminate. 
  unfold Rpid_opt, fun_hrel in H0.
  repeat case_match; try discriminate; simpl in *. 
  - lia.
  - lia.
  - inv H. f_equal. f_equal. simpl. congruence.
  - congruence.
Qed.

Lemma Rmon_set_cfree :
  forall mona monb cfreea cfreeb,
  Rmon (Some mona) monb ->
  Rnat cfreea cfreeb ->
  cfreea <> O ->
  let monb' := monb <| types_mon_t_cfree := cfreeb |> in
  let mona' := mona <| (@cfree mon_t) := cfreea |> in
  Rmon (Some mona') monb'.
Proof.
  unfold Rmon, ofun_hrel, mon_up, mbind, option_bind, mk_cap_opt.
  intros.
  case_match; try discriminate. 
  unfold Rnat, fun_hrel in H0.
  repeat case_match; try discriminate; simpl in *. 
  - congruence.
  - inv H.
  - inv H. repeat f_equal. simpl. congruence.
  - inv H.
Qed.

Lemma Rmon_inv :
  forall mona monb,
  Rpid_opt mona.(cowner) monb.(types_mon_t_owner) ->
  Rnat mona.(cfree) monb.(types_mon_t_cfree) ->
  mona.(cfree) <> O ->
  Rnat mona.(csize) monb.(types_mon_t_csize) ->
  Rpid_opt (Some mona.(cdata).(mpid)) monb.(types_mon_t_pid) ->
  Rmon (Some mona) monb.
Proof.
  intros.
Admitted.

(** Lemmas used for forward reasoning *)

Lemma Rmon_Some_corres :
  forall va vb,
  Rmon (Some va) vb ->
  Rpid_opt va.(cowner) vb.(types_mon_t_owner) /\
    Rnat va.(cfree) vb.(types_mon_t_cfree) /\
    Rnat va.(csize) vb.(types_mon_t_csize) /\
    Rpid_opt (Some va.(cdata).(mpid)) vb.(types_mon_t_pid).
Proof.
  intros.
  unfold Rmon, ofun_hrel, mon_up, mbind, option_bind, mk_cap_opt in H.
  repeat case_match; try discriminate.
  inv H.
  by repeat split.
Qed.

Lemma Rpid_opt_inv_Rmon :
  forall va vb,
  Rmon (Some va) vb ->
  Rpid_opt (Some va.(cdata).(mpid)) vb.(types_mon_t_pid).
Proof.
  intros.
  apply Rmon_Some_corres in H.
  tauto.
Qed.
  
Lemma mon_get_Some_corres :
  forall ta tb ia ib va,
  Rmon_table (CapTable ta) tb ->
  Rnat ia ib ->
  ta !! ia = Some va ->
  exists vb, tb.[ib] = Some vb /\ Rmon va vb.
Proof.
  intros.
  unfold Rmon_table, ofun_hrel, mon_table_up, mbind, option_bind in H.
  case_match; try discriminate.
  inv H.
  apply mapM_Some in H2.
  pose proof Forall2_length _ _ _ H2.
  pose proof lookup_lt_Some _ _ _ H1.
  rewrite bget_lookup.
  rewrite (int64_to_usize_to_nat_same H0).
  rewrite <- H in H3.
  apply lookup_lt_is_Some in H3.
  destruct H3.
  eexists x.
  split.
  - done.
  - by pose proof Forall2_lookup_lr _ _ _ _ _ _ H2 H3 H1.
Qed.

Lemma Rmon_None_corres :
  forall ownera ownerb cb,
  Rpid_opt (Some ownera) ownerb ->
  Rmon None cb ->
  Int64.eq cb.(types_mon_t_owner) ownerb = false.
Proof.
  unfold Rpid_opt, Rmon, mon_up, int64_to_pid, fun_hrel, ofun_hrel, mbind, option_bind, mk_cap_opt.
  intros.
  repeat case_match; try discriminate.
  inv H.
  norm_cmp in *.
  congruence.
Qed.

Lemma Rpid_opt_inj ownera ownerb ownera' ownerb':
  Rpid_opt ownera ownerb ->
  Rpid_opt ownera' ownerb' ->
  (ownera = ownera' <-> Int64.unsigned ownerb = Int64.unsigned ownerb').
Proof.
  unfold Rpid_opt, fun_hrel, mon_up, int64_to_pid.
  intros.
  repeat case_match; try discriminate.
  all: norm_cmp in *; subst; try (split; congruence).
  unfold int64_to_nat.
  repr_elim in *.
  split; intros.
  - inv H. rep_lia.
  - f_equal. rep_lia.
Qed.

Lemma Rmon_table_len_same :
  forall ta tb,
  Rmon_table (CapTable ta) tb ->
  length ta = length tb.
Proof.
Admitted.

Lemma lookup_Some_bget_safe {A} {B} :
  forall (ta : list A) (tb : list B) ia ib va,
  ta !! ia = Some va ->
  Rnat ia ib ->
  length ta = length tb ->
  exists vb, tb.[ib] = Some vb.
Proof.
Admitted.

Section Length.

Variable ta : list (option (cap_t mon_t)).
Hypothesis mon_table_size : ctable_size (CapTable ta) = MON_SZ.
  
Lemma mon_lookup_Some_len :
  forall ia ib va,
  ta !! ia = Some va ->
  Rnat ia ib ->
  Int64.ltu ib Config_mon_table_size = true.
Proof.
  (* Use axioms about array lengths from invariants.v *)
Admitted.

Lemma mon_lookup_None_len :
  forall ia ib,
  ta !! ia = None ->
  Rnat ia ib ->
  Int64.ltu ib Config_mon_table_size = false.
Proof.
Admitted.

End Length.
