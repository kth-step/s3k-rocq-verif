From stdpp Require Import prelude.
From compcert Require Import Integers.
From RecordUpdate Require Import RecordUpdate.
From S3K.Barocq Require Import S3K_ShallowR.
From S3K.ExecSem Require Import kstate cap ctx exec util proc sched config.
From S3K.BarocqComp Require Import Option Barray Intop Utils.
From S3K.BarocqComp Require Import ShallowNotations.
From S3K.Verif Require Import barocq_aux invariants gen_tactics refine_util.

Import IntopNotations.

Set Implicit Arguments.

(** * General refinement mapping definitions.  *)

Definition Rnat : nat -> int64 -> Prop := fun_hrel int64_to_nat.

Ltac rewrite_Rnat :=
  match goal with
  | [ H : Rnat ?ia ?ib |- _ ] => unfold Rnat, fun_hrel in H; rewrite H
  end.

(** * S3K specific refinement mapping definitions. *)

(** ** Capability mappings. *)

(** Refinement mapping from 64-bit integer to abstract process ID. 0UL encodes empty PID. *)
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

(** Refinement mapping for the time slice capability. *)
Definition tsl_up (tsl : Types_tsl_t) : option (option (cap_t tsl_t)) :=
  let owner := int64_to_pid tsl.(types_tsl_t_owner) in
  let free := int64_to_nat tsl.(types_tsl_t_cfree) in
  let size := int64_to_nat tsl.(types_tsl_t_csize) in
  let data := {| thart := int64_to_nat tsl.(types_tsl_t_hart);
                 tbase := int64_to_nat tsl.(types_tsl_t_base);
                 tsize := int64_to_nat tsl.(types_tsl_t_size);
                 tfree := int64_to_nat tsl.(types_tsl_t_free); |} in
  mk_cap_opt owner free size data.

(** Refinement mapping for the monitor capability. *) 
Definition mon_up (mon : Types_mon_t) : option (option (cap_t mon_t)) :=
  pid ← int64_to_pid mon.(types_mon_t_pid);
  let owner := int64_to_pid mon.(types_mon_t_owner) in
  let free := int64_to_nat mon.(types_mon_t_cfree) in
  let size := int64_to_nat mon.(types_mon_t_csize) in
  let data := {| mpid := pid; |} in
  mk_cap_opt owner free size data.

(** Refinement mappings from concrete capability table to abstract capability table.
Using stdpp list monad operation [mapM]:
   https://plv.mpi-sws.org/coqdoc/stdpp/stdpp.list_monad.html *)
Definition tsl_table_up (l : list Types_tsl_t) : option tsl_table_t :=
  tsl_table ← mapM tsl_up l; mret (CapTable tsl_table).

Definition mon_table_up (l : list Types_mon_t) : option mon_table_t :=
  mon_table ← mapM mon_up l; mret (CapTable mon_table).

(* TODO: complete refinement mappings *)
(* NOTE: Axiomatize a dummy abstract memory table since the refinement mapping from concrete
memory table to abstract memory table is not yet defined. *)
Parameter dummy_mem_table : mem_table_t.


(** ** Process control block mappings. *)

(* NOTE: Axiomatize for now the refinement mappings from concrete register list/PMP structure/
process status flags to their abstract counterparts. *)
Parameter regs_up : list int64 -> regs_t.
Parameter pmp_up : Types_pmp_t -> pmp_t.
Parameter pstate_to_flags : int64 -> (bool * bool).

(** Refinement mapping for a process control block. *)
Definition proc_up (p : Types_proc_t) : proc_t :=
  {| pregs := regs_up p.(types_proc_t_regs);
     ppmp := pmp_up p.(types_proc_t_pmp);
     psuspend := fst (pstate_to_flags p.(types_proc_t_state)); |}.

(** Refinement mapping for the process table. *)
Definition ptable_up := map proc_up.

(** ** Scheduler mappings. *)

(** Refinement mapping for time frame. *)
Definition frame_up (f: Types_frame_t) : (option nat * nat) :=
  (int64_to_pid f.(types_frame_t_pid), int64_to_nat f.(types_frame_t_length)).

(** Refinement mapping for scheduler per hart. *)
Definition hsched_up (l : list Types_frame_t) : hsched_t :=
  HSched (map frame_up l).

(** Refinement mapping for the scheduler. *)
Definition sched_up (l : list (list Types_frame_t)) : sched_t :=
  map hsched_up l.

(** Refinement mapping for the persistent kernel state, omitting error code. *)
Definition kstate_up (k : Types_kstate) : option kstate_t :=
  mon_table ← mon_table_up k.(types_kstate_mon_table);
  tsl_table ← tsl_table_up k.(types_kstate_tsl_table);
  mret {|
    kptable := ptable_up k.(types_kstate_procs);
    ktsl_tbl := tsl_table;
    kmon_tbl := mon_table;
    kmem_tbl := dummy_mem_table;
    ksched := sched_up k.(types_kstate_sched);
  |}.

(** Refinement mapping for the persistent kernel state with error code. *)
Definition kstate_to_kstate_err (k : Types_kstate) : option (kstate_t * int64) :=
  k' ← kstate_up k; mret (k', k.(types_kstate_errcode)).

(** ** Relational version of refinement mappings. *)
Definition Rpid : nat -> int64 -> Prop := ofun_hrel int64_to_pid.

Definition Rpid_opt : option nat -> int64 -> Prop := fun_hrel int64_to_pid.

Definition Rtsl := ofun_hrel tsl_up.

Definition Rmon := ofun_hrel mon_up.

Definition Rframe := fun_hrel frame_up.

Definition Rtsl_table := ofun_hrel tsl_table_up.

Definition Rmon_table := ofun_hrel mon_table_up.

Definition Rhsched := fun_hrel hsched_up.

Definition Rsched := fun_hrel sched_up.

Definition Rptable := fun_hrel ptable_up.

Definition Rkstate := ofun_hrel kstate_up.

Definition Rkstate_with_err := ofun_hrel kstate_to_kstate_err.

(** * Helper lemmas *)

Create HintDb kstate_unfold.
Hint Unfold mbind option_bind : kstate_unfold.
Hint Unfold fun_hrel ofun_hrel : kstate_unfold.
Hint Unfold kstate_up kstate_to_kstate_err : kstate_unfold.
Hint Unfold Rtsl_table Rmon_table Rsched Rptable Rkstate Rkstate_with_err : kstate_unfold.

(** Abstract lookup safety + indices connected by Rnat imply barocq get safety. *)
Lemma lookup_Some_bget_safe {A} {B} :
  forall (ta : list A) (tb : list B) ia ib va,
  ta !! ia = Some va ->
  Rnat ia ib ->
  length ta = length tb ->
  exists vb, tb.[ib] = Some vb.
Proof.
  intros.
  assert (tb.[ib] <> None). {
    apply bget_Some_lt.
    rewrite int64_to_usize_to_nat_same.
    rewrite <- H1.
    rewrite_Rnat.
    by eapply lookup_lt_Some.
  }
  destruct tb.[ib]; [ eauto | congruence ].
Qed.

(** ** Rksate related. *)

(** Rkstate inversion. *)

Section Rkstate.

Variable ka : kstate_t.

(* FIXME We assume memory table is always correct for now. *)
Hypothesis mem_table_correct :
  ka.(kmem_tbl) = dummy_mem_table.

Lemma Rkstate_inv :
  forall kb,
  Rmon_table ka.(kmon_tbl) kb.(types_kstate_mon_table) ->
  Rtsl_table ka.(ktsl_tbl) kb.(types_kstate_tsl_table) ->
  Rsched ka.(ksched) kb.(types_kstate_sched) ->
  Rptable ka.(kptable) kb.(types_kstate_procs) ->
  Rkstate ka kb.
Proof.
  autounfold with kstate_unfold.
  intros.
  destruct ka.
  simpl in *.
  by rewrite H, H0, H1, H2, mem_table_correct.
Qed.

End Rkstate.

Lemma Rmon_table_inv_Rkstate :
  forall ka kb, Rkstate ka kb ->
  Rmon_table ka.(kmon_tbl) kb.(types_kstate_mon_table).
Proof.
  autounfold with kstate_unfold.
  intros; repeat case_match; try discriminate; by inv H.
Qed.

Lemma Rtsl_table_inv_Rkstate :
  forall ka kb, Rkstate ka kb ->
  Rtsl_table ka.(ktsl_tbl) kb.(types_kstate_tsl_table).
Proof.
  autounfold with kstate_unfold.
  intros; repeat case_match; try discriminate; by inv H.
Qed.

Lemma Rptable_inv_Rkstate :
  forall ka kb, Rkstate ka kb ->
  Rptable ka.(kptable) kb.(types_kstate_procs).
Proof.
  autounfold with kstate_unfold.
  intros; repeat case_match; try discriminate; by inv H.
Qed.

Lemma Rsched_inv_Rkstate :
  forall ka kb, Rkstate ka kb ->
  Rsched ka.(ksched) kb.(types_kstate_sched).
Proof.
  autounfold with kstate_unfold.
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

(** ** Monitor table related. *)

(** Table set preserves correspondence. *)
Lemma Rmon_table_set :
  forall ta tb ia (ib : int64) va vb tb',
  tb.[ib <- vb] = Some tb' ->
  Rmon_table ta tb ->
  Rmon va vb ->
  Rnat ia ib ->
  Rmon_table (cap_set ta (ia, va)) tb'.
Proof.
  autounfold with kstate_unfold.
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
  rewrite int64_to_usize_to_nat_same.
  rewrite_Rnat.
  unfold cap_set.
  inv H0.
  apply mapM_Some_2 in H4.
  by rewrite H4.
Qed.

(** Getting at a valid index preserves correspondence. *)
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
  rewrite int64_to_usize_to_nat_same.
  rewrite_Rnat.
  rewrite <- H in H3.
  apply lookup_lt_is_Some in H3.
  destruct H3.
  eexists x.
  split.
  - done.
  - by pose proof Forall2_lookup_lr _ _ _ _ _ _ H2 H3 H1.
Qed.

(** When two tables correspond, they have the same length. *)
Lemma Rmon_table_len_same :
  forall ta tb,
  Rmon_table (CapTable ta) tb ->
  length ta = length tb.
Proof.
  unfold Rmon_table, mon_table_up, mbind, option_bind, ofun_hrel.
  intros.
  case_match; try discriminate.
  inv H.
  symmetry; by eapply length_mapM.
Qed.


Section Length.

Variable ta : list (option (cap_t mon_t)).
Hypothesis mon_table_size : ctable_size (CapTable ta) = MON_SZ.
  
(** When abstract lookup on monitor table succeeds, barocq array length runtime check
succeeds. *)
Lemma mon_lookup_Some_len :
  forall ia ib va,
  ta !! ia = Some va ->
  Rnat ia ib ->
  Int64.ltu ib Config_mon_table_size = true.
Proof.
  intros.
  pose proof mon_sz_config_same.
  unfold Rnat, int64_to_nat, fun_hrel in *.
  norm_cmp.
  pose proof lookup_lt_Some _ _ _ H.
  simpl in mon_table_size.
  rep_lia.
Qed.

Lemma mon_lookup_None_len :
  forall ia ib,
  ta !! ia = None ->
  Rnat ia ib ->
  Int64.ltu ib Config_mon_table_size = false.
Proof.
  intros.
  pose proof mon_sz_config_same.
  unfold Rnat, int64_to_nat, fun_hrel in *.
  norm_cmp.
  pose proof lookup_ge_None_1 _ _ H.
  simpl in mon_table_size.
  rep_lia.
Qed.

End Length.

(** ** Monitor capability related. *)

(** Barocq monitor capability corresponds to None if owner and cfree are 0
and has valid pid. *)
Lemma Rmon_None_inv :
  forall csize pa pb,
  Rpid_opt (Some pa) pb ->
  Rmon None {|
    types_mon_t_owner := 0 L;
    types_mon_t_cfree := 0 L;
    types_mon_t_csize := csize;
    types_mon_t_pid := pb;
  |}.
Proof.
  unfold Rmon, ofun_hrel, mon_up, mbind, option_bind, mk_cap_opt.
  intros.
  repeat case_match; try discriminate. 
  - reflexivity.
  - simpl in H0; unfold Rpid_opt, fun_hrel in H; congruence.
Qed.


(** Capabilities correspond if fields correspond. *)
Lemma Rmon_Some_inv :
  forall mona monb,
  Rpid_opt mona.(cowner) monb.(types_mon_t_owner) ->
  Rnat mona.(cfree) monb.(types_mon_t_cfree) ->
  mona.(cfree) <> O ->
  Rnat mona.(csize) monb.(types_mon_t_csize) ->
  Rpid_opt (Some mona.(cdata).(mpid)) monb.(types_mon_t_pid) ->
  Rmon (Some mona) monb.
Proof.
  destruct mona, cdata.
  simpl.
  unfold Rmon, Rpid_opt, Rnat, fun_hrel, ofun_hrel, mon_up, mbind, option_bind, mk_cap_opt.
  intros.
  repeat case_match; try discriminate; try congruence.
Qed.

(** When a concrete capability corresponds to some abstract capability, their fields correspond. *)
Lemma Rmon_Some_corres :
  forall va vb,
  Rmon (Some va) vb ->
  Rpid_opt va.(cowner) vb.(types_mon_t_owner) /\
    Rnat va.(cfree) vb.(types_mon_t_cfree) /\
    Rnat va.(csize) vb.(types_mon_t_csize) /\
    Rpid_opt (Some va.(cdata).(mpid)) vb.(types_mon_t_pid) /\
    va.(cfree) <> O.
Proof.
  intros.
  unfold Rmon, ofun_hrel, mon_up, mbind, option_bind, mk_cap_opt in H.
  repeat case_match; try discriminate.
  inv H.
  by repeat split.
Qed.

(** When a concrete capability corresponds to None, it's owner field is invalid. *)
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

(** ** Rpid_opt related *)

(** Rpid_opt is a one-to-one function. *)
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
  repr_elim.
  split; intros.
  - inv H. rep_lia.
  - f_equal. rep_lia.
Qed.

