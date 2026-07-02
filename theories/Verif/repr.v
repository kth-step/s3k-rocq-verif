From stdpp Require Import prelude.
From compcert Require Import Integers.
From S3K.Barocq Require Import S3K_ShallowR.
From S3K.ExecSem Require Import kstate cap ctx exec util proc sched.
From S3K.BarocqComp Require Import Intop Option.

Import IntopNotations.

Definition fun_hrel {A} {B} (f : B -> A) : A -> B -> Prop :=
  fun a b => f b = a.

Definition ofun_hrel {A} {B} (f : B -> option A) : A -> B -> Prop :=
  fun a b => f b = Some a.

Definition usize_to_nat (i : usize) : nat := Z.to_nat (USIZE.to_Z i).

Definition int64_to_pid (i : int64) : option nat :=
  if Int64.eq i 0UL then None else Some ((int64_to_nat i) - 1).

Definition mk_cap_opt {A} (owner : option nat) (free size : nat) (data : A) : option (option (cap_t A)) :=
  match free with
  | O => match owner with
         | None => Some None (* physically deleted *)
         | Some _ => None (* Invalid state, when owner exists, free must be greater than 0 *)
         end
  | S _ => Some
             (Some {| cowner := owner;
                      cfree := free;
                      csize := size;
                      cdata := data; |})
  end.

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
  match int64_to_pid mon.(types_mon_t_pid) with
  | None => None
  | Some pid =>
    let owner := int64_to_pid mon.(types_mon_t_owner) in
    let free := int64_to_nat mon.(types_mon_t_cfree) in
    let size := int64_to_nat mon.(types_mon_t_csize) in
    let data := {| mpid := pid; |} in
    mk_cap_opt owner free size data
  end.

Definition tsl_table_up l :=
  match mmap tsl_up l with
  | None => None
  | Some tsl_table => Some (CapTable tsl_table)
  end.

Definition mon_table_up (l : list Types_mon_t) :=
  match mmap mon_up l with
  | None => None
  | Some mon_table => Some (CapTable mon_table)
  end.
Parameter regs_up : list int64 -> regs_t.

Parameter pmp_up : Types_pmp_t -> pmp_t.

(* psuspend or busy flag *)
Parameter pstate_to_flags : int64 -> (bool * bool).

Definition proc_up (p : Types_proc_t) : proc_t :=
  {| pregs := regs_up p.(types_proc_t_regs);
     ppmp := pmp_up p.(types_proc_t_pmp);
     psuspend := fst (pstate_to_flags p.(types_proc_t_state)); |}.

Definition ptable_up := map proc_up.
Parameter mem_up : Types_mem_t -> mem_t.

Definition mem_table_up := map mem_up.

Parameter some_sched : sched_t.

Parameter some_mem_table : mem_table_t.

(* TODO maybe we should use some option monad notation *)
(* Alternatively, can define a version of kstate_to_kstate that is total. *)
Definition kstate_to_kstate (k : Types_kstate) : option kstate_t :=
  match mon_table_up k.(types_kstate_mon_table) with
  | None => None
  | Some mon_table =>
      match tsl_table_up k.(types_kstate_tsl_table) with
      | None => None
      | Some tsl_table =>
        Some {|
          kptable := ptable_up k.(types_kstate_procs);
          ktsl_tbl := tsl_table;
          kmon_tbl := mon_table;
          kmem_tbl := some_mem_table;
          ksched := some_sched;
        |}
      end
  end.

Definition kstate_to_kstate_err (k : Types_kstate) : option (kstate_t * int64) :=
  match kstate_to_kstate k with
  | None => None
  | Some k' => Some (k', k.(types_kstate_errcode))
  end.

Definition Rnat : nat -> int64 -> Prop := fun_hrel int64_to_nat.

Definition Rnat_usz : nat -> usize -> Prop := fun_hrel usize_to_nat.

Definition Rpid : nat -> int64 -> Prop := ofun_hrel int64_to_pid.

Definition Rpid_opt := fun_hrel int64_to_pid.

Definition Rtsl := ofun_hrel tsl_up.

Definition Rmon := ofun_hrel mon_up.

Definition Rtsl_table := ofun_hrel tsl_table_up.

Definition Rmon_table := ofun_hrel mon_table_up.

Definition Rptable := fun_hrel ptable_up.

Parameter kstate_to_ctx : Types_kstate -> ctx_t.

Definition Rctx := fun_hrel kstate_to_ctx.

Definition Rkstate := ofun_hrel kstate_to_kstate.

Definition Rkstate_with_err := ofun_hrel kstate_to_kstate_err.

Lemma Rkstate_equiv :
  forall ka kb,
  Rkstate ka kb <->
  Rmon_table ka.(kmon_tbl) kb.(types_kstate_mon_table) /\
    Rtsl_table ka.(ktsl_tbl) kb.(types_kstate_tsl_table) /\
    Rptable ka.(kptable) kb.(types_kstate_procs).
Proof.
Admitted.

Lemma Rkstate_with_err_equiv :
  forall ka kb erra,
  Rkstate_with_err (ka, erra) kb <->
  Rkstate ka kb /\ erra = kb.(types_kstate_errcode).
Proof.
Admitted.

Lemma Rmon_equiv :
  forall va vb,
  Rmon (Some va) vb ->
  Rnat va.(cfree) vb.(types_mon_t_cfree) /\
    Rnat va.(csize) vb.(types_mon_t_csize) /\
    Rpid_opt va.(cowner) vb.(types_mon_t_owner).
Proof.
Admitted.

