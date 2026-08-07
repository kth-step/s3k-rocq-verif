From stdpp Require Import prelude.
From compcert Require Import Integers.
From S3K.Barocq Require Import S3K_ShallowR.
From S3K.ExecSem Require Import util config cap proc.
From S3K.Verif Require Import gen_tactics.

(** * Axioms and their consequences *)

(** Concrete-level capability table size is the same as the abstract. *)
(* TODO: should become possible to derive from shallow embedding *)
Axiom mon_sz_config_same :
  MON_SZ = int64_to_nat Config_mon_table_size.

Axiom tsl_sz_config_same :
  TSL_SZ = int64_to_nat Config_tsl_table_size.

(** Axiomatize a dummy abstract memory table since the refinement mapping from concrete
memory table to abstract memory table is not yet defined. *)
(* TODO: complete refinement mappings *)
Parameter dummy_mem_table : mem_table_t.

(** Axiomatize for now the refinement mappings from concrete register list/PMP structure/
process status flags to their abstract counterparts. *)
Parameter regs_up : list int64 -> regs_t.
Parameter pmp_up : Types_pmp_t -> pmp_t.
Parameter pstate_to_flags : int64 -> (bool * bool).

(** Establish table size upper bound so as to ensure there is no arithmetic
overflow at the concrete level. *)
Remark mon_sz_upper_bound : MON_SZ <= Z.to_nat Int64.max_signed.
Proof.
  rewrite mon_sz_config_same.
  unfold int64_to_nat, Config_mon_table_size.
  repr_elim; rep_lia.
Qed.

Remark tsl_sz_upper_bound : TSL_SZ <= Z.to_nat Int64.max_signed.
Proof.
  rewrite tsl_sz_config_same.
  unfold int64_to_nat, Config_tsl_table_size.
  repr_elim; rep_lia.
Qed.
