From stdpp Require Import prelude.
From compcert Require Import Integers.
From S3K.Barocq Require Import S3K_ShallowR.
From S3K.ExecSem Require Import util config.
From S3K.Verif Require Import gen_tactics.

(** * Invariants and axioms *)

(** Concrete-level capability table size is the same as the abstract. *)
Axiom mon_sz_config_same :
  MON_SZ = int64_to_nat Config_mon_table_size.

(** Establish table size upper bound so as to ensure there is no arithmetic
overflow at the concrete level. *)
Remark mon_sz_upper_bound : MON_SZ <= Z.to_nat Int64.max_signed.
Proof.
  rewrite mon_sz_config_same.
  unfold int64_to_nat, Config_mon_table_size.
  repr_elim; rep_lia.
Qed.

Axiom tsl_sz_config_same :
  TSL_SZ = int64_to_nat Config_tsl_table_size.

Remark tsl_sz_upper_bound : TSL_SZ <= Z.to_nat Int64.max_signed.
Proof.
  rewrite tsl_sz_config_same.
  unfold int64_to_nat, Config_tsl_table_size.
  repr_elim; rep_lia.
Qed.
