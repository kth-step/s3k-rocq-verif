From S3K.Barocq Require Import S3K_ShallowR.
From S3K.ExecSem Require Import util config.
From S3K.Verif Require Import gen_tactics.

(** * Invariants and axioms *)

(** Specify absract kernel configurations with concrete numbers. *)
(* TODO document, generalize *)
Axiom mon_sz_config : MON_SZ = 32.

Remark mon_sz_config_same :
  MON_SZ = int64_to_nat Config_mon_table_size.
Proof. unfold int64_to_nat; rewrite mon_sz_config; repr_elim; reflexivity. Qed.

Axiom tsl_sz_config : TSL_SZ = 32.

Remark tsl_sz_config_same :
  TSL_SZ = int64_to_nat Config_tsl_table_size.
Proof. unfold int64_to_nat; rewrite tsl_sz_config; repr_elim; reflexivity. Qed.


