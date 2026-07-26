From S3K.Barocq Require Import S3K_ShallowR.
From S3K.ExecSem Require Import util config.
From S3K.Verif Require Import tactics.

(** * Invariants and axioms *)

Section ExecSem.

(** Specify absract kernel configurations with concrete numbers. *)
Axiom proc_cnt_config : PROC_CNT = 4.
Axiom hart_cnt_config : HART_CNT = 1.

Axiom mon_sz_config : MON_SZ = 32.
Remark mon_sz_config_same :
  MON_SZ = int64_to_nat Config_mon_table_size.
Proof. unfold int64_to_nat; rewrite mon_sz_config; repr_elim; reflexivity. Qed.

Axiom tsl_sz_config : TSL_SZ = 32.
Remark tsl_sz_config_same :
  TSL_SZ = int64_to_nat Config_tsl_table_size.
Proof. unfold int64_to_nat; rewrite tsl_sz_config; repr_elim; reflexivity. Qed.

End ExecSem.

Section Barocq.

Variable kb : Types_kstate.

(** Array Barocq kernel state should have fixed lengths given at compile time. *)
Axiom kb_tsl_len : length kb.(types_kstate_tsl_table) = int64_to_nat Config_tsl_table_size.
Axiom kb_mon_len : length kb.(types_kstate_mon_table) = int64_to_nat Config_mon_table_size.
Axiom kb_procs_len : length kb.(types_kstate_procs) = int64_to_nat Config_max_pid.

End Barocq.

