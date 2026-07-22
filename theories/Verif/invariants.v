From S3K.Barocq Require Import S3K_ShallowR.
From S3K.ExecSem Require Import util config.

(** * Invariants and axioms *)

Section ExecSem.

(** Specify absract kernel configurations with concrete numbers. *)
Axiom proc_cnt_config : PROC_CNT = int64_to_nat Config_max_pid.
Axiom hart_cnt_config : HART_CNT = int64_to_nat Platform_num_harts .
Axiom mon_sz_config : MON_SZ = int64_to_nat Config_mon_table_size.
Axiom tsl_sz_config : TSL_SZ = int64_to_nat Config_tsl_table_size.

End ExecSem.

Section Barocq.

Variable kb : Types_kstate.

(** Array Barocq kernel state should have fixed lengths given at compile time. *)
Axiom kb_tsl_len : length kb.(types_kstate_tsl_table) = int64_to_nat Config_tsl_table_size.
Axiom kb_mon_len : length kb.(types_kstate_mon_table) = int64_to_nat Config_mon_table_size.
Axiom kb_procs_len : length kb.(types_kstate_procs) = int64_to_nat Config_max_pid.

End Barocq.

