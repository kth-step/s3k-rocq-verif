From S3K.Barocq Require Import S3K_ShallowR.
From S3K.ExecSem Require Import util.

Record invariants (kb: Types_kstate) := {
  kb_tsl_len :
    length kb.(types_kstate_tsl_table) = int64_to_nat Config_tsl_table_size;
  kb_mon_len :
    length kb.(types_kstate_mon_table) = int64_to_nat Config_mon_table_size;
  kb_procs_len :
    length kb.(types_kstate_procs) = int64_to_nat Config_max_pid;
}.

