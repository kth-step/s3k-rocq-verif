From stdpp Require Import prelude.
From S3K Require Export core_proc core_mon core_tsl.

(** * Core kernel state *)

Record kstate_t := mk_kstate_t {
  Kproc_tbl : list proc_t;
  Kmon_tbl : mon_table_t;
  Ktsl_tbl : tsl_table_t;
}.
