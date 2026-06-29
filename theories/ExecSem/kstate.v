From stdpp Require Import prelude.
From S3K.ExecSem Require Import cap proc sched.

(** * Core kernel state definitions *)

Record kstate_t := mk_kstate_t {
  kptable : ptable_t;
  ktsl_tbl : tsl_table_t;
  kmon_tbl : mon_table_t;
  kmem_tbl : mem_table_t;
  ksched : sched_t;
}.
