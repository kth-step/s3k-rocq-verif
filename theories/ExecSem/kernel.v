From stdpp Require Import prelude.
From S3K.ExecSem Require Import cap proc sched.

(** * Core kernel state definitions *)

(** Kernel state contains the process table, three typed capability tables, and
    the executable schedule derived from time-slice capability ownership. *)
Record kernel_t := mk_kernel_t {
  kptable : ptable_t;
  ktsl_tbl : tsl_table_t;
  kmon_tbl : mon_table_t;
  kmem_tbl : mem_table_t;
  ksched : sched_t;
}.
