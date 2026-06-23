From S3K Require Import core_kernel exec_sched.

(** * Executable kernel state *)

Record exec_kstate_t := mk_exec_kstate_t {
  Kstate : kstate_t;
  Ksched : sched_t;
  Current : option nat;
}.

