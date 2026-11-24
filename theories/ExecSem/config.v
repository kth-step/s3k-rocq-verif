From stdpp Require Import prelude.

(** * Kernel state configuration constants *)

Definition REG_CNT : nat := 32.
Definition PMP_CNT : nat := 8.
Definition MEM_ADDR_LIMIT : nat := 2 ^ 56.

Parameter HART_CNT : nat.
Parameter PROC_CNT : nat.
Parameter MON_TBL_SZ : nat.
Parameter TSL_TBL_SZ : nat.
Parameter MEM_TBL_SZ : nat.
Parameter TSLOT_CNT : nat.
Parameter WCET_SYSCALL : nat.
Parameter WCET_YIELD : nat.
Parameter WCET_SCHED : nat.
Parameter PADDING : nat.
Parameter SLOT_LEN : nat.

(* leaving the HOL4 constraints on the parameters at the moment, as not
 * necessary in proofs. *)
