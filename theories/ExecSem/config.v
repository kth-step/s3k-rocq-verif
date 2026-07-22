(** * Kernel state configuration constants *)

Parameter PROC_CNT : nat.
Parameter HART_CNT : nat.
Parameter MON_SZ : nat.
Parameter TSL_SZ : nat.
Parameter TSLOT_CNT : nat.

Axiom proc_cnt_0_gt : 0 < PROC_CNT.
Axiom hart_cnt_0_gt : 0 < HART_CNT.
Axiom mon_sz_0_gt : 0 < MON_SZ.
Axiom tsl_sz_0_gt : 0 < TSL_SZ.
Axiom tslot_cnt_0_gt : 0 < TSLOT_CNT.

