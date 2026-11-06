From stdpp Require Import prelude.

(** * Kernel state configuration constants *)

Definition REG_CNT : nat := 32.
Definition PMP_CNT : nat := 8.
Definition MEM_ADDR_LIMIT : nat := 2 ^ 56.

(** Kernel dimensions and timing constants remain abstract within word-level
    representation bounds and the required timing separation. *)

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

Axiom hart_cnt_0_gt : 0 < HART_CNT.
Axiom proc_cnt_0_gt : 0 < PROC_CNT.
Axiom mon_tbl_sz_0_gt : 0 < MON_TBL_SZ.
Axiom tsl_tbl_sz_0_gt : 0 < TSL_TBL_SZ.
Axiom mem_tbl_sz_0_gt : 0 < MEM_TBL_SZ.
Axiom tslot_cnt_0_gt : 0 < TSLOT_CNT.
Axiom hart_cnt_le_65536 : HART_CNT ≤ 65536.
Axiom proc_cnt_le_65535 : PROC_CNT ≤ 65535.
Axiom mon_tbl_sz_le_65535 : MON_TBL_SZ ≤ 65535.
Axiom tsl_tbl_sz_le_65535 : TSL_TBL_SZ ≤ 65535.
Axiom mem_tbl_sz_le_65535 : MEM_TBL_SZ ≤ 65535.
Axiom tslot_cnt_le_65535 : TSLOT_CNT ≤ 65535.
Axiom wcet_syscall_0_gt : 0 < WCET_SYSCALL.
Axiom wcet_yield_0_gt : 0 < WCET_YIELD.
Axiom wcet_sched_0_gt : 0 < WCET_SCHED.

(** PADDING covers a syscall followed by a yield; one padded interval plus the
    scheduler WCET must fit strictly within a hardware scheduling slot. *)
Axiom wcet_syscall_yield_lt_padding : WCET_SYSCALL + WCET_YIELD < PADDING.
Axiom padding_wcet_sched_lt_slot_len : PADDING + WCET_SCHED < SLOT_LEN.
