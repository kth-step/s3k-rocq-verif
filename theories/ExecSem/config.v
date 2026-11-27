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

(** Kernel configuration axiomatized properties.
      The bounds are written [Z.to_nat _] since Rocq would parse large [nat]
       literals as an [Nat.of_num_uint] of their decimal digits. *)
Axiom kernel_config :
  0 < HART_CNT ∧
  0 < PROC_CNT ∧
  0 < MON_TBL_SZ ∧
  0 < TSL_TBL_SZ ∧
  0 < MEM_TBL_SZ ∧
  0 < TSLOT_CNT ∧
  HART_CNT ≤ Z.to_nat 65536 ∧
  PROC_CNT ≤ Z.to_nat 65535 ∧
  MON_TBL_SZ ≤ Z.to_nat 65535 ∧
  TSL_TBL_SZ ≤ Z.to_nat 65535 ∧
  MEM_TBL_SZ ≤ Z.to_nat 65535 ∧
  TSLOT_CNT ≤ Z.to_nat 65535 ∧
  0 < WCET_SYSCALL ∧
  0 < WCET_YIELD ∧
  0 < WCET_SCHED ∧
  WCET_SYSCALL + WCET_YIELD < PADDING ∧
  PADDING + WCET_SCHED < SLOT_LEN.

Lemma hart_cnt_0_gt : 0 < HART_CNT.
Proof. pose proof kernel_config. lia. Qed.
Lemma proc_cnt_0_gt : 0 < PROC_CNT.
Proof. pose proof kernel_config. lia. Qed.
Lemma mon_tbl_sz_0_gt : 0 < MON_TBL_SZ.
Proof. pose proof kernel_config. lia. Qed.
Lemma tsl_tbl_sz_0_gt : 0 < TSL_TBL_SZ.
Proof. pose proof kernel_config. lia. Qed.
Lemma mem_tbl_sz_0_gt : 0 < MEM_TBL_SZ.
Proof. pose proof kernel_config. lia. Qed.
Lemma tslot_cnt_0_gt : 0 < TSLOT_CNT.
Proof. pose proof kernel_config. lia. Qed.
Lemma hart_cnt_le_65536 : HART_CNT ≤ Z.to_nat 65536.
Proof. pose proof kernel_config. lia. Qed.
Lemma proc_cnt_le_65535 : PROC_CNT ≤ Z.to_nat 65535.
Proof. pose proof kernel_config. lia. Qed.
Lemma mon_tbl_sz_le_65535 : MON_TBL_SZ ≤ Z.to_nat 65535.
Proof. pose proof kernel_config. lia. Qed.
Lemma tsl_tbl_sz_le_65535 : TSL_TBL_SZ ≤ Z.to_nat 65535.
Proof. pose proof kernel_config. lia. Qed.
Lemma mem_tbl_sz_le_65535 : MEM_TBL_SZ ≤ Z.to_nat 65535.
Proof. pose proof kernel_config. lia. Qed.
Lemma tslot_cnt_le_65535 : TSLOT_CNT ≤ Z.to_nat 65535.
Proof. pose proof kernel_config. lia. Qed.
Lemma wcet_syscall_0_gt : 0 < WCET_SYSCALL.
Proof. pose proof kernel_config. lia. Qed.
Lemma wcet_yield_0_gt : 0 < WCET_YIELD.
Proof. pose proof kernel_config. lia. Qed.
Lemma wcet_sched_0_gt : 0 < WCET_SCHED.
Proof. pose proof kernel_config. lia. Qed.
Lemma wcet_syscall_yield_lt_padding : WCET_SYSCALL + WCET_YIELD < PADDING.
Proof. pose proof kernel_config. lia. Qed.
Lemma padding_wcet_sched_lt_slot_len : PADDING + WCET_SCHED < SLOT_LEN.
Proof. pose proof kernel_config. lia. Qed.
Lemma slot_len_0_gt : 0 < SLOT_LEN.
Proof. pose proof kernel_config. lia. Qed.
