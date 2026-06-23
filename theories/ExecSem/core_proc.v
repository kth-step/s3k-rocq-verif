From stdpp Require Import prelude functions.
From compcert Require Import Integers.
From RecordUpdate Require Import RecordUpdate.

(** * Process control block definitions *)

Inductive reg_t :=
  | REG_PC | REG_RA | REG_SP | REG_GP | REG_TP
  | REG_T0 | REG_T1 | REG_T2 | REG_T3 | REG_T4 | REG_T5 | REG_T6
  | REG_S0 | REG_S1 | REG_S2 | REG_S3 | REG_S4 | REG_S5 
  | REG_S6 | REG_S7 | REG_S8 | REG_S9 | REG_S10 | REG_S11
  | REG_A0 | REG_A1 | REG_A2 | REG_A3 | REG_A4 | REG_A5 | REG_A6 | REG_A7
  | REG_ECAUSE | REG_EVAL | REG_EPC | REG_ESP | REG_TPC | REG_TSP.

#[export] Instance reg_t_eq_dec : EqDecision reg_t.
Proof. solve_decision. Defined.

Inductive pmpreg_t :=
    PMP_REG0 | PMP_REG1 | PMP_REG2 | PMP_REG3 | PMP_REG4 | PMP_REG5 | PMP_REG6 | PMP_REG7.

#[export] Instance pmpreg_t_eq_dec : EqDecision pmpreg_t.
Proof. solve_decision. Defined.

Record proc_t := mk_proc_t {
  Regs : reg_t -> int64;
  Pmp : pmpreg_t -> (byte * int64);
}.

Definition proc_pmp_set (p : proc_t) (i : pmpreg_t) (pe : byte * int64) : proc_t :=
  p <| Pmp ::= <[ i := pe ]> |>.

Definition proc_pmp_get (p : proc_t) (i : pmpreg_t) : (byte * int64) :=
  p.(Pmp) i.

Definition proc_reg_set (p : proc_t) (r : reg_t) (v : int64) : proc_t :=
  p <| Regs ::= <[ r := v ]> |>.

Definition proc_reg_get (p : proc_t) r : int64 :=
  p.(Regs) r.

