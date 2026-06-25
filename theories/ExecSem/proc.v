From stdpp Require Import prelude functions countable.
From compcert Require Import Integers.
From RecordUpdate Require Import RecordUpdate.
Local Open Scope positive.

(** * Process control block definitions *)

Inductive perm_t := PERM_READ | PERM_WRITE | PERM_EXEC.

Inductive reg_t :=
  | REG_PC | REG_RA | REG_SP | REG_GP | REG_TP
  | REG_T0 | REG_T1 | REG_T2 | REG_T3 | REG_T4 | REG_T5 | REG_T6 | REG_T7
  | REG_A0 | REG_A1 | REG_A2 | REG_A3 | REG_A4 | REG_A5 | REG_A6 | REG_A7
  | REG_S0 | REG_S1 | REG_S2 | REG_S3 | REG_S4 | REG_S5 | REG_S6 | REG_S7 | REG_S8 | REG_S9 | REG_S10 | REG_S11.

Inductive pmpreg_t :=
    PMP_REG0 | PMP_REG1 | PMP_REG2 | PMP_REG3 | PMP_REG4 | PMP_REG5 | PMP_REG6 | PMP_REG7.

#[export] Instance perm_t_eq_dec : EqDecision perm_t.
Proof. solve_decision. Defined.

#[export] Program Instance perm_t_countable : Countable perm_t :=
  {| encode perm := match perm with
                    | PERM_READ => 1
                    | PERM_WRITE => 2
                    | PERM_EXEC => 3
                    end;
     decode p := match p with
                 | 1 => Some PERM_READ
                 | 2 => Some PERM_WRITE
                 | 3 => Some PERM_EXEC
                 | _ => None
                 end
  |}.
Solve All Obligations with by intros [].

#[export] Instance reg_t_eq_dec : EqDecision reg_t.
Proof. solve_decision. Defined.

#[export] Instance pmpreg_t_eq_dec : EqDecision pmpreg_t.
Proof. solve_decision. Defined.

Definition pmpconf_t : Type := (byte * int64).
Definition regs_t : Type := reg_t -> int64.
Definition pmp_t : Type := pmpreg_t -> option pmpconf_t.

Record proc_t := mk_proc_t {
  pregs : regs_t;
  ppmp : pmp_t;
  psuspend : bool;
}.

Definition ptable_t : Type := list proc_t.

Definition proc_reg_set (p : proc_t) (reg : reg_t) (val : int64) : proc_t :=
  p <| pregs ::= <[ reg := val ]> |>.

Definition proc_reg_get (p : proc_t) (reg : reg_t) : int64 :=
  p.(pregs) reg.

Definition proc_pmp_set (p : proc_t) (pmpreg : pmpreg_t) (conf : option pmpconf_t) : proc_t :=
  p <| ppmp ::= <[ pmpreg := conf ]> |>.

Definition proc_pmp_get (p : proc_t) (pmpreg : pmpreg_t) : option pmpconf_t :=
  p.(ppmp) pmpreg.

