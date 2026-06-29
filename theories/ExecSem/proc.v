From stdpp Require Import prelude functions countable gmap.
From compcert Require Import Integers.
From RecordUpdate Require Import RecordUpdate.
From S3K.ExecSem Require Import util.
From S3K.BarocqComp Require Import Intop.

Import IntopNotations.

(** * Process control block definitions *)

Inductive perm_t := PERM_READ | PERM_WRITE | PERM_EXEC.

Inductive reg_t := REG_PC | REG_RA | REG_SP | REG_GP | REG_TP
 | REG_T0 | REG_T1 | REG_T2 | REG_T3 | REG_T4 | REG_T5 | REG_T6 | REG_T7
 | REG_A0 | REG_A1 | REG_A2 | REG_A3 | REG_A4 | REG_A5 | REG_A6 | REG_A7
 | REG_S0 | REG_S1 | REG_S2 | REG_S3 | REG_S4 | REG_S5 | REG_S6 | REG_S7
 | REG_S8 | REG_S9 | REG_S10 | REG_S11.

Inductive pmpreg_t := PMP_REG0 | PMP_REG1 | PMP_REG2
 | PMP_REG3 | PMP_REG4 | PMP_REG5 | PMP_REG6 | PMP_REG7.

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
  |}%positive.
Solve All Obligations with by intros [].

#[export] Instance reg_t_eq_dec : EqDecision reg_t.
Proof. solve_decision. Defined.

#[export] Instance pmpreg_t_eq_dec : EqDecision pmpreg_t.
Proof. solve_decision. Defined.

Definition pmpconf_t := (byte * int64)%type.
Definition regs_t := reg_t -> int64.
Definition pmp_t := pmpreg_t -> option pmpconf_t.

Record proc_t := mk_proc_t {
  pregs : regs_t;
  ppmp : pmp_t;
  psuspend : bool;
}.

Definition ptable_t := list proc_t.

Definition proc_reg_set (p : proc_t) '(reg, val) : proc_t :=
  p <| pregs ::= <[ reg := val ]> |>.

Definition proc_reg_get (p : proc_t) (reg : reg_t) : int64 :=
  p.(pregs) reg.

Definition proc_pmp_set (p : proc_t) '(pmpreg, conf) : proc_t :=
  p <| ppmp ::= <[ pmpreg := conf ]> |>.

Definition ptable_pmp_try_set (ptbl : ptable_t) '(p_opt, pmpreg_opt, conf_opt)
  : ptable_t :=
  match p_opt with
  | None => ptbl
  | Some p =>
      match pmpreg_opt with
      | None => ptbl
      | Some pmpreg =>
          match ptbl !! p with
          | None => ptbl
          | Some proc =>
              <[p := proc <| ppmp ::= <[pmpreg := conf_opt]> |> ]> ptbl
          end
      end
  end.

Definition proc_pmp_get (p : proc_t) (pmpreg : pmpreg_t) : option pmpconf_t :=
  p.(ppmp) pmpreg.

Definition ptable_pmp_get (ptbl : ptable_t) '(p, pmpreg)
  : option pmpconf_t :=
  match ptbl !! p with
  | None => None
  | Some proc => proc_pmp_get proc pmpreg
  end.

Definition rwx_decode (rwx : byte) : gset perm_t :=
  (if Byte.eq (rwx &₈  Byte.one) Byte.one then {[ PERM_READ ]} else ∅ ) ∪
  (if Byte.eq (rwx &₈  Byte.repr 2) (Byte.repr 2) then {[ PERM_WRITE ]} else ∅ ) ∪
  (if Byte.eq (rwx &₈  Byte.repr 4) (Byte.repr 4) then {[ PERM_EXEC ]} else ∅ ).

Definition pmp_decode '(rwx, addr) : gset perm_t * nat * nat :=
  let perm := rwx_decode rwx in
  let base := int64_to_nat (((addr +₆₄ 1UL) &₆₄ addr) <<₆₄ 2UL) in
  let size := int64_to_nat (((addr +₆₄ 1UL) ^₆₄ addr) +₆₄ 1UL)  in
  (perm, base, size).

