From stdpp Require Import prelude functions countable gmap.
From compcert Require Import Integers.
From RecordUpdate Require Import RecordUpdate.
From S3K.ExecSem Require Import util config.
From BarocqComp Require Import Intop.

Import IntopNotations.

(** * Process control block definitions *)

Inductive perm_t := PERM_READ | PERM_WRITE | PERM_EXEC.

Inductive reg_t := REG_PC | REG_RA | REG_SP | REG_GP | REG_TP
 | REG_T0 | REG_T1 | REG_T2 | REG_T3 | REG_T4 | REG_T5 | REG_T6
 | REG_A0 | REG_A1 | REG_A2 | REG_A3 | REG_A4 | REG_A5 | REG_A6 | REG_A7
 | REG_S0 | REG_S1 | REG_S2 | REG_S3 | REG_S4 | REG_S5
 | REG_S6 | REG_S7 | REG_S8 | REG_S9 | REG_S10 | REG_S11.

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

(** Register indices, following the saved-context order *)
Definition reg_t2num (reg : reg_t) : nat :=
  match reg with
  | REG_PC => 0 | REG_RA => 1 | REG_SP => 2 | REG_GP => 3 | REG_TP => 4
  | REG_T0 => 5 | REG_T1 => 6 | REG_T2 => 7 | REG_T3 => 8 | REG_T4 => 9
  | REG_T5 => 10 | REG_T6 => 11
  | REG_A0 => 12 | REG_A1 => 13 | REG_A2 => 14 | REG_A3 => 15 | REG_A4 => 16
  | REG_A5 => 17 | REG_A6 => 18 | REG_A7 => 19
  | REG_S0 => 20 | REG_S1 => 21 | REG_S2 => 22 | REG_S3 => 23 | REG_S4 => 24
  | REG_S5 => 25 | REG_S6 => 26 | REG_S7 => 27 | REG_S8 => 28 | REG_S9 => 29
  | REG_S10 => 30 | REG_S11 => 31
  end.

Definition reg_pc := reg_t2num REG_PC.
Definition reg_ra := reg_t2num REG_RA.
Definition reg_sp := reg_t2num REG_SP.
Definition reg_gp := reg_t2num REG_GP.
Definition reg_tp := reg_t2num REG_TP.
Definition reg_t0 := reg_t2num REG_T0.
Definition reg_t1 := reg_t2num REG_T1.
Definition reg_t2 := reg_t2num REG_T2.
Definition reg_t3 := reg_t2num REG_T3.
Definition reg_t4 := reg_t2num REG_T4.
Definition reg_t5 := reg_t2num REG_T5.
Definition reg_t6 := reg_t2num REG_T6.
Definition reg_a0 := reg_t2num REG_A0.
Definition reg_a1 := reg_t2num REG_A1.
Definition reg_a2 := reg_t2num REG_A2.
Definition reg_a3 := reg_t2num REG_A3.
Definition reg_a4 := reg_t2num REG_A4.
Definition reg_a5 := reg_t2num REG_A5.
Definition reg_a6 := reg_t2num REG_A6.
Definition reg_a7 := reg_t2num REG_A7.
Definition reg_s0 := reg_t2num REG_S0.
Definition reg_s1 := reg_t2num REG_S1.
Definition reg_s2 := reg_t2num REG_S2.
Definition reg_s3 := reg_t2num REG_S3.
Definition reg_s4 := reg_t2num REG_S4.
Definition reg_s5 := reg_t2num REG_S5.
Definition reg_s6 := reg_t2num REG_S6.
Definition reg_s7 := reg_t2num REG_S7.
Definition reg_s8 := reg_t2num REG_S8.
Definition reg_s9 := reg_t2num REG_S9.
Definition reg_s10 := reg_t2num REG_S10.
Definition reg_s11 := reg_t2num REG_S11.

(** System call arguments *)
Record args_t := mk_args_t {
  args_a0 : int64;
  args_a1 : int64;
  args_a2 : int64;
  args_a3 : int64;
  args_a4 : int64;
  args_a7 : int64;
}.

Inductive pmpreg_t := PMP_REG0 | PMP_REG1 | PMP_REG2
 | PMP_REG3 | PMP_REG4 | PMP_REG5 | PMP_REG6 | PMP_REG7.

#[export] Instance pmpreg_t_eq_dec : EqDecision pmpreg_t.
Proof. solve_decision. Defined.

Definition pmpreg_t2num (pmpreg : pmpreg_t) : nat :=
  match pmpreg with
  | PMP_REG0 => 0 | PMP_REG1 => 1 | PMP_REG2 => 2 | PMP_REG3 => 3
  | PMP_REG4 => 4 | PMP_REG5 => 5 | PMP_REG6 => 6 | PMP_REG7 => 7
  end.

(** Inverse of [pmpreg_t2num] on indices below [PMP_CNT]. HOL4 leaves the
    result unspecified for larger indices; here they map to [PMP_REG7]. *)
Definition num2pmpreg_t (n : nat) : pmpreg_t :=
  match n with
  | 0 => PMP_REG0 | 1 => PMP_REG1 | 2 => PMP_REG2 | 3 => PMP_REG3
  | 4 => PMP_REG4 | 5 => PMP_REG5 | 6 => PMP_REG6 | _ => PMP_REG7
  end.

Record pmpconf_t := mk_pmpconf_t {
  wpmp_conf : byte;
  wpmp_addr : int64;
}.

Definition regs_t := list int64.
Definition pmp_t := list pmpconf_t.

Definition pmpconf_zero : pmpconf_t :=
  {| wpmp_conf := Byte.zero; wpmp_addr := Int64.zero |}.

Definition pmpconf_view (conf : pmpconf_t) : option pmpconf_t :=
  if decide (conf.(wpmp_conf) = Byte.zero) then None else Some conf.

(** State mask 1 marks hart ownership; mask 2 prevents future scheduling. *)
Record proc_t := mk_proc_t {
  pregs : regs_t;
  ppmp : pmp_t;
  pstate : int64;
}.

Definition ptable_t := list proc_t.

Definition ptable_get (p : nat) (ptable : ptable_t) : option proc_t :=
  ptable !! p.

Definition ptable_set (p : nat) (proc : proc_t) (ptbl : ptable_t) : ptable_t :=
  <[ p := proc ]> ptbl.

Definition ptable_upd (p : nat) (f : proc_t -> proc_t) (ptable : ptable_t)
  : option ptable_t :=
  match ptable_get p ptable with
  | None => None
  | Some proc => Some (ptable_set p (f proc) ptable)
  end.

Definition proc_reg_get (proc : proc_t) (reg : nat) : int64 :=
  proc.(pregs) !!! reg.

Definition proc_get_args (proc : proc_t) : option args_t :=
  if decide (length proc.(pregs) < 20) then None
  else
    Some {| args_a0 := proc_reg_get proc reg_a0;
            args_a1 := proc_reg_get proc reg_a1;
            args_a2 := proc_reg_get proc reg_a2;
            args_a3 := proc_reg_get proc reg_a3;
            args_a4 := proc_reg_get proc reg_a4;
            args_a7 := proc_reg_get proc reg_a7 |}.

Definition proc_pmp_get (proc : proc_t) (pmpreg : pmpreg_t) : option pmpconf_t :=
  (proc.(ppmp) !! pmpreg_t2num pmpreg) ≫= pmpconf_view.

Definition proc_suspend_get (proc : proc_t) : bool :=
  bool_decide (proc.(pstate) &₆₄ Int64.repr 2 ≠ Int64.zero).

Definition proc_busy_get (proc : proc_t) : bool :=
  bool_decide (proc.(pstate) &₆₄ Int64.one ≠ Int64.zero).

Definition ptable_reg_get (p : nat) (reg : nat) (ptbl : ptable_t) : option int64 :=
  match ptable_get p ptbl with
  | None => None
  | Some proc =>
      if decide (reg < length proc.(pregs)) then
        Some (proc_reg_get proc reg)
      else None
  end.

Definition ptable_pmp_get (p : nat) (pmpreg : pmpreg_t) (ptbl : ptable_t)
  : option pmpconf_t :=
  match ptable_get p ptbl with
  | None => None
  | Some proc => proc_pmp_get proc pmpreg
  end.

Definition ptable_suspend_get (p : nat) (ptbl : ptable_t) : option bool :=
  match ptable_get p ptbl with
  | None => None
  | Some proc => Some (proc_suspend_get proc)
  end.

Definition ptable_busy_get (p : nat) (ptbl : ptable_t) : option bool :=
  match ptable_get p ptbl with
  | None => None
  | Some proc => Some (proc_busy_get proc)
  end.

Definition proc_reg_set (reg : nat) (val : int64) (proc : proc_t) : proc_t :=
  proc <| pregs := (<[ reg := val ]> proc.(pregs)) |>.

Definition proc_pmp_set (pmpreg : pmpreg_t) (conf : option pmpconf_t)
  (proc : proc_t) : proc_t :=
  let conf' := match conf with None => pmpconf_zero | Some c => c end in
  proc <| ppmp := (<[ pmpreg_t2num pmpreg := conf' ]> proc.(ppmp)) |>.

Definition proc_busy_set (b : bool) (proc : proc_t) : proc_t :=
  proc <| pstate := ((proc.(pstate) &₆₄ Int64.not Int64.one)
                     |₆₄ (if b then Int64.one else Int64.zero)) |>.

Definition proc_suspend_set (b : bool) (proc : proc_t) : proc_t :=
  proc <| pstate := ((proc.(pstate) &₆₄ Int64.not (Int64.repr 2))
                     |₆₄ (if b then Int64.repr 2 else Int64.zero)) |>.

Definition ptable_reg_upd (p : nat) (reg : nat) (val : int64) (ptbl : ptable_t)
  : option ptable_t :=
  match ptable_get p ptbl with
  | None => None
  | Some proc =>
      if decide (reg < length proc.(pregs)) then
        Some (ptable_set p (proc_reg_set reg val proc) ptbl)
      else None
  end.

Definition ptable_pmp_upd (p : nat) (pmpreg : pmpreg_t) (conf : option pmpconf_t)
  (ptbl : ptable_t) : option ptable_t :=
  match ptable_get p ptbl with
  | None => None
  | Some proc =>
      if decide (pmpreg_t2num pmpreg < length proc.(ppmp)) then
        Some (ptable_set p (proc_pmp_set pmpreg conf proc) ptbl)
      else None
  end.

Definition ptable_suspend_upd (p : nat) (b : bool) (ptbl : ptable_t)
  : option ptable_t :=
  ptable_upd p (proc_suspend_set b) ptbl.

Definition ptable_busy_upd (p : nat) (b : bool) (ptbl : ptable_t)
  : option ptable_t :=
  ptable_upd p (proc_busy_set b) ptbl.

Definition ptable_pmp_try_clear (p_opt : option nat) (reg_opt : option pmpreg_t)
  (ptbl : ptable_t) : option ptable_t :=
  match p_opt with
  | None => Some ptbl
  | Some p =>
      match reg_opt with
      | None => Some ptbl
      | Some preg => ptable_pmp_upd p preg None ptbl
      end
  end.

(** The low three bits encode read, write, and execute respectively. *)
Definition rwx_decode (rwx : byte) : gset perm_t :=
  (if Byte.eq (rwx &₈  Byte.one) Byte.one then {[ PERM_READ ]} else ∅ ) ∪
  (if Byte.eq (rwx &₈  Byte.repr 2) (Byte.repr 2) then {[ PERM_WRITE ]} else ∅ ) ∪
  (if Byte.eq (rwx &₈  Byte.repr 4) (Byte.repr 4) then {[ PERM_EXEC ]} else ∅ ).

Definition rwx_encode (perm : gset perm_t) : byte :=
  (if decide (PERM_READ ∈ perm) then Byte.one else Byte.zero) |₈
  (if decide (PERM_WRITE ∈ perm) then Byte.repr 2 else Byte.zero) |₈
  (if decide (PERM_EXEC ∈ perm) then Byte.repr 4 else Byte.zero).

(** Syscall ABI: permissions occupy bits 63-56 and the PMP address occupies
    bits 55-0. Reserved permission bits are normalized to zero. *)
Definition pmpconf_unpack (raw : int64) : pmpconf_t :=
  (* 24 = 0x18 *)
  {| wpmp_conf := Byte.repr 24 |₈ (int64_to_byte (raw >>u₆₄ Int64.repr 56) &₈ Byte.repr 7);
     wpmp_addr := (raw <<₆₄ Int64.repr 8) >>u₆₄ Int64.repr 8 |}.

Definition pmpconf_pack (conf : pmpconf_t) : int64 :=
  (byte_to_int64 (conf.(wpmp_conf) &₈ Byte.repr 7) <<₆₄ Int64.repr 56) |₆₄
  ((conf.(wpmp_addr) <<₆₄ Int64.repr 8) >>u₆₄ Int64.repr 8).

Definition pmp_addr_decode (addr : int64) : int64 * int64 :=
  (((addr +₆₄ 1UL) &₆₄ addr) <<₆₄ 2UL,
   (((addr +₆₄ 1UL) ^₆₄ addr) +₆₄ 1UL) <<₆₄ 2UL).

(** Decode a RISC-V naturally aligned power-of-two PMP address into a
    permission set and a half-open byte range represented by base and size. *)
Definition pmp_decode (conf : pmpconf_t) : gset perm_t * nat * nat :=
  let perm := rwx_decode conf.(wpmp_conf) in
  let '(base, size) := pmp_addr_decode conf.(wpmp_addr) in
  (perm, int64_to_nat base, int64_to_nat size).

(** PMP syscall indices map directly to the eight modeled hardware slots. *)
Definition word2pmpreg (x : int64) : option pmpreg_t :=
  if decide (int64_to_nat x < PMP_CNT) then Some (num2pmpreg_t (int64_to_nat x))
  else None.

Definition word2pmpreg_opt (w : int64) : option (option pmpreg_t) :=
  if decide (w = Int64.zero) then Some None
  else Some <$> word2pmpreg (w -₆₄ Int64.one).
