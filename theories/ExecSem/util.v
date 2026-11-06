From stdpp Require Import prelude.
From compcert Require Import Integers.

(** * Utilities *)

(** [w2n] and [n2w] for 64-bit words *)
Definition int64_to_nat (i : int64) := Z.to_nat (Int64.unsigned i).

Definition nat_to_int64 (i : nat) := Int64.repr (Z.of_nat i).

(** [w2w] between 64-bit and 8-bit words *)
Definition int64_to_byte (i : int64) : byte := Byte.repr (Int64.unsigned i).

Definition byte_to_int64 (b : byte) : int64 := Int64.repr (Byte.unsigned b).

Infix "&₈" := Byte.and (at level 40,left associativity).
Infix "|₈" := Byte.or (at level 50,left associativity).

(** Decidable equality on machine words, so that word (in)equalities of the
    specification can be used with [decide] and [bool_decide]. *)
#[export] Instance byte_eq_dec : EqDecision byte := Byte.eq_dec.
#[export] Instance int64_eq_dec : EqDecision int64 := Int64.eq_dec.

(** Used by total list lookup [!!!], the counterpart of HOL4's [EL]. *)
#[export] Instance int64_inhabited : Inhabited int64 := populate Int64.zero.
