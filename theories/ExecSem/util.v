From stdpp Require Import prelude.
From compcert Require Import Integers.
From BarocqComp Require Import Intop.
Export IntopNotations.

(** * Utilities *)

Definition int64_to_n (i : int64) := Z.to_nat (Int64.unsigned i).

Definition n_to_int64 (i : nat) := Int64.repr (Z.of_nat i).

Infix "&₈" := Byte.and (at level 40,left associativity).

