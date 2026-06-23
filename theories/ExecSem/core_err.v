From stdpp Require Import prelude.
From compcert Require Import Integers.
From Stdlib Require Import ZArith.

(** * Error code definitions *)

Definition err_success (n: nat) : int64 := Int64.repr (Z.of_nat n).

Definition err_invalid_access : int64 := Int64.mone.

Definition err_invalid_argument : int64 := Int64.repr (-2).

Definition err_invalid_syscall : int64 := Int64.repr (-6).

