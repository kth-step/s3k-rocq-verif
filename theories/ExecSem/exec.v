From stdpp Require Import prelude.
From RecordUpdate Require Import RecordUpdate.
From compcert Require Import Integers.
From S3K Require Import cap kstate.

(** * Executable semantics for S3K *)

(** ** Error code definitions *)

Definition err_success (n : nat) : int64 :=
  Int64.repr (Z.of_nat n).

Definition err_invalid_syscall : int64 :=
  Int64.repr (-1).

Definition err_invalid_access : int64 :=
  Int64.repr (-2).

Definition err_invalid_argument : int64 :=
  Int64.repr (-3).

Definition err_invalid_state : int64 :=
  Int64.repr (-4).

(** ** Monitor operations *)

Definition exec_mon_delete (kstate : kstate_t) (owner : nat) (i : nat) : (kstate_t * int64):=
  match cap_owner_get kstate.(kmon_tbl) owner i with
  | None => (kstate, err_invalid_access)
  | Some ci => 
      let ci' := ci <| (@cowner mon_t) := None |> in
      let kmon_tbl' := cap_set kstate.(kmon_tbl) i (Some ci') in
      let kstate' := kstate <| kmon_tbl := kmon_tbl' |> in
      (kstate', err_success 0)
  end.

(** ** Time slice operations *)

(** ** Memory operations *)

(** ** System calls *)

(** ** Syscall handler definitions *)

