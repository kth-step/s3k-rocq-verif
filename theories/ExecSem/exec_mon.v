From stdpp Require Import prelude.
From RecordUpdate Require Import RecordUpdate.
From compcert Require Import Integers.
From S3K Require Import core_cap core_err exec_kernel.

(** * Executable semantics for monitor capability operations *)

Definition exec_mon_delete (ek : exec_kstate_t) (owner : nat) (i : nat) : (exec_kstate_t * int64):=
  match cap_owner_get ek.(Kstate).(Kmon_tbl) owner i with
  | None => (ek, err_invalid_access)
  | Some ci => 
      let ci' := ci <| (@Cowner nat) := None |> in
      let kmon_tbl' := cap_set ek.(Kstate).(Kmon_tbl) i (Some ci') in
      let kstate' := ek.(Kstate) <| Kmon_tbl := kmon_tbl' |> in
      (ek <| Kstate := kstate' |>, err_success 0)
  end.

