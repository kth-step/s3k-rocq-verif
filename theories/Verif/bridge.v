From stdpp Require Import prelude.
From RecordUpdate Require Import RecordUpdate.
From compcert Require Import Integers.
From S3K.ExecSem Require Import kstate cap exec.

Definition exec_mon_revoke' (kstate : kstate_t) (owner : nat) (i : nat) : option (kstate_t * int64) :=
  match cap_owner_get kstate.(kmon_tbl) owner i with
  | None => Some (kstate, err_invalid_access)
  | Some ci =>
    if decide (ci.(cfree) < ci.(csize)) then
      let j := i + ci.(cfree) in
      match cap_get kstate.(kmon_tbl) j with
      | None => None
      | Some cj =>
        let ci' := ci <| (@cfree mon_t) := ci.(cfree) + cj.(cfree) |> in
        let kmon_tbl' := cap_set kstate.(kmon_tbl) (i, (Some ci')) in
        match cap_get kmon_tbl' j with
        | None => None
        | Some cj =>
          let kmon_tbl'' := cap_set kmon_tbl' (j, None) in
          let kstate' := kstate <| kmon_tbl := kmon_tbl'' |> in
          Some (kstate', err_success (ci'.(csize) - ci'.(cfree)))
        end
      end
    else 
      Some (kstate, err_success 0)
  end.
