From stdpp Require Import prelude.
From RecordUpdate Require Import RecordUpdate.

(** * Context *)

(** Ephemeral kernel state per hart*)
Record hstate_t := mk_hstate_t {
  (* Active process *)
  hcurrent : option nat;
  (* Timeout *)
  htimeout : nat;
}.

(** Kernel context, the ephemeral part of the kernel state *)
Record ctx_t := mk_ctx_t {
  (* HW thread -> active process *)
  ctx_hstate : list hstate_t;
  (* PID -> busy flag *)
  ctx_busy : list bool;
}.

Definition ctx_current (h : nat) (ctx : ctx_t) : option nat :=
  match ctx.(ctx_hstate) !! h with
  | None => None
  | Some hstate => hstate.(hcurrent)
  end.

Definition ctx_busy_at (p : nat) (ctx : ctx_t) : bool :=
  match ctx.(ctx_busy) !! p with
  | None => false
  | Some b => b
  end.

Definition ctx_release (h : nat) (ctx : ctx_t) : option ctx_t :=
  match ctx.(ctx_hstate) !! h with
  | None => None
  | Some hstate =>
      match hstate.(hcurrent) with
      | None => None
      | Some p =>
          let hstate' := hstate <| hcurrent := None |> in
          Some (ctx <| ctx_hstate ::= <[ h := hstate' ]> |>
                    <| ctx_busy ::= <[ p := false ]> |>)
      end
  end.

Definition ctx_acquire (h : nat) (ctx : ctx_t) (p : nat) (to_opt : option nat)
  : option ctx_t :=
  match ctx.(ctx_hstate) !! h with
  | None => None
  | Some hstate =>
      match hstate.(hcurrent) with
      | None =>
          let hstate' := hstate
            <| hcurrent := Some p |>
            <| htimeout :=
                 match to_opt with
                 | None => hstate.(htimeout)
                 | Some to => to
                 end
            |> in
          Some (ctx <| ctx_busy ::= <[ p := true ]> |>
                    <| ctx_hstate ::= <[ h := hstate' ]> |>)
      | Some _ => None
      end
  end.

Definition ctx_yield (h : nat) (ctx : ctx_t) (p_opt : option nat)
  : option ctx_t :=
  match ctx_release h ctx with
  | None => None
  | Some ctx' =>
      match p_opt with
      | None => Some ctx'
      | Some p => ctx_acquire h ctx' p None
      end
  end.

