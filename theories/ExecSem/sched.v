From stdpp Require Import prelude.

(** * Scheduler definitions *)

(** Scheduler data structure per hart *)
Inductive hsched_t := HSched : list (option nat * nat) -> hsched_t.

(** Scheduler datatype *)
Definition sched_t := list hsched_t.

Definition hsched_size (h : hsched_t) : nat :=
  match h with HSched hsched => length hsched end.

Definition hsched_set 
    (h : hsched_t) (i : nat) (p_opt : option nat) (len : nat)
  : hsched_t :=
  match h with HSched hsched => HSched (<[ i := (p_opt, len) ]> hsched) end.

Definition sched_set
    (sched : sched_t) (h i : nat) (p_opt : option nat) (len : nat)
  : sched_t :=
  match sched !! h with
  | None => sched
  | Some hsched => <[ h := hsched_set hsched i p_opt len ]> sched
  end.

Definition hsched_get (h : hsched_t) (i : nat) : option (option nat * nat) :=
  match h with HSched hsched => hsched !! i end.

Definition sched_get (sched : sched_t) (h i : nat) : option (option nat * nat) :=
  match sched !! h with
  | None => None
  | Some hsched => hsched_get hsched i
  end.

