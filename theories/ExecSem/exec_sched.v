From S3K Require Import core_cap core_tsl util.

Record sched_entry_t := {
  Spid : option nat;
  Slen : nat;
}.

Inductive sched_t := Sched (l : list sched_entry_t).

Definition sched_size (l: sched_t) :=
  match l with Sched l => length l end.

Definition sched_get (l: sched_t) (i: nat) :=
  match l with Sched l => l !! i end.

Definition sched_set (l: sched_t) (tsl: cap_t tsl_t) :=
  match l with Sched l =>
    let i := tsl.(Cdata).(Tbase) in
    let se := {| Spid := if tsl.(Cdata).(Tenable) then tsl.(Cowner) else None; Slen := tsl.(Cdata).(Tfree) |} in
    if decide (tsl.(Cdata).(Tfree) <> 0) then
      Sched (<[i := se]> l)
    else
      Sched l
  end.

