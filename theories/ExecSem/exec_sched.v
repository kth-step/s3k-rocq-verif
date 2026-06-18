From S3K Require Import core_cap core_tsl util.

Record sched_entry := {
  Spid : option nat;
  Slen : nat;
}.

Definition sched := list sched_entry.

Definition sched_size (l: sched) := length l.

Definition sched_get (l: sched) (i: nat) := nth_error l i.

Definition sched_set (l: sched) (tsl: cap tsl) :=
  let i := tsl.(Cdata).(Tbase) in
  let se := {| Spid := if tsl.(Cdata).(Tenable) then tsl.(Cowner) else None; Slen := tsl.(Cdata).(Tfree) |} in
  if (tsl.(Cdata).(Tfree) <> 0)? then
    <[i := se]> l
  else
    l.

