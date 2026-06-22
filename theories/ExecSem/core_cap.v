From stdpp Require Import prelude propset.

Set Implicit Arguments.

(** Capability datatype *)
Record cap_t (A : Type) := {
  Cowner : option nat;
  Cfree : nat;
  Csize : nat;
  Cdata : A;
}.

(** Capability table *)
Inductive cap_table_t (A : Type) := CapTable (l : list (option (cap_t A))).

Definition cap_get {A} (ct : cap_table_t A) (i : nat) : option (cap_t A) :=
  match ct with CapTable l =>
    match l !! i with
    | None => None
    | Some v => v
    end
  end.

Definition cap_set {A} (ct : cap_table_t A) (i : nat) (v : option (cap_t A)) : cap_table_t A :=
  match ct with CapTable l => CapTable (<[i := v]> l) end.

(* To be added as needed.

Definition cap_range {A} (ct : cap_table_t A) (i : nat) :=
  match cap_get ct i with
  | None => empty
  | Some v => {[ j | i <= j /\ j < i + v.(Csize) ]}
  end.

Definition cap_frange {A} (ct : cap_table_t A) (i : nat) :=
  match cap_get ct i with
  | None => empty
  | Some v => {[ j | i <= j /\ i + j < v.(Cfree) ]}
  end.

Definition cap_table_size {A} (ct : cap_table_t A) := length ct.

Record cap_wf {A} (ct: cap_table_t A) := {
  cap_wf_free_size : 
    forall i c, cap_get ct i = Some c -> 0 < c.(Cfree) <= c.(Csize);
  cap_wf_valid_index :
    forall i j, j ∈ cap_range ct i -> j < cap_table_size ct;
  cap_wf_partitioned :
    forall i j, j ∈ cap_range ct i -> exists k, j ∈ cap_frange ct k;
  cap_wf_nested :
    forall i j, j ∈ cap_range ct i -> cap_range ct j ⊆ cap_range ct i;
  cap_wf_frange_free :
    forall i j, i <> j /\ j ∈ cap_frange ct i -> cap_get ct j = None;
}.

*)
