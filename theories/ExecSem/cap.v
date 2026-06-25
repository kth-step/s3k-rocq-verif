From stdpp Require Import prelude gmap.
From S3K Require Import proc.

Set Implicit Arguments.

(** * Capability definitions *)

(** ** Capability datatypes *)
Record cap_t (A : Type) := mk_cap_t {
  cowner : option nat;
  cfree : nat;
  csize : nat;
  cdata : A;
}.

(** Capability table *)
Inductive cap_table_t (A : Type) := CapTable (l : list (option (cap_t A))).

Definition cap_get (A : Type) (ct : cap_table_t A) (i : nat) : option (cap_t A) :=
  match ct with CapTable l =>
    match l !! i with
    | None => None
    | Some v => v
    end
  end.

Definition cap_owner_get (A : Type) (τ : cap_table_t A) (p : nat) (i : nat) : option (cap_t A) :=
  match cap_get τ i with
  | None => None
  | Some v => if decide (v.(cowner) = Some p) then Some v else None
  end.

Definition cap_set (A: Type) (ct : cap_table_t A) (i : nat) (v : option (cap_t A)) : cap_table_t A :=
  match ct with CapTable l => CapTable (<[i := v]> l) end.

(** ** Monitor table *)

Record mon_t := {
  mpid : nat
}.

Definition mon_table_t := cap_table_t mon_t.

(** ** Time slice table *)

Record tsl_t := {
  thart : nat;
  tbase : nat;
  tsize : nat;
  tfree : nat;
}.

Definition tsl_table_t := cap_table_t tsl_t.

(** ** Memory table *)

Record mem_t := {
  mbase : nat;
  msize : nat;
  mslot : option pmpreg_t;
  mperm : gset perm_t;
}.

Definition mem_table_t := cap_table_t mem_t.

