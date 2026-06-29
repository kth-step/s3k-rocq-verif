From stdpp Require Import prelude gmap.
From S3K.ExecSem Require Import proc.

Set Implicit Arguments.

(** * Capability definitions *)

Section Cap.

Variable A : Type.

(** ** Capability datatypes *)

Record cap_t := mk_cap_t {
  cowner : option nat;
  cfree : nat;
  csize : nat;
  cdata : A;
}.

(** Capability table *)
Inductive cap_table_t := CapTable (l : list (option cap_t)).

Definition cap_get (ct : cap_table_t) (i : nat) : option cap_t :=
  match ct with CapTable l =>
    match l !! i with
    | None => None
    | Some v => v
    end
  end.

Definition cap_owner_get (τ : cap_table_t) (p : nat) (i : nat) : option cap_t :=
  match cap_get τ i with
  | None => None
  | Some v => if decide (v.(cowner) = Some p) then Some v else None
  end.

Definition cap_set (ct : cap_table_t) '(i, v)  : cap_table_t :=
  match ct with CapTable l => CapTable (<[ i := v ]> l) end.

End Cap.

(** ** Monitor table *)

Record mon_t := mk_mon_t {
  mpid : nat
}.

Definition mon_table_t := cap_table_t mon_t.

(** ** Time slice table *)

Record tsl_t := mk_tsl_t {
  thart : nat;
  tbase : nat;
  tsize : nat;
  tfree : nat;
}.

Definition tsl_table_t := cap_table_t tsl_t.

(** ** Memory table *)

Record mem_t := mk_mem_t {
  mbase : nat;
  msize : nat;
  mslot : option pmpreg_t;
  mperm : gset perm_t;
}.

Definition mem_table_t := cap_table_t mem_t.

