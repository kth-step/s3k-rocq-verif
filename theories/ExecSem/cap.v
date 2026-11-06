From stdpp Require Import prelude gmap.
From S3K.ExecSem Require Import proc.

Set Implicit Arguments.

(** * Capability definitions *)

Section Cap.

Variable A : Type.

(** ** Capability datatypes *)

(** A capability occupies [csize] table indices. Its first [cfree] indices form
    the unallocated prefix available for deriving children; [None] owner means
    unowned. *)
Record cap_t := mk_cap_t {
  cowner : option nat;
  cfree : nat;
  csize : nat;
  cdata : A;
}.

(** Capability table *)
Definition cap_table_t := list (option cap_t).

(** [None] is out of bounds; [Some None] is an empty slot. *)
Definition cap_get (l : cap_table_t) (i : nat) : option (option cap_t) :=
  l !! i.

(** Empty, out-of-bounds, and wrong-owner slots all fail authorization. *)
Definition cap_owner_get (τ : cap_table_t) (p : nat) (i : nat) : option cap_t :=
  match cap_get τ i with
  | None => None
  | Some None => None
  | Some (Some ci) => if decide (ci.(cowner) = Some p) then Some ci else None
  end.

(** Writes beyond the fixed table extent are no-ops. *)
Definition cap_set (l : cap_table_t) '(i, v) : cap_table_t :=
  <[ i := v ]> l.

Definition ctable_size (l : cap_table_t) : nat :=
  length l.

Definition cap_upd (τ : cap_table_t) '(i, v) : option cap_table_t :=
  if decide (i < ctable_size τ) then Some (cap_set τ (i, v)) else None.

End Cap.

(** ** Monitor table *)

Record mon_t := mk_mon_t {
  mpid : nat
}.

Definition mon_table_t := cap_table_t mon_t.

Definition mon_get (τ : mon_table_t) (i : nat) : option nat :=
  match cap_get τ i with
  | None => None
  | Some None => None
  | Some (Some ci) => Some ci.(cdata).(mpid)
  end.

(** ** Time slice table *)

(** A time-slice capability covers a half-open slot interval on one hart. *)
Record tsl_t := mk_tsl_t {
  thart : nat;
  tbase : nat;
  tsize : nat;
  tfree : nat;
}.

Definition tsl_table_t := cap_table_t tsl_t.

(** ** Memory table *)

(** A memory capability carries an address range, permissions, and at most one
    process PMP slot currently realizing that authority. *)
Record mem_t := mk_mem_t {
  mbase : nat;
  msize : nat;
  mslot : option pmpreg_t;
  mperm : gset perm_t;
}.

Definition mem_table_t := cap_table_t mem_t.

Definition mem_mslot (τ : mem_table_t) (i : nat) : option pmpreg_t :=
  match cap_get τ i with
  | None => None
  | Some None => None
  | Some (Some c) => c.(cdata).(mslot)
  end.
