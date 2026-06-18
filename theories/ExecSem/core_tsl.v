From S3K Require Import core_cap.

Record tsl := {
  Tenable : bool;
  Tbase : nat;
  Tsize : nat;
  Tfree : nat;
}.

Definition tsl_table := cap_table tsl.

