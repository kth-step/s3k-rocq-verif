From S3K Require Import core_cap.

Record tsl_t := {
  Tenable : bool;
  Tbase : nat;
  Tsize : nat;
  Tfree : nat;
}.

Definition tsl_table_t := cap_table_t tsl_t.

