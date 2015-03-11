(** Packet Header Fields. *)

Require Import List.

Module Type FIELDSPEC.
  Parameter t : Set. (* Set of fields *)
  Parameter all : list t.
  Parameter finite: forall f:t, In f all.
  Parameter eq_dec : forall x y : t, { x=y } + { ~x=y }.
  (* Parameter beq : F -> F -> bool. *)
End FIELDSPEC.

Require Import Ensembles.
Require Import Finite_sets.

Module Type FIELDSPEC'.
  Parameter FU : Set. (* Universe of fields *)
  Parameter F : Ensemble FU. (* Set of fields *)
  Parameter finite : Finite FU F.
  Parameter eq_dec : forall x y : FU, { x=y } + { ~x=y }.
  (* Parameter beq : F -> F -> bool. *)
End FIELDSPEC'.