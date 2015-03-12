(** Packet Header Fields. *)

Require Import List.

Module Type FIELDSPEC.
  Parameter t : Set. (* Set of fields *)
  Parameter all : list t.
  Parameter finite: forall f:t, In f all.
  Parameter eq_dec : forall x y : t, { x=y } + { ~x=y }.
  (* Parameter beq : F -> F -> bool. *)
End FIELDSPEC.
