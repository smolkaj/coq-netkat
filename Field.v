(** Packet Header Fields. *)
Require Import List Classes.

Module Type FIELDSPEC.
  Parameter t : Set. (* Set of fields *)
  Parameter finite : Finite t.
  Parameter eq_dec : EqType t.
  Global Instance : Finite t := finite.
  Global Instance : EqType t := eq_dec.
End FIELDSPEC.
