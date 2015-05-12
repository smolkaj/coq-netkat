(** Packet Header Values. *)
Require Import Field List Classes.
Import ListNotations.

Module Type VALUESPEC (Import F : FIELDSPEC).
  Parameter t : F.t -> Set.
  Parameter finite : forall f, Finite (t f).
  Parameter eq_dec : forall f : F.t, EqType (t f).
  Global Instance is_finite : forall f, Finite (t f) := finite.
  Global Instance is_eqtype : forall f, EqType (t f) := eq_dec.
End VALUESPEC.
