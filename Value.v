Require Import Field.
Require Import List.
Import ListNotations.

Module Type VALUESPEC (Import F : FIELDSPEC).
  Parameter t : F.t -> Set.
  Parameter eqb : forall f : F.t, t f -> t f -> bool.
  Parameter eqb_eq : forall f : F.t, forall x y : t f,
    eqb f x y = true <-> x = y.
  Parameter eq_dec : forall f : F.t, forall x y : t f,
    {x=y} + {x<>y}.
End VALUESPEC.
