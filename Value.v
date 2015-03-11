Require Import Field.
Require Import List.
Import ListNotations.
Require Import Equalities.

Module Type VALUESPEC (Import F : FIELDSPEC).
  Parameter t : F.t -> Set.
  Parameter all : forall f:F.t, list (t f).
  Parameter finite : forall f:F.t, forall v : (t f), In v (all f).
  Parameter eqb : forall f : F.t, t f -> t f -> bool.
  Parameter eqb_eq : forall f : F.t, forall x y : t f, eqb f x y = true <-> x = y.
End VALUESPEC.
