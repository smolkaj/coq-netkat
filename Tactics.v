(** some useful custom tactics **)

Ltac if_case :=
  match goal with
    | [ |- context[if ?X then _ else _] ] => destruct X
  end.

Ltac invert id := inversion id; try(subst); eauto.

Ltac gd id := generalize dependent id.