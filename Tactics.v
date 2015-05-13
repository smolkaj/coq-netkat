(** some useful custom tactics **)
Require Import Bool Classes List.

Ltac split_if :=
  match goal with
    | [ |- context[if ?X then _ else _] ] => destruct X
    | [ _ : context[if ?X then _ else _] |- _ ] => destruct X
  end.

Ltac invert H := inversion H; try(subst); eauto.

Ltac gd id := generalize dependent id.


Create HintDb __bool_reflection.

Hint Rewrite
  (* rewrite rules from Bool.v *)
  not_true_iff_false not_false_iff_true
  negb_orb negb_involutive if_negb negb_true_iff negb_false_iff
  orb_true_iff orb_false_iff orb_diag orb_true_r orb_true_l orb_false_r
    orb_false_l orb_negb_r orb_assoc
  andb_true_iff andb_false_iff andb_false_r andb_false_l andb_diag
    andb_true_r andb_true_l andb_negb_r andb_assoc absorption_andb absorption_orb
  (* xorb_false_r xorb_false_l xorb_true_r xorb_true_l xorb_nilpotent xorb_negb_negb *)
  andb_if negb_if
  (* rewrite rules from Classes.v *)
  exists_false existsb_false exists_iff
  (* rewrite rules from List.v *)
  existsb_exists existsb_app forallb_app forallb_forall
: __bool_reflection.

Ltac steffen_rewrite := 
  autorewrite with __bool_reflection in *.


Ltac steffen :=
repeat (first [
  match goal with
    | [ H : _ /\ _ |- _ ] => destruct H
    | [ H : exists x, _ |- _ ] => destruct H as [x H]
    | [ H : exists x, _ |- _ ] => destruct H
    | [ H : context [eqb _ _ = true] |- _ ] => rewrite eqb_eq in H
    | [ H : context [eqb _ _ = false] |- _ ] => rewrite eqb_eq_false in H
    | [ |- context [eqb _ _ = true] ] => rewrite eqb_eq
    | [ |- context [eqb _ _ = false] ] => rewrite eqb_eq_false
  end |
  steffen_rewrite
]).
  

(* eq_iff_eq_true  *)
