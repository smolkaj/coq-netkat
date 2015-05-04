Require Import List.


Fixpoint list_eqb {X : Type} (eqb : X -> X -> bool) (xs : list X) (ys : list X) : bool :=
  match xs, ys with
  | nil, nil => true
  | cons x xs, cons y ys => andb (eqb x y) (list_eqb eqb xs ys)
  | _,_ => false
  end.

Lemma list_eqb_eq : forall {X : Type}, forall (eqb : X -> X -> bool),
  forall p : (forall x y : X, eqb x y = true <-> x = y),
  forall l1 l2 : list X, list_eqb eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros X eqb p l1.
  induction l1; intros; destruct l2; intuition; try solve [inversion H].
  + assert (eqb a x = true /\ list_eqb eqb l1 l2 = true) by auto using
    andb_prop.
    destruct H0. apply p in H0. apply IHl1 in H1.
    congruence.
  + inversion H; subst; simpl. 
    apply andb_true_intro; split.
    - apply p. reflexivity.
    - apply IHl1. reflexivity.
Qed.

Lemma list_eq_dec {X} (eq_dec : forall x y:X, {x=y}+{x<>y}) (xs ys : list X) :
  {xs=ys}+{xs<>ys}.
Proof.
  pose (eqb := fun x y => if eq_dec x y then true else false).
  assert (forall x y, eqb x y = true <-> x = y).
  + intros. subst eqb. split; intro H;
    simpl in H; destruct (eq_dec x y); auto; inversion H.
  + assert (H' := list_eqb_eq eqb H xs ys).
    destruct (list_eqb eqb xs ys); [left|right]; intuition.
Qed.
