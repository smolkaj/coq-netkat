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
  induction l1.
    destruct l2; intuition. inversion H. inversion H.
  intros l2.
  destruct l2; intuition.
  inversion H. inversion H.
  assert (eqb a x = true /\ list_eqb eqb l1 l2 = true) as H0.
    apply andb_prop; assumption.
  destruct H0.
  rewrite -> (p a x) in H0.
  rewrite -> (IHl1 l2) in H1.
  subst a l1.
  reflexivity.
  apply andb_true_intro.
  rewrite -> (p a x).
  rewrite -> (IHl1 l2).
  inversion H.
  split; reflexivity.
Qed.