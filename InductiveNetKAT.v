Require Export NetKAT.
Require Import List Coq.Program.Equality Bool.

Module NetKAT' (F : FIELDSPEC) (V : VALUESPEC(F)).

  Include NetKAT.NetKAT(F)(V).
  

  Inductive sem : policy -> H.t -> H.t -> Prop :=
  | SemId : forall h, sem Id h h
  | SemFilter : forall f v h, (fst h) f = v -> sem (Filter f v) h h
  | SemNFilter : forall f v h, (~ (fst h) f = v) -> sem (NFilter f v) h h
  | SemMod : forall f v h, sem (Mod f v) h ((fst h)[f:=v], snd h)
  | SemPlusLeft : forall h h' p q, sem p h h' -> sem (p+q) h h'
  | SemPlusRight : forall h h' p q, sem q h h' -> sem (p+q) h h'
  | SemSeq : forall h h' h'' p q, sem p h h' -> sem q h' h'' -> sem (p;q) h h''
  | SemStarRefl : forall h p, sem (p*) h h
  | SemStarTrans : forall h h' h'' p, sem p h h' -> sem (p*) h' h'' -> sem (p*) h h''
  | SemDup : forall h, sem Dup h (fst h, fst h :: snd h).

  Notation "'[||' p '||]'" := (sem p) (at level 1).

  Lemma sem_interpret : forall p h h', sem p h h' -> interpret p h h'.
  Proof.
    intros p h h' H.
    induction H; destruct h as [pk h]; simpl; try (simpl in H); auto.
    - rewrite <- V.eqb_eq in H.
      rewrite -> H.
      unfold HSet.singleton; reflexivity.
    - rewrite <- V.eqb_eq in H.
      rewrite if_negb.
      case (V.eqb f (pk f) v) eqn:H'.
      + intuition.
      + auto.
    - left; assumption.
    - right; assumption.
    - exists h'. intuition.
    - exists 0; simpl; auto.
    - destruct IHsem2 as [n].
      exists (S n). simpl. exists h'. intuition.
  Qed.

  Lemma interpret_sem : forall p h h', interpret p h h' -> sem p h h'.
  Proof.
    intros p.
    induction p; intros h h' H; destruct h as [pk h];
    simpl in H; try (unfold HSet.empty in H); try (unfold HSet.singleton in H);
    try (subst h'; constructor); try contradiction.
    - case (V.eqb f (pk f) t) eqn: H'.
      + rewrite V.eqb_eq in H'. subst h'. constructor. auto.
      + contradiction.
    - case (V.eqb f (pk f) t) eqn: H'; simpl in H.
      + contradiction.
      + subst h'. constructor. simpl. rewrite <- V.eqb_eq. intuition.
        rewrite H in H'. inversion H'.
    - destruct H; [apply SemPlusLeft|apply SemPlusRight]; intuition.
    - destruct H as [h'']. apply (SemSeq _ h''); intuition.
    - destruct H as [n].
      generalize dependent pk; generalize dependent h; generalize dependent h';
      induction n; intros h' h pk H; simpl in H.
      + unfold HSet.singleton in H. subst h'. constructor.
      + destruct H as [h'']. apply (SemStarTrans _ h'');
        destruct h'' as [pk'' h'']; intuition.
    Qed.

End NetKAT'.