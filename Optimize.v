Require Export NetKAT.

Module Optimize (F : FIELDSPEC) (V : VALUESPEC(F)).

Include NetKAT.NetKAT(F)(V).

Definition mk_union (p1 p2 : policy) :=
  match p1,p2 with
    | Drop, _ => p2
    | _, Drop => p1
    | _,_ => p1 + p2
  end.

Definition mk_seq (p1 p2 : policy) :=
  match p1,p2 with
    | Drop, _
    | _, Drop => Drop
    | Id, _ => p2
    | _, Id => p1
    | _, _ => p1;; p2
  end.

Fixpoint mk_star (p : policy) :=
  match p with
    | Drop
    | Id => Id
    | q* => mk_star q 
    | _ => p*
  end.

Fixpoint optimize (p : policy) :=
  match p with
    | p1 + p2 => mk_union (optimize p1) (optimize p2)
    | p1;; p2 => mk_seq (optimize p1) (optimize p2)
    | p0* => mk_star (optimize p0)
    | _ => p
  end.



Lemma mk_union_sound: forall p q : policy, mk_union p q === p + q.
Proof. netkat_cases. Qed.

Lemma mk_seq_sound: forall p q : policy, mk_seq p q === p;;q.
Proof. netkat_cases. Qed.

Lemma star_zero: Drop* === Id.
Proof. rewrite <- ka_unroll_l. netkat. Qed.
Hint Rewrite star_zero : netkat.

Lemma star_one_aux: forall n h, eq (power n [|Id|] h) ([|Id|] h).
Proof.
  induction n; intros h h'; intuition.
  simpl in H. destruct H as [h'' [H0 H1]].
  + apply IHn in H1. congruence.
  + simpl. exists h. intuition. apply IHn. assumption.
Qed.

Lemma star_one: Id* === Id.
Proof.
  intros h h'.
  split; intros H.
  destruct H as [n].
  apply (star_one_aux n h). assumption.
  exists 0. simpl. apply H.
Qed.
Hint Rewrite star_one : netkat.

Lemma star_star p: p * * === p*.
Proof.
  intro h. split; intro H;
  destruct H as [n H]; generalize dependent x; generalize dependent h;
  induction n; intros.
  - exists 0. auto.
  - repeat destruct H.
    assert ([|p*|] x0 x) by eauto.
    destruct H1 as [m H1].
    exists ((x1 + m)%nat).
    apply power_decompose.
    exists x0; intuition.
  - exists 0. auto.
  - simpl in H. destruct H as [h'' [H0 H1]].
    assert (H2 := IHn _ _ H1); clear IHn H1 n.
    destruct H2 as [n]. exists (S n). simpl. exists h''.
    intuition. exists 1. simpl. exists h''; auto.
Qed.
Hint Rewrite star_star : netkat.
  

Lemma mk_star_sound p: mk_star p === p*.
Proof. netkat_induction p. Qed.

Hint Rewrite mk_union_sound mk_seq_sound mk_star_sound : netkat.

Theorem optimize_sound p: optimize p === p.
Proof. netkat_induction p. Qed.

Print optimize_sound.


End Optimize.