Require Import NetKAT.
Require Import CpdtTactics.

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
    | _, _ => p1; p2
  end.

Definition mk_star (p : policy) :=
  match p with
    | Drop
    | Id => Id
    | _ => p*
  end.

Fixpoint optimize (p : policy) :=
  match p with
    | p1 + p2 => mk_union (optimize p1) (optimize p2)
    | p1; p2 => mk_seq (optimize p1) (optimize p2)
    | p0* => mk_star p0
    | _ => p
  end.

Lemma mk_union_sound: forall p q : policy, mk_union p q === p + q.
Proof.
  intros p q.
  netkat_cases p q.
Qed.

Lemma mk_seq_sound: forall p q : policy, mk_seq p q === p;q.
Proof.
  intros p q.
  netkat_cases p q.
Qed.

Lemma mk_star_sound: forall p : policy, mk_star p === p*.
Proof.
  admit.
Qed.

Hint Rewrite mk_union_sound mk_seq_sound mk_star_sound.
Hint Resolve mk_union_sound mk_seq_sound mk_star_sound.

Theorem optimize_sound: forall p : policy, p === optimize p.
Proof.
  intros p.
  induction p; simpl; try reflexivity;
    [rewrite mk_union_sound | rewrite mk_seq_sound | rewrite mk_star_sound].
      symmetry. rewrite <- IHp2. rewrite ka_plus_comm. rewrite <- IHp1.
      rewrite ka_plus_comm. reflexivity.
    rewrite <- IHp2. (* axiomatic reasoning fails :( *)
      intros h h'.
      split; (intros H; destruct H as [h'']; exists h'';
      split; [apply IHp1| ]; intuition).
  reflexivity.
Qed.

End Optimize.