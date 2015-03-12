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

Lemma mk_union_sound: forall p q : policy, p + q === mk_union p q.
Proof.
  intros p q h.
  netkat_cases p q.
Qed.

Lemma mk_seq_sounds: forall p q : policy, p;q === mk_seq p q.
Proof.
  intros p q h.
  netkat_cases p q.
Qed.

End Optimize.