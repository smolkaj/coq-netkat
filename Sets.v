Require Import Equalities.
Require Import List.
Require Import FunctionalExtensionality. 

Module set(X : UsualDecidableTypeFull).

Definition t := X.t -> Prop.

Definition empty : t := fun _ => False.

Definition full : t := fun _ => True.

Definition singleton (x : X.t) := fun y => x=y.

Definition list (xs : list X.t) := fun y => List.In y xs.

Definition union (A : t) (B : t) := fun x => A x \/ B x.

Definition eq (A B : t) := forall x : X.t, A x <-> B x.

Notation "A == B" := (eq A B) (at level 20, no associativity).

Hint Unfold eq.

Lemma union_assoc : forall A B C : t,
  union (union A B) C == union A (union B C).
Proof.
  intros A B C x.
  apply or_assoc.
Qed.

End set.