Set Implicit Arguments.

Require Import Equalities.
Require Import List.
Require Import FunctionalExtensionality.
Require Import Relations.
Require Import Classes.

Section set.

Variable X : Type.
Context `{EqType X}.

Definition set := X -> Prop.

Implicit Types x y z : X.
Implicit Types A B C : set.

Definition empty : set := fun _ => False.

Definition full : set := fun _ => True.

Definition singleton x : set := fun y => x=y.

Definition list xs : set := fun y => List.In y xs.

Definition union A B : set := fun x => A x \/ B x.

Definition eq : relation set := 
  fun A B => forall x, A x <-> B x.

Lemma eq_refl : Reflexive eq.
Proof. intros A x; reflexivity. Qed.

Lemma eq_sym : Symmetric eq.
Proof. intros A B H0 x. symmetry. apply (H0 x). Qed.

Lemma eq_trans : Transitive eq.
Proof. intros A B C H1 H2 x. rewrite -> (H1 x). apply (H2 x). Qed.

(* This allows us to use reflexivity, symmetry, and rewrite for set equality *)
Global Instance eq_equiv : Equivalence eq.
Proof. split; [apply eq_refl | apply eq_sym | apply eq_trans]. Qed.

Notation "A == B" := (eq A B) (at level 20, no associativity) : set_scope.
Hint Unfold eq.
Open Scope set_scope.

Lemma union_assoc : forall A B C,
  union (union A B) C == union A (union B C).
Proof.
  intros A B C x.
  apply or_assoc.
Qed.

Lemma union_comm : forall A B,
  union A B == union B A.
Proof.
  intros A B x.
  apply or_comm.
Qed.

Lemma union_empty_right : forall A,
  union A empty == A.
Proof.
  intros A x.
  unfold union.
  unfold empty.
  intuition.
Qed.

Lemma union_empty_left : forall A,
  union empty A == A.
Proof.
  intros A.
  rewrite -> union_comm.
  apply union_empty_right.
Qed.

Lemma union_mono_left : forall A B x,
  A x -> union A B x.
Proof.
  intros.
  unfold union; left; assumption.
Qed.

Lemma union_mono_right : forall A B x,
  B x -> union A B x.
Proof.
  intros.
  unfold union; right; assumption.
Qed.

Lemma union_idem : forall A,
  union A A == A.
Proof.
  intros A x.
  unfold union.
  intuition.
Qed.

Lemma singleton_iff : forall x y,
  singleton x y <-> x=y.
Proof. intuition. Qed.

Lemma singleton_refl : forall x,
  singleton x x.
Proof. intuition. Qed.

End set.

Hint Unfold singleton full empty.
Hint Resolve singleton full empty.

