Require Import Equalities.
Require Import List.
Require Import FunctionalExtensionality.
Require Import Relations.
Require Import CpdtTactics.

Module set(X : UsualDecidableTypeFull).

Definition t := X.t -> Prop.

Definition empty : t := fun _ => False.

Definition full : t := fun _ => True.

Definition singleton (x : X.t) := fun y => x=y.

Definition list (xs : list X.t) := fun y => List.In y xs.

Definition union (A : t) (B : t) := fun x => A x \/ B x.

Definition eq : relation t := 
  fun A B => forall x, A x <-> B x.

Lemma eq_refl : Reflexive eq.
Proof. intros A x. reflexivity. Qed.

Lemma eq_sym : Symmetric eq.
Proof. intros A B H x. symmetry. apply (H x). Qed.

Lemma eq_trans : Transitive eq.
Proof. intros A B C H1 H2 x. rewrite -> (H1 x). apply (H2 x). Qed.

(* This allows us to use reflexivity, symmetry, and rewrite for set equality *)
Instance eq_equiv : Equivalence eq.
Proof. split; [apply eq_refl | apply eq_sym | apply eq_trans]. Qed.

Notation "A == B" := (eq A B) (at level 20, no associativity).
Hint Unfold eq.

Lemma union_assoc : forall A B C : t,
  union (union A B) C == union A (union B C).
Proof.
  intros A B C x.
  apply or_assoc.
Qed.

Lemma union_comm : forall A B : t,
  union A B == union B A.
Proof.
  intros A B x.
  apply or_comm.
Qed.

Lemma union_empty_right : forall A : t,
  union A empty == A.
Proof.
  intros A x.
  unfold union.
  unfold empty.
  crush.
Qed.

Lemma union_empty_left : forall A : t,
  union empty A == A.
Proof.
  intros A.
  rewrite -> union_comm.
  apply union_empty_right.
Qed.

Lemma union_mono_left : forall A B : t, forall x : X.t,
  A x -> union A B x.
Proof.
  intros.
  unfold union; left; assumption.
Qed.

Lemma union_mono_right : forall A B : t, forall x : X.t,
  B x -> union A B x.
Proof.
  intros.
  unfold union; right; assumption.
Qed.

Lemma union_idem : forall A : t,
  union A A == A.
Proof.
  intros A x.
  unfold union.
  crush.
Qed.

Lemma singleton_iff : forall x y: X.t,
  singleton x y <-> x=y.
Proof. unfold singleton. reflexivity. Qed.

Lemma singleton_refl : forall x : X.t,
  singleton x x.
Proof. unfold singleton. reflexivity. Qed.

Hint Unfold singleton full.
Hint Resolve union_empty_right union_empty_left union_idem singleton_refl.
Hint Rewrite union_empty_right union_empty_left union_idem.

End set.