Require Import List FunctionalExtensionality.
Import ListNotations.



(* decidable sets *)
Definition pred T := T -> bool.

Notation "x \in L" := (L x) (at level 30, L at next level, only parsing) : bool_scope.
Notation "[$ x | B ]" := (fun x => B) (at level 0, x ident, only parsing) : bool_scope.
Notation "[$ x : T | B ]" := (fun x : T => B) (at level 0, x ident, only parsing) : bool_scope.

Open Scope bool_scope.

Theorem pred_eq_intro {X} (B1 B2 : X -> bool) : 
  (forall x, B1 x = true <-> B2 x = true) -> [$ x | B1 x ] = [$ x | B2 x ].
Proof.
  intro H.
  extensionality x.
  assert (H0 := H x); clear H.
  case_eq(B1 x); case_eq(B2 x); intros H1 H2; intuition; congruence.
Qed.





Definition injective {A B} (f : A -> B) := 
  forall x y : A, f x = f y -> x = y.

Definition surjective {A B} (f : A -> B) := 
  forall y : B, exists x : A, f x = y.

Inductive bijective {A B} (f: A -> B) :=
  is_bijective : injective f -> surjective f -> bijective f.

Hint Constructors bijective.




Lemma rev_eq_nil {X} {xs : list X} : rev xs = [] -> xs = [].
Proof.
  intro H. destruct xs. reflexivity.
  assert(length (@nil X) = length (x::xs)). rewrite <- H. apply rev_length.
  inversion H0.
Qed.

Lemma rev_eq_singleton {X} {xs : list X} {x} : rev xs = [x] -> xs = [x].
Proof.
  intro H. destruct xs as [ |y[ |z xs]]. inversion H. simpl in H. assumption.
  assert(length ([x]) = length (y::z::xs)). rewrite <- H. apply rev_length.
  inversion H0.
Qed.