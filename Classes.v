Require Import List.
Import ListNotations.
Require Import Relations Morphisms.

Class eqType (X : Type) : Type := eq_dec : forall x y : X, {x=y} + {x<>y}.

Class Finite {X} `{eqType X} : Type := enum : {xs: list X|forall x, In x xs}.

Definition test `{eqType X} := X.

Check Set.

Check count_occ.

Program Instance : Finite := [true;false].
Next Obligation. destruct x; intuition. Qed.

Program Instance : Finite := [I].
Next Obligation. destruct x; intuition. Qed.

Program Instance : @Finite False := [].

Eval compute in seq 0 3.
Check length.

Program Fixpoint seq' (n:nat) : {l | length l = n} := seq 0 n.
Next Obligation. apply seq_length. Qed.

Program Fixpoint weaken {n:nat} (xs : list {x|x<n}) : list {x|x<S n} :=
match xs with
  | [] => []
  | x::xs => x :: weaken xs
end.

Program Fixpoint seq'' (n:nat) : list {m|m<n} :=
match n with
  | O => []
  | S n => n :: weaken (seq'' n)
end.

Eval compute in map (proj1_sig _ _) (seq'' 4).

Program Instance test (n:nat) : @Finite {m|m<n} := seq' n.

Lemma ex : @Finite bool.
Proof. intuition. Qed.

Class Finite (X:Set) : Type := {
  enumeration : list X;
  enumerate : forall x : X, In x enumeration
}.

Class SemiGroup (G : Type) (e : relation G) (op : G -> G -> G) : Prop := {
  sg_setioid : Equivalence e;
  sg_proper : Proper (e ==> e ==> e) op
}.


}

Theorem example `{Finite X} : enumeration = enumeration.

Print X.

Parameter F : Finite.

Class FinTy : Type := {
  X :> Set;
  Y : Finite(X)
}.

Coercion (Finite X) >-> X.

Parameter A : FinTy.

Program Fixpoint weaken {n} (xs : list {m|m<n}) : list {m|m<S n} :=
match xs with
  | [] => []
  | x::xs => x :: weaken xs
end.

Eval compute in weaken [].

Check enumeration.
Print enumeration.

Check X.
Parameter p : Finite X.
Print p.

Check @enumeration.

Program Instance prod_finite {X} {Y} (p1: Finite X) (p2: Finite Y) : Finite(X*Y) :=
{| enumeration := (map (@inl X Y) (@enumeration(X)(p1))) ++ 
                  (map (@inr X Y) (@enumeration(Y)(p2)));
   enumerate := _ |}.

Next Obligation.

Instance sum_finite : Finite'-> Finite' -> Finite'.
Proof.
  intros.
  destruct X0 as [X xs p]; destruct X1 as [Y ys p'].
  esplit.
  eapply p.
  destruct H as [xs p]; destruct H0 as [ys p'].
  econstructor; intros.
  cut (In x (app (map inl xs) (map inr ys))); eauto.
  apply in_or_app.
  destruct x; [left|right]; apply in_map; auto.
Qed.

Instance sum_finite {X} {Y} : Finite X -> Finite Y -> Finite(X+Y).
Proof.
  intros.
  destruct H as [xs p]; destruct H0 as [ys p'].
  econstructor; intros.
  cut (In x (app (map inl xs) (map inr ys))); eauto.
  apply in_or_app.
  destruct x; [left|right]; apply in_map; auto.
Qed.

Check sum_finite.

Instance prod_finite {X} {Y} : Finite X -> Finite Y -> Finite(X*Y).
Proof.
  intros.
  destruct H as [xs p]; destruct H0 as [ys p'].
  econstructor. intros. destruct x.
  cut (In (x,y) (list_prod xs ys)); eauto using in_prod.
Qed.

Inductive finTy {X : Set} (xs : list X) : Set :=
  | finTyE : forall x, In x xs -> finTy xs.
Hint Constructors finTy.

Inductive atom : Set := Atom.

Instance atom_finite : Finite atom.
Proof.
  assert(forall x : atom, In x [Atom]); econstructor; eauto.
  destruct x; trivial.
Qed.

Inductive null : Set :=.
Instance null_finite : Finite null.
Proof.
  assert(forall x : null, In x []).
  + intro x; inversion x.
  + econstructor; eapply H.
Qed.

Fixpoint nary (n : nat) : Finite _ :=
match n with
  | O -> null
  | _