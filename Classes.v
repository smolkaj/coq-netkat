Require Import List Bool Arith Setoid Morphisms.
Require Import Relations Morphisms.
Require Import Omega FunctionalExtensionality.
Require Import Misc.
Import ListNotations.

(* decidable sets as in ssreflect *)
Definition pred T := T -> bool.
(* Identity Coercion fun_of_pred : pred >-> Funclass. *)

Notation "[$ x | B ]" := (fun x => B) (at level 0, x ident) : bool_scope.
Notation "[$ x : T | B ]" := (fun x : T => B) (at level 0, x ident) : bool_scope.
Notation "x \in L" := (L x = true) (at level 0) : bool_scope.

Notation pred0 := [$ _ | false ].
Notation pred1 := [$ _ | true ].
Notation predI := (fun (p1 p2 : pred _) x => p1 x && p2 x).
Notation predU := (fun (p1 p2 : pred _) x => p1 x || p2 x).
Notation predC := (fun (p : pred _) x => ~~ p x).




Generalizable Variables X Y.




Section Equality_Type.

Class EqType (X : Type) : Type := eq_dec : forall x y : X, {x=y} + {x<>y}.

Definition eqb `{EqType X} (x y : X) := if eq_dec x y then true else false.

Theorem eqb_eq `{EqType X} (x y : X) : eqb x y = true <-> x=y.
Proof. unfold eqb. destruct (eq_dec x y); intuition. inversion H0. Qed.

Theorem eqb_eq_false `{EqType X} (x y : X) : eqb x y = false <-> x<>y.
Proof. unfold eqb. destruct (eq_dec x y); intuition. Qed.

Hint Resolve eqb_eq eqb_eq_false.

Global Instance : EqType bool := bool_dec.
Global Instance : EqType nat := eq_nat_dec.
Global Program Instance : EqType True := fun x y => match x,y with I,I => left _ end. 
Global Program Instance : EqType False := fun x y => match x,y with end.

Global Program Instance sum_EqType `(EqType X) `(EqType Y) : EqType(X+Y) :=
fun a b =>
  match a, b with
  | inl _, inr _ | inr _, inl _ => right _
  | inl z, inl z' | inr z, inr z' => if eq_dec z z' then left _ else right _ 
  end.

Global Program Instance prod_EqType `(EqType X) `(EqType Y) : EqType(X*Y) :=
fun a b =>
  match a,b with
  | pair x y, pair x' y' =>
    if eq_dec x x' then (if eq_dec y y' then left _ else right _)
    else right _
  end.

Global Program Instance list_EqType `{EqType X} : EqType(list X) := fix f xs ys :=
match xs, ys with
  | nil, nil => left _
  | nil,cons _ _ | cons _ _,nil => right _
  | cons x xs, cons y ys =>
    if eq_dec x y then (if f xs ys then left _ else right _)
    else right _
end.


Eval compute in eqb 
  [(1,true);(2,false);(3,true)]
  [(1,true);(2,false);(3,true)].

End Equality_Type.

Definition test := (@eqb (list (prod bool nat)) _).
Recursive Extraction test.





(** Section Finite **)

Class Finite (X : Type) : Type := enum : {xs: list X|forall x, In x xs}.

Definition enum' X `{Finite X} := proj1_sig enum.
Hint Unfold enum'.

Theorem in_enum `{Finite X} (x:X) : In x (proj1_sig enum).
Proof. destruct enum; simpl; auto. Qed.
Hint Resolve in_enum. 

Corollary in_enum' `{Finite X} (x:X) : In x (enum' X).
Proof. unfold enum'; auto. Qed.
Hint Resolve in_enum'.

Global Program Instance : Finite bool := [true;false].
Next Obligation. destruct x; intuition. Defined.

Global Program Instance : Finite True := [I].
Next Obligation. destruct x; intuition. Defined.

Global Program Instance : Finite False := [].

Global Program Instance sum_finite `(p1:Finite X) `(p2:Finite Y) : Finite(X+Y) :=
  (map (@inl X Y) enum) ++ (map (@inr X Y) enum).
Next Obligation. destruct x; auto using in_map, in_or_app. Defined.

Global Program Instance prod_finite `(px: Finite X) `(py: Finite Y) : Finite(X*Y) :=
  list_prod enum enum.
Next Obligation. auto using in_prod. Defined.



(** Section Finite of list. **)

Program Definition weaken {X} {xs: list X} x (y : {y|In y xs}) : {y|In y (x::xs)} := y.
Program Fixpoint siglist {X} (xs : list X) : list {x:X|In x xs} :=
match xs with
  | [] => []
  | x::xs => x :: (map (weaken x) (siglist xs))
end.

Global Program Instance fin_of_list {X} (xs : list X) : Finite {x|In x xs} := 
  siglist xs.
Next Obligation.
  induction xs; destruct H.
  + subst a. simpl. auto.
  + right. 
    assert (weaken a (exist (fun x0 : X => In x0 xs) x i) =
            exist (fun x0 : X => In x0 (a :: xs)) x (or_intror i))
    by auto.
    rewrite <- H.
    apply in_map. auto.
Defined.

(** End Finite_Of_List. **)


(* decidable exists on finite types *)

Notation "[$ 'exists' x | B ]" := (existsb (fun x => B) (enum' _))
  (at level 0, x ident) : bool_scope.
Notation "[$ 'exists' x : T | B ]" := (existsb (fun x : T => B) (enum' _))
  (at level 0, x ident) : bool_scope.

Theorem exists_iff `(Finite X) B : (exists x, B x = true) <-> [$ exists x | B x] = true.
Proof.
  rewrite existsb_exists.
  split; intro H0; destruct H0 as [x H0]; exists x; intuition eauto.
Qed.
Hint Resolve exists_iff.

(** End Finite. **)








Section Finite_Functions.

Definition eq_dec_f `{Finite X} `{EqType Y} (f g : X->Y) :=
  eq_dec (map f (enum' X)) (map g (enum' X)).

Global Program Instance fun_EqType `(Finite X) `(EqType Y) : EqType (X->Y) := 
  fun f g => if eq_dec_f f g then left _ else right _.
Next Obligation.
  extensionality x.
  assert(In x (enum' X)) by (unfold enum'; destruct enum; auto).
  induction enum'; simpl in *; inversion H1; clear H1; intuition.
  subst a; assumption.
Defined.
Next Obligation. intro eq; apply H1; congruence. Defined.

(*

Definition functs `(Finite X) `(Finite Y) `{EqType X} : list(X->Y) :=
  fold_left 
    (fun fs x => flat_map (fun f => 
      map (fun y x' => if eq_dec x x' then y else f x') (enum' Y)) fs)
    (enum' X)
    (map (fun y => fun _ => y) (enum' Y)).

Definition test `(Finite X) `(Finite Y) (y:Y) :=
  (fun (x:X) => match x with end).

Program Instance fun_finite `(px:Finite X) `(py:Finite Y) `{_:EqType X} `{_:EqType Y} 
: Finite(X->Y) :=
  functs px py.
Next Obligation.
  rename x into f.
  unfold functs.
  induction (enum' X); simpl in *.
  functional induction
  assert(xs := enum' X).
  induction (xs).
*)


End Finite_Functions.
