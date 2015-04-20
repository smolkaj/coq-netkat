Require Import List Bool Arith.
Import ListNotations.
Require Import Relations Morphisms.
Require Import Omega FunctionalExtensionality.
Require Import Misc.

Generalizable Variables X Y.




Section Equality_Type.

Class eqType (X : Type) : Type := eq_dec : forall x y : X, {x=y} + {x<>y}.

Definition eqb `{eqType X} (x y : X) := if eq_dec x y then true else false.

Theorem eqb_eq `{eqType X} (x y : X) : eqb x y = true <-> x=y.
Proof. unfold eqb. destruct (eq_dec x y); intuition. inversion H0. Qed.

Theorem eqb_eq_false `{eqType X} (x y : X) : eqb x y = false <-> x<>y.
Proof. unfold eqb. destruct (eq_dec x y); intuition. Qed.

Hint Resolve eqb_eq eqb_eq_false.

Instance : eqType bool := bool_dec.
Instance : eqType nat := eq_nat_dec.
Program Instance : eqType True := fun x y => match x,y with I,I => left _ end. 
Program Instance : eqType False := fun x y => match x,y with end.

Program Instance sum_eqType `(eqType X) `(eqType Y) : eqType(X+Y) := fun a b =>
match a, b with
  | inl _, inr _ | inr _, inl _ => right _
  | inl z, inl z' | inr z, inr z' =>
      match eq_dec z z' with left _ => left _
                           | right _ => right _
      end
end.

Program Instance prod_eqType `(eqType X) `(eqType Y) : eqType(X*Y) := fun a b =>
match a,b with
  | pair x y, pair x' y' =>
  match eq_dec x x', eq_dec y y' with
    | left _, left _ => left _
    | left _, right _ | right _, left _ | right _, right _ => right _
  end
end.

Program Instance list_eqType `(eqType X) : eqType(list X) := fix f xs ys :=
match xs, ys with
  | nil, nil => left _
  | nil,cons _ _ | cons _ _,nil => right _
  | cons x xs, cons y ys =>
    match eq_dec x y with
      | left _ => match f xs ys with left _ => left _ | right _ => right _ end
      | right _ => right _
    end
end.

Eval compute in eqb 
  [(1,true);(2,false);(3,true)]
  [(1,true);(2,false);(3,true)].

End Equality_Type.






Section Finite.

Class Finite (X : Type) : Type := enum : {xs: list X|forall x, In x xs}.

Definition enum' X `{Finite X} := proj1_sig enum.
Hint Unfold enum'.

Program Instance : Finite bool := [true;false].
Next Obligation. destruct x; intuition. Qed.

Program Instance : Finite True := [I].
Next Obligation. destruct x; intuition. Qed.

Program Instance : Finite False := [].

Check @enum.

Program Instance sum_finite `(p1:Finite X) `(p2:Finite Y) : Finite(X+Y) :=
  (map (@inl X Y) (@enum X p1)) ++ (map (@inr X Y) (@enum Y p2)).
Next Obligation.
  destruct (@enum X p1) as [xs px]; destruct (@enum Y p2) as [ys py]; simpl.
  apply in_or_app.
  destruct x; [left|right]; apply in_map; auto.
Qed.

Program Instance prod_finite `(px: Finite X) `(py: Finite Y) : Finite(X*Y) :=
  list_prod enum enum.
Next Obligation.
  destruct (@enum X px) as [xs p1]; destruct (@enum Y py) as [ys p2]; simpl.
  auto using in_prod.
Qed.



Section Finite_Of_List.

Program Definition weaken {X} {xs: list X} x (y : {y|In y xs}) : {y|In y (x::xs)} := y.
Program Fixpoint siglist {X} (xs : list X) : list {x:X|In x xs} :=
match xs with
  | [] => []
  | x::xs => x :: (map (weaken x) (siglist xs))
end.

Program Instance fin_of_list {X} (xs : list X) : Finite {x|In x xs} := siglist xs.
Next Obligation.
  induction xs; destruct H.
  + subst a. simpl. auto.
  + right. 
    assert (weaken a (exist (fun x0 : X => In x0 xs) x i) =
            exist (fun x0 : X => In x0 (a :: xs)) x (or_intror i))
    by auto.
    rewrite <- H.
    apply in_map. auto.
Qed.

End Finite_Of_List.


End Finite.






Section Finite_Functions.

Definition eq_dec_f `{Finite X} `{eqType (list Y)} (f g : X->Y) :=
  eq_dec (map f (enum' X)) (map g (enum' X)).

Program Instance fun_eqType `(Finite X) `(p:eqType Y) : eqType (X->Y) := fun f g =>
  if @eq_dec_f X _ Y (list_eqType p) f g then left _ else right _.
Next Obligation.
  extensionality x.
  assert(In x (enum' X)) by (unfold enum'; destruct enum; auto).
  induction enum'; simpl in *; inversion H0; clear H0; intuition. 
  subst a; assumption.
Qed.
Next Obligation. intro eq; subst; apply H0; reflexivity. Qed.

Definition functs' `(Finite X) `(Finite Y) : list (X->Y) := (fix loop ys :=
match ys with
  | [] => []
  | y::ys => (fun _ => y) :: (loop ys)
end) (enum' Y).

Fixpoint functs `(px:Finite X) `{_:eqType X} `(py:Finite Y) : list (X->Y) := 
(fix loop xs :=
  match xs with
    | [] => functs' px py
    | x::xs => flat_map (fun f => map (fun y x' => if eq_dec x x' then y else f x') (enum' Y))
       (loop xs)
  end) (enum' X).

Instance fun_finite `(Finite X) `(Finite Y) : Finite(X->Y) := fun f g =>



End Finite_Functions.







Fixpoint power {X} (xs : list X) :=
match xs with
  | [] => [[]]
  | x::xs => 
   map (fun p => app (fst p) (snd p)) (list_prod [[x];[]] (power xs))
end.

Definition insertn {X} (n:nat) (x:X) (xs:list X) := app (firstn n xs) (x::skipn n xs).


Lemma in_insertn X (x:X) y n xs : 
  In x xs \/ x=y -> In x (insertn n y xs).
Proof.
  intro H.
  unfold insertn. apply in_or_app.
  destruct H as [H|H].
  + rewrite <- (firstn_skipn n) in H. apply in_app_or in H.
    destruct H; [left|right]; simpl; auto.
  + right. simpl. auto.
Qed.

Fixpoint power {X} (xs : list X) :=
match xs with
  | [] => [[]]
  | x::xs => flat_map f (power xs)

Lemma in_power

Program Instance list_finite `(p: Finite X) : Finite(list X) :=

End Finite.

Check Finite (sum (prod bool True) False).


Class FinTy : Type := {
  T :> Type;
  T_finite :> Finite T
}.

Definition test `(FinTy) := enum.

Check test.

Parameter X : FinTy.

Check T.
Check @enum X.