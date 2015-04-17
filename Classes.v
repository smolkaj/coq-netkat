Require Import List Bool Arith.
Import ListNotations.
Require Import Relations Morphisms.
Require Import Omega.

Generalizable Variables X Y.

Class eqType (X : Type) : Type := eq_dec : forall x y : X, {x=y} + {x<>y}.

Instance : eqType bool := bool_dec.
Instance : eqType nat := eq_nat_dec.
Instance : eqType True.
Proof. intros x y. destruct x; destruct y; auto. Qed.
Instance : eqType False.
Proof. intros x; destruct x. Qed.

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

Eval compute in if eq_dec ((4,3)) ((2,3)) then true else false.

Instance prod_eqType `(eqType X) `(eqType Y) : eqType(X*Y).


Section Finite.

Class Finite (X : Type) `{eqType X} : Type := enum : {xs: list X|forall x, In x xs}.
Check Finite.

Check @enum.
Check Finite.


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





Section Finite_Functions.

Lemma 


Program Instance fun_finite `(p1:Finite X) `(p2:Finite Y) : Finite(X->Y) :=
 fold_right list_prod (map (list_prod (@enum Y p2)) (@enum X p1)) [].

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