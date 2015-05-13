Require Import List Bool Arith Setoid Relations Morphisms Omega FunctionalExtensionality
  Sumbool Misc.
Import ListNotations.



(** Section Equality Type. ******************************************)

Generalizable Variables X Y.

Class EqType (X : Type) : Type := eq_dec : forall x y : X, {x=y} + {x<>y}.

Definition eqb `{EqType X} (x y : X) := if eq_dec x y then true else false.
Definition neqb `{EqType X} (x y : X) := if eq_dec x y then false else true.


Definition swap {P1 P2} (x:{P1}+{P2}) := match x with left a => right a | right b => left b end.
Global Transparent swap.

Notation "x =d= y :> T" := (@eq_dec T _ x y)
  (at level 70, y at next level, no associativity) : bool_scope.

Notation "x <d> y :> T" := (swap (@eq_dec T _ x y))
  (at level 70, y at next level, no associativity) : bool_scope.

Notation "x =b= y :> T" := (@eqb T _ x y)
  (at level 70, y at next level, no associativity) : bool_scope.

Notation "x <b> y :> T" := (@neqb T _ x y)
  (at level 70, y at next level, no associativity) : bool_scope.

Notation "x =d= y" := (eq_dec x y)
  (at level 70, no associativity) : bool_scope.

Notation "x <d> y" := (swap (eq_dec  x y))
  (at level 70, no associativity) : bool_scope.

Notation "x =b= y" := (eqb x y)
  (at level 70, no associativity) : bool_scope.

Notation "x <b> y" := (neqb x y) 
  (at level 70, no associativity) : bool_scope.



Theorem eqb_eq `{EqType X} (x y : X) : eqb x y = true <-> x=y.
Proof. unfold eqb. destruct (eq_dec x y); intuition. inversion H0. Qed.

Theorem eqb_eq' `{EqType X} (x y : X) : eqb x y = true -> x=y.
Proof. rewrite eqb_eq. auto. Qed.

Theorem eqb_eq_false `{EqType X} (x y : X) : eqb x y = false <-> x<>y.
Proof. unfold eqb. destruct (eq_dec x y); intuition. Qed.

Theorem eqb_eq_false' `{EqType X} (x y : X) : x<>y <-> eqb x y = false.
Proof. symmetry. apply eqb_eq_false. Qed.

Theorem eqb_refl `{EqType X} (x : X) : eqb x x = true.
Proof. apply eqb_eq. reflexivity. Qed.

Hint Resolve eqb_eq' eqb_eq_false' eqb_refl.



Global Instance : EqType bool := bool_dec.
Global Instance : EqType nat := eq_nat_dec.
Global Program Instance : EqType True := fun x y => match x,y with I,I => left _ end. 
Global Program Instance : EqType False := fun x y => match x,y with end.
Global Program Instance : EqType unit := fun x y =>  match x,y with tt,tt => left _ end.

Global Program Instance option_EqType `{EqType X} : EqType (option X) := fun x y =>
match x,y with 
  | None, None => left _
  | Some x, Some y => if eq_dec x y then left _ else right _
  | None, Some _ | Some _, None => right _
end.

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

(* DONT MAKE THIS AN INSTANCE!! It can lead to nontermination *)
Program Definition injectvie_EqType {X} `(EqType Y) (f:X->Y) (p : injective f) : EqType X :=
  fun x1 x2 => if f x1 =d= f x2 then left _ else right _.
Next Obligation. intro H1. apply H0. apply f_equal. assumption. Defined.




(* Demo: Built-in equality vs boolean equality *)

Eval compute in 
  [(1,true);(2,false);(3,true)] = 
  [(4,true);(2,false);(3,true)].

Eval compute in  
  [(1,true);(2,false);(3,true)] =b= 
  [(4,true);(2,false);(3,true)].


(* Demo: Code extraction *) 
Definition test := (@eqb (list (prod bool nat)) _).
Recursive Extraction test.

(** End Equality_Type. #################################################*)









(** Section Finite *******************************************************)

Class Finite (X : Type) : Type := enum : {xs: list X | forall x, In x xs}.


(* Given a type X, this function returns a list of all elements of X,
   provided COQ can infer that X is finite.
*)
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

Global Program Instance : Finite unit := [tt].
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

Global Program Instance option_finite `{Finite X} : Finite (option X) := 
  None :: map (@Some X) enum.
Next Obligation. destruct x; intuition (auto using in_map). Qed.

Global Program Instance surjective_Finite Y `(Finite X) (f:X->Y) (p : surjective f) : Finite Y :=
  map f (enum' X).
Next Obligation. 
  unfold surjective in p. destruct (p x) as [x' H0]; subst x.
  apply in_map. auto.
Defined.


(* This will require the axiom of choice *)
(* Global Program Instance injective_Finite {X} `(Finite Y) (f:X->Y) (p : injective f) : Finite X. *)






(** Section Finite of list. ***********************************************************)
(* here we define the necessary infrastructure to create a finite type from a list *)

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

(** End Finite_Of_List. ########################################################**)






(* decidable exists on finite types **********************************************)

Notation "[$ 'exists' x | B ]" := (existsb (fun x => B) (enum' _))
  (at level 0, x ident) : bool_scope.
Notation "[$ 'exists' x : T | B ]" := (existsb (fun x : T => B) (enum' _))
  (at level 0, x ident) : bool_scope.

Theorem in_nth {X} (x : X) y xs : In x xs -> exists n, n < length xs /\ nth n xs y = x.
Proof. 
  induction xs; intros; destruct H.
  + subst a. exists 0; simpl. intuition.
  + destruct (IHxs H) as [n H']. exists (S n); simpl. intuition.
Qed.

Theorem existsb_false X B (xs : list X) :
  existsb B xs = false <-> (forall x : X, In x xs -> B x = false).
Proof.
  split.
  + intros H0 x H1.
    apply in_nth with (y:=x) in H1. destruct H1 as [n [H1 H2]].
    rewrite <- H2.
    eauto using existsb_nth.
  + intros. induction xs; simpl; auto.
    apply orb_false_iff. split.
    - apply H. simpl; auto.
    - apply IHxs. intros. apply H. simpl; auto.
Qed.

Theorem exists_false X `(Finite X) B :
  [$ exists x : X | B x ] = false <-> (forall x:X, B x = false).
Proof.
  split; intros.
  + eapply existsb_false in H0; eauto.
  + apply existsb_false; eauto.
Qed.

Theorem exists_iff X `(Finite X) B : [$ exists x | B x ] = true <-> (exists x, B x = true).
Proof.
  rewrite existsb_exists.
  split; intro H0; destruct H0 as [x H0]; exists x; intuition eauto.
Qed.

Theorem exists_existb_intro `(Finite X) B : (exists x, B x = true) -> [$ exists x | B x ] = true.
Proof. rewrite exists_iff. intro H'; exact H'. Qed.
Hint Resolve exists_existb_intro.




(* Finite Functions ***************************************************************)

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


(* For now, we state these well known facts as Axioms. *)
Axiom fun_fin : forall X Y, Finite X -> Finite Y -> Finite (X -> Y).
Global Instance fun_fin_inst : forall X Y, Finite X -> Finite Y -> Finite (X->Y) := fun_fin.


Axiom eq_dec_dep_f : forall X Y,
  Finite X -> (forall x:X, EqType(Y x)) -> EqType(forall x : X, Y x).
Global Instance dep_fun_EqType `(Finite X) `(forall x:X, EqType(Y x)) : 
  EqType (forall x:X, Y x) := eq_dec_dep_f _ _ _ _.


Axiom dep_fun_fin : forall X Y,
  Finite X -> (forall x:X, Finite (Y x)) -> Finite (forall x:X, Y x).
Global Instance dep_fun_fin_inst `(Finite X) `(forall x:X, Finite(Y x)) :
  Finite (forall x:X, Y x) := dep_fun_fin _ _ _ _.


(** IDEA!!! 
first prove that there is a bijection between associative lists and functions,
then prove that there are only finitely many associative lists.

f : X -> Y  ===  (enum' X, map f (enum' X)) === map (fun x => (x, f x) (enum' X)).
**)


End Finite_Functions.


(** End Finite. ######################################################################**)
