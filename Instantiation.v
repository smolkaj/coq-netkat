(** Instantiate NetKAT with actual fields and values.
    This template can be easily adapted to introduce new fields,
    different values, etc. *)

Require Import Optimize.
Require Import List Bool.
Import ListNotations.



Module F : FIELDSPEC.
  
  Inductive t' :=
    | Sw
    | Pt
    | Vlan.

  (* Coq unfortunately requires this ugly hack *)
  Definition t := t'.
  Hint Unfold t.

  (* automatically generates equality for indudtively defined type *)
  (* Scheme Equality for F'. *)

  Lemma eq_dec : forall f g : t, {f=g} + {~f=g}.
  Proof. decide equality. Qed.

  Definition all := [Sw; Pt; Vlan].

  Theorem finite : forall f:t, In f all.
  Proof. intros f. unfold all. case f; simpl; auto. Qed.

End F.




Module V : VALUESPEC(F).

  Inductive value :=
    | ZERO
    | ONE
    | TWO
    | THREE.

  Definition t (f : F.t) := value.
  Hint Unfold t.

  Definition all (f : F.t) := [ZERO; ONE; TWO; THREE].
  
  Lemma finite : forall f:F.t, forall v : (t f), In v (all f).
  Proof. intros f v. case v; unfold all; simpl; auto. Qed.

  Lemma eq_dec : forall f : F.t, forall v1 v2 : (t f), {v1=v2} + {~v1=v2}.
  Proof. decide equality. Qed.
  
  Definition eqb (f : F.t) (v1 v2 : t f) :=
    if eq_dec f v1 v2 then true else false.

  Lemma eqb_eq : forall f : F.t, forall x y : t f,
    eqb f x y = true <-> x = y.
  Proof.
    intros f x y.
    split; intros H.
      unfold eqb in H.
      destruct (eq_dec f x y). assumption. inversion H.
    replace y. unfold eqb.
    case (eq_dec f x x); auto.
  Qed.

  Lemma eqb_dec : forall f : F.t, forall x y : t f,
    {x=y} + {x<>y}.
  Proof.
    intros.
    case (eqb f x y) eqn: eq; [cut (x=y) | cut(x<>y)]; intuition.
    + apply eqb_eq. assumption.
    + apply eqb_eq in H. rewrite eq in H. inversion H.
  Qed.

End V.

Module N := Optimize.Optimize(F)(V).
(* Print N. *)