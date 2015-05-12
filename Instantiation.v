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

  Program Definition finite : (Finite t) := [Sw;Pt;Vlan].
  Next Obligation. destruct x; auto. Defined.

  (* automatically generates equality for indudtively defined type *)
  (* Scheme Equality for F'. *)
  Lemma eq_dec : forall f g : t, {f=g} + {~f=g}.
  Proof. decide equality. Qed.

  Global Instance : Finite t := finite.
  Global Instance : EqType t := eq_dec.

End F.




Module V : VALUESPEC(F).

  Inductive value :=
    | ZERO
    | ONE
    | TWO
    | THREE.

  Definition t (_ : F.t) := value.
  Hint Unfold t.

  Program Definition finite f : Finite (t f) := [ZERO; ONE; TWO; THREE].
  Next Obligation. destruct x; auto. Qed.

  Lemma eq_dec : forall f : F.t, forall v1 v2 : (t f), {v1=v2} + {~v1=v2}.
  Proof. decide equality. Qed.

  Global Instance is_finite : forall f, Finite (t f) := finite.
  Global Instance is_eqtype : forall f, EqType (t f) := eq_dec.

End V.



Module N := Optimize.Optimize(F)(V).
(* Print N. *)