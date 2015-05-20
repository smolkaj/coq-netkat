(** Instantiate NetKAT with actual fields and values.
    This template can be easily adapted to introduce new fields,
    different values, etc. *)

Require Import Optimize Automata List Bool.
Import ListNotations.



Module F <: FIELDSPEC.
  
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




Module V <: VALUESPEC(F).

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



Module O := Optimize.Optimize(F)(V).
Module A := Automata.Automata(F)(V).
Include A.


Definition pk : A.P.t := fun _ => V.ONE.
Definition trace1 := pk~([])~pk.
Definition trace2 := pk~([pk])~pk.
Definition pol1 := A.Drop.
Definition pol2 := A.Id.
Definition pol3 := F.Sw==V.ONE;; F.Pt==V.ONE;; F.Vlan==V.ONE.
Eval compute in A.nfa_lang (A.netkat_nfa pol2) trace1.


(* Print O. *)
(* Print A. *)
