(** Instantiate NetKAT with actual fields and values.
    This template can be easily adapted to introduce new fields,
    different values, etc. *)

Require Import Field.
Require Import Value.
Require Import List.
Import ListNotations.

Require Import CpdtTactics.



Module Fieldspec : FIELDSPEC.
  
  Inductive F' :=
    | Sw
    | Pt
    | Vlan.

  (* Coq unfortunately requires this ugly hack *)
  Definition F := F'.
  Hint Unfold F.

  (* automatically generates equality for indudtively defined type *)
  (* Scheme Equality for F'. *)

  Lemma eq_dec : forall f g : F, {f=g} + {~f=g}.
    decide equality.
  Qed.

  Definition all := [Sw; Pt; Vlan].

  Theorem finite : forall f:F, In f all.
  Proof.
    intros f.
    unfold all.
    case f; simpl; auto.
  Qed.

End Fieldspec.



Require Import Ensembles.
Require Import Finite_sets.

Module Fieldspec' : FIELDSPEC'.
  Inductive FU' :=
    | Sw
    | Pt
    | Vlan.

  (* Coq unfortunately requires this ugly hack *)
  Definition FU := FU'.
  Hint Unfold FU.

  Definition F := Full_set FU.
  Hint Unfold F.

  Lemma finite : Finite FU F.
  Proof.
  unfold FU. unfold F. admit.
  Qed.

  Require Import MSetWeakList.
  Print Make.

  Parameter finite : Finite FU F.
  Parameter eq_dec : forall x y : FU, { x=y } + { ~x=y }.
  (* Parameter beq : F -> F -> bool. *)
End Fieldspec'.




Module Valuespec : VALUESPEC(Fieldspec).
  Include Fieldspec.

  Definition V (_ : F) := { n : nat | n < 1024 }.
  Print sig.

End Valuespec.