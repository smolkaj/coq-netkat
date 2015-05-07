Require Export Field.
Require Export Value.
Require Export Packet.
Require Import Misc.
Require Import List.
Require Import Equalities.
Require Import FunctionalExtensionality.

Module History(F : FIELDSPEC) (V : VALUESPEC(F)) (P : PACKET(F)(V)).

  Module Skeleton.
  
  Definition t : Type := prod P.t (list P.t).

  Definition eq (h1 : t) (h2 : t) := h1 = h2.

  Definition peqb : P.t -> P.t -> bool := eqb.
  
  Definition eqb (h1 : t) (h2 : t) :=
    let (p1, rest1) := h1 in
    let (p2, rest2) := h2 in
    andb (eqb p1 p2) (list_eqb eqb rest1 rest2).

  Lemma eqb_eq : forall h1 h2 : t, eqb h1 h2 = true <-> h1 = h2.
  Proof.
    intros h1 h2.
    destruct h1 as [p h].
    destruct h2 as [p' h'].
    unfold eqb.
    split; intros H.
      assert (peqb p p' = true /\ list_eqb peqb h h' = true).
        apply andb_prop; assumption.
      destruct H0.
      unfold peqb in *.
      rewrite -> eqb_eq in H0.
      rewrite -> (list_eqb_eq peqb eqb_eq h h') in H1.
      subst p h; reflexivity.
    inversion H.
      apply andb_true_intro.
      split.
      apply eqb_eq; reflexivity.
      apply (list_eqb_eq peqb eqb_eq). reflexivity.
  Qed.

  End Skeleton.

  Include Make_UDTF(Skeleton).

End History.