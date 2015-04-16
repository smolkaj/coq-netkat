Require Export Field.
Require Export Value.
Require Import List.
Require Import Equalities.
Require Import FunctionalExtensionality.

Module Type PACKET (F : FIELDSPEC) (V : VALUESPEC(F)).
  Definition t : Type := forall f:F.t, (V.t f).
  Parameter mod : t -> forall f : F.t, V.t f -> t.
  (* Print UsualDecidableTypeFull *)
  Definition eq (p1 p2 : t) := (p1 = p2).
  Parameter eq_dec : forall x y : t, {x = y} + {x <> y}.
  Parameter eqb : t -> t -> bool.
  Parameter eqb_eq : forall x y : t, eqb x y = true <-> x = y.
End PACKET.

Module Packet (F : FIELDSPEC) (V : VALUESPEC(F)) : PACKET(F)(V).
  
  Module Skeleton.

  Definition t : Type := forall f:F.t, (V.t f).

  Definition eq (p1:t) (p2:t) := p1=p2.

  Definition eqb p1 p2 :=
    forallb (fun f : F.t => V.eqb f (p1 f) (p2 f)) F.all.

  Lemma eqb_eq : forall p1 p2 : t, eqb p1 p2 = true <-> p1 = p2.
  Proof.
    intros p1 p2.
    unfold eqb.
    rewrite -> forallb_forall.
    constructor; intros H.
      extensionality f.
      rewrite <- V.eqb_eq.
      apply H.
    apply F.finite.
      intros f _.
      rewrite -> V.eqb_eq.
      rewrite H.
      reflexivity.
  Qed.

  End Skeleton.

  Include Make_UDTF(Skeleton).

  Program Definition mod (pk : t) (f : F.t) (v : V.t f) : t :=
    fun f' => if F.eq_dec f' f then v else pk f'.
 
  (* old definition from the days before I heard about "Program" **
  Definition mod (pk : t) (f : F.t) (v : V.t f) : t :=
    fun f' =>
      match F.eq_dec f' f with
      | left e => eq_rec_r V.t v e
      | right ne => pk f'
      end.
  *)

End Packet.
