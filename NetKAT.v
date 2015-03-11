Require Import Field.
Require Import Value.
Require Import List.
Import ListNotations.
Require Import Sets.
Require Import FunctionalExtensionality.
Require Import Bool.
Require Import Equalities.

Require Import CpdtTactics.

Fixpoint list_eqb {X : Type} (eqb : X -> X -> bool) (xs : list X) (ys : list X) : bool :=
  match xs, ys with
  | nil, nil => true
  | cons x xs, cons y ys => andb (eqb x y) (list_eqb eqb xs ys)
  | _,_ => false
  end.

Lemma list_eqb_eq : forall {X : Type}, forall (eqb : X -> X -> bool),
  forall p : (forall x y : X, eqb x y = true <-> x = y),
  forall l1 l2 : list X, list_eqb eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros X eqb p l1.
  induction l1.
  destruct l2.
  crush.
  crush.
  intros l2.
  destruct l2.
  crush.
  simpl.
  split; intros H.
  assert (eqb a x = true /\ list_eqb eqb l1 l2 = true) as H0.
    apply andb_prop; assumption.
  destruct H0.
  rewrite -> (p a x) in H0.
  rewrite -> (IHl1 l2) in H1.
  subst a l1.
  reflexivity.
  apply andb_true_intro.
  rewrite -> (p a x).
  rewrite -> (IHl1 l2).
  inversion H.
  split; reflexivity.
Qed.
 

Module Type PACKET (F : FIELDSPEC) (V : VALUESPEC(F)).
  Definition t : Type := forall f:F.t, (V.t f).
  Parameter mod : t -> forall f : F.t, V.t f -> t.
  (* Print UsualDecidableTypeFull *)
  Definition eq (p1 p2 : t) := (p1 = p2).
  Parameter eq_dec : forall x y : t, {x = y} + {x <> y}.
  Parameter eqb : t -> t -> bool.
  Parameter eqb_eq : forall x y : t, eqb x y = true <-> x = y.
End PACKET.

Module Packet (F : FIELDSPEC) (V : VALUESPEC(F)) <: PACKET(F)(V).
  
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

  Definition mod (pk : t) (f : F.t) (v : V.t f) : t :=
    fun f' =>
      match F.eq_dec f' f with
      | left e => eq_rec_r V.t v e
      | right ne => pk f'
      end.

End Packet.




Module History(F : FIELDSPEC) (V : VALUESPEC(F)) (P : PACKET(F)(V)).

  Module Skeleton.
  
  Definition t : Type := prod P.t (list P.t).

  Definition eq (h1 : t) (h2 : t) := h1 = h2.
  
  Definition eqb (h1 : t) (h2 : t) :=
    let (p1, rest1) := h1 in
    let (p2, rest2) := h2 in
    andb (P.eqb p1 p2) (list_eqb P.eqb rest1 rest2).

  Lemma eqb_eq : forall h1 h2 : t, eqb h1 h2 = true <-> h1 = h2.
  Proof.
    intros h1 h2.
    destruct h1 as [p h].
    destruct h2 as [p' h'].
    unfold eqb.
    split; intros H.
      assert (P.eqb p p' = true /\ list_eqb P.eqb h h' = true).
        apply andb_prop; assumption.
      destruct H0.
      rewrite -> P.eqb_eq in H0.
      rewrite -> (list_eqb_eq P.eqb P.eqb_eq h h') in H1.
      subst p h; reflexivity.
    inversion H.
      apply andb_true_intro.
      split.
      apply P.eqb_eq; reflexivity.
      apply (list_eqb_eq P.eqb P.eqb_eq). reflexivity.
  Qed.

  End Skeleton.

  Include Make_UDTF(Skeleton).

End History.



Module NetKAT (F : FIELDSPEC) (V : VALUESPEC(F)).

  Module P := Packet(F)(V).
  Module H := History(F)(V)(P).
  Module HSet := set(H).
  
  Inductive policy : Set :=
  | Drop : policy
  | Id : policy
  | Filter  : forall (f : F.t), V.t f -> policy
  | NFilter : forall (f : F.t), V.t f -> policy
  | Mod : forall (f : F.t), V.t f -> policy
  | Union   : policy -> policy -> policy
  | Seq     : policy -> policy -> policy
  | Star    : policy -> policy
  | Dup     : policy.

  Notation "f <- v" := (Mod f v) (at level 30, no associativity).
  Notation "f == v" := (Filter f v) (at level 30, no associativity).
  Notation "f != v" := (NFilter f v) (at level 30, no associativity).
  Notation "p + q" := (Union p q) (at level 50, left associativity).
  Notation "p ; q" := (Seq p q) (at level 40, left associativity).
  Notation "p *" := (Star p) (at level 31, left associativity).
  Notation "pk [ f := v ]" := (P.mod pk f v) (at level 10, no associativity).

  Check P.mod.

  Fixpoint fpower {X : Type} (n : nat) (f : X -> X):=
  match n with
  | O => fun x => x
  | S n => fun x => fpower n f (f x)
  end.

  Definition kleisli (f g : H.t -> HSet.t) : H.t -> HSet.t :=
    fun (h : H.t) =>
      fun (h' : H.t) => ex (fun h'' => f h h'' /\ g h'' h').

  Fixpoint interpret (p : policy) (h : H.t) : HSet.t :=
  match p, h with
  | Drop, _ => 
      HSet.empty
  | Id, h => 
      HSet.singleton h
  | Filter f v, (pk,h) =>
      if V.eqb f (pk f) v then HSet.singleton (pk,h)
      else HSet.empty
  | NFilter f v, (pk,h) =>
      if negb (V.eqb f (pk f) v) then HSet.singleton (pk,h)
      else HSet.empty
  | Mod f v, (pk,h) => 
      HSet.singleton (pk[f:=v], h)
  | p+q, h =>
      HSet.union (interpret p h) (interpret q h)
  | p;q, h =>
      kleisli (interpret p) (interpret q) h
  | p*, h =>
      let pn n := fpower n (kleisli (interpret p)) HSet.singleton in
      fun h' => ex (fun n => pn n h h')
  | Dup, (pk,h) => 
      HSet.singleton (pk, pk::h)
  end.

  Notation "'[|' p '|]'" := (interpret p) (at level 1).
  Notation "p === q" := (forall h : H.t, HSet.eq ([|p|] h) ([|q|] h)) (at level 80).
  
  (* Since we have eq_equiv : Equivalence HSet.eq, we can use reflexivity, symmetry,
     and rewrite with === *)

  Lemma kleisli_assoc: forall p q r h,
    HSet.eq (kleisli (kleisli p q) r h) (kleisli p (kleisli q r) h).
  Proof.
    intros p q r h0.
    unfold HSet.eq.
    intros h1.
    split; intros H; destruct H as [h']; destruct H as [H1 H2].
      destruct H1 as [h''].
      destruct H as [H0 H1].
      eapply ex_intro.
      split.
        apply H0.
      eapply ex_intro.
        split. apply H1. apply H2.
    destruct H2 as [h''].
      destruct H as [H2 H3].
      repeat (eapply ex_intro; split).
      apply H1. apply H2. apply H3.
   Qed.

  Theorem ka_plus_assoc : forall p q r : policy, (p+q)+r === p+(q+r).
  Proof.
   intros p q r h.
   apply HSet.union_assoc.
  Qed.

  Theorem ka_plus_comm : forall p q : policy, p + q === q + p.
  Proof.
   intros p q h.
   simpl.
   apply HSet.union_comm.
  Qed.

  Theorem ka_pluz_zero : forall p : policy, p + Drop === p.
  Proof.
    intros p h.
    simpl.
    apply HSet.union_empty_right.
  Qed.

  Theorem ka_seq_assoc : forall p q r : policy, (p;q);r === p;(q;r).
  Proof.
    intros p q r h.
    simpl.
    apply kleisli_assoc.
  Qed.

  Theorem ka_one_seq : forall p : policy, Id; p === p.
  Proof.
    intros p h h'.
    split; intro H.
      destruct H as [h''].
      destruct H as [H0 H1].
      simpl in H0.
      unfold HSet.singleton in H0.
      subst h''.
      assumption.
    simpl.
      eapply ex_intro.
      split. apply HSet.singleton_refl. apply H.
  Qed.

  Theorem ka_seq_one : forall p : policy, p; Id === p.
  Proof.
    intros p h h'.
    split; intro H.
      destruct H as [h''].
      destruct H as [H0 H1].
      simpl in H1.
      unfold HSet.singleton in H1.
      subst h''.
      assumption.
    simpl.
      eapply ex_intro.
      split. apply H. apply HSet.singleton_refl.
  Qed.

  Theorem ka_seq_dist_l : forall p q r : policy,
    p; (q + r) === p;q + (p; r).
  Proof.
    intros p q r h h''.
    split; intro H.
      destruct H as [h'].
      destruct H as [H0 H1].
      destruct H1 as [H1|H1]; [left | right]; exists h'; auto.
    destruct H as [H|H]; destruct H as [h']; destruct H as [H1 H2];
    exists h';split; try (apply H1).
    apply HSet.union_mono_left; assumption.
    apply HSet.union_mono_right; assumption.
  Qed.

  Theorem ka_seq_dist_r : forall p q r : policy,
    (p + q); r === p;r + q; r.
  Proof.
    intros p q r h h''.
    split; intro H.
      destruct H as [h'].
      destruct H as [H1 H0].
      destruct H1 as [H1|H1]; [left | right]; exists h'; auto.
    destruct H as [H|H]; destruct H as [h']; destruct H as [H1 H2];
    exists h'; split; try assumption.
    apply HSet.union_mono_left; assumption.
    apply HSet.union_mono_right; assumption.
  Qed.

  Theorem ka_zero_seq : forall p : policy, Drop; p === Drop.
  Proof.
    intros p h h'.
    crush.
    destruct H as [h'']. destruct H as [contr _].
    contradiction.
  Qed.

  Theorem ka_seq_zero : forall p : policy, p; Drop === Drop.
  Proof.
    intros p h h'.
    crush.
    destruct H as [h'']. destruct H as [_ contr].
    contradiction.
  Qed.


End NetKAT.


