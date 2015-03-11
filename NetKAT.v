Require Import Field.
Require Import Value.
Require Import List.
Import ListNotations.
Require Import Sets.
Require Import FunctionalExtensionality.
Require Import Bool.
Require Import Equalities.
Set Implicit Arguments.

Require Import CpdtTactics.

Fixpoint list_eqb {X : Type} (eqb : X -> X -> bool) (xs : list X) (ys : list X) : bool :=
  match xs, ys with
  | nil, nil => true
  | cons x xs, cons y ys => andb (eqb x y) (list_eqb eqb xs ys)
  | _,_ => false
  end.

Lemma list_eqb_eq : forall X : Type, forall (eqb : X -> X -> bool),
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
  Include UsualDecidableTypeFull.
  Parameter mod : t -> forall f : F.t, V.t f -> t.
  Notation "pk [ f := v ]" := (mod pk f v) (at level 8, left associativity).
End PACKET.


Module Packet (F : FIELDSPEC) (V : VALUESPEC(F)) : PACKET(F)(V).
  
  Module Skeleton.

  Definition t : Set := forall f:F.t, (V.t f).

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

  Notation "pk [ f := v ]" := (mod pk f v) (at level 8, left associativity).

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

  Notation "f <- v" := (Mod f v) (at level 20, no associativity).
  Notation "f == v" := (Filter f v) (at level 20, no associativity).
  Notation "f != v" := (NFilter f v) (at level 20, no associativity).
  Notation "p + q" := (Union p q). (* at level 50 *)
  Notation "p ; q" := (Seq p q) (at level 40, left associativity).
  Notation "p *" := (Star p) (at level 31, left associativity).

  Fixpoint fpower {X : Type} (n : nat) (f : X -> X):=
  match n with
  | O => fun x => x
  | S n => fun x => fpower n f (f x)
  end.

  Definition lift_arg {X : Type} (f : X -> Ensemble X) (A : Ensemble X) : Ensemble X :=
    fun x => ex (fun y => and (A y) (f y x)).

  Fixpoint interpret (p : policy) (h : history) : Ensemble history :=
  match p, h with
  | Drop, _ => 
      Empty_set history
  | Id, h => 
      Singleton history h
  | f==v, (pk,h) =>
      if V.eq_dec f (pk f) v then Singleton history (pk,h)
      else Empty_set history
  | f!=v, (pk,h) =>
      if V.eq_dec f (pk f) v then Empty_set history
      else Singleton history (pk,h)
  | f<-v, (pk,h) => 
      Singleton history (pk[f:=v], h)
  | p+q, h =>
      Ensembles.Union history (interpret p h) (interpret q h)
  | p;q, h =>
      lift_arg (interpret q) (interpret p h)
  | p*, h =>
      let pn n := fpower n (lift_arg (interpret p)) in
      fun h' => ex (fun n => pn n (Singleton history h) h')
  | Dup, (pk,h) => 
      Singleton history (pk, pk::h)
  end.

  Notation "'|' p '|'" := (interpret p) (at level 10).
  Notation "p === q" := (forall h, |p| h  = |q| h) (at level 80).

  Require Import Classical_sets.
  Require Import CpdtTactics.

  Theorem ka_plus_assoc : forall p q r : policy, (p+q)+r === p+(q+r).
  Proof.
   intros p q r h.
   simpl.
   apply Extensionality_Ensembles.
   auto.
   crush.
   rewrite -> (union_assoc history).
   reflexivity.
  Qed.

  Theorem ka_plus_com : forall p q : policy, p + q === q + p.
  Proof.
   intros p q h h'.
   simpl.
   rewrite -> (union_comm history).
   reflexivity.
  Qed.

  Theorem ka_pluz_zero : forall p : policy, p + Drop === p.
  Proof.
    intros p h h'.
    simpl.


End NetKAT.

Module N := NetKAT(Headers).
Import N.
Import Headers.

Definition pk1 (f : F) := 1.

Definition pk2 := pk1 [Port := 2][Vlan := 5].
Eval cbv in pk2 Port.
