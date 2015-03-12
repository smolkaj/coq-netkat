Require Import Misc.
Require Export Field.
Require Export Value.
Require Export Packet.
Require Export History.
Require Import List.
Import ListNotations.
Require Export Sets.
Require Import FunctionalExtensionality.
Require Import Bool.
Require Import Equalities.
Require Import CpdtTactics.


Module NetKAT (F : FIELDSPEC) (V : VALUESPEC(F)).

  (** * Packets, Histories, and History Sets *)
  Module P := Packet.Packet(F)(V).
  Module H := History.History(F)(V)(P).
  Module HSet := set(H).
  

  (** * NetKAT Syntax.
     For simplicity, we restrict Filters to simple tests
     and provide a negated filter NFilter, instead of defining predicates.
     We do not lose expressivity (since all negations can be pushed down).
  *)
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



  (** * NetKAT denotation Semantics *)

  (* auxilliary functions for (repeated) kleisli composition *) 
  Definition kleisli (f g : H.t -> HSet.t) : H.t -> HSet.t :=
    fun (h : H.t) =>
      fun (h' : H.t) => ex (fun h'' => f h h'' /\ g h'' h').

  Fixpoint power (n: nat) f :=
    match n with
      | O => (fun h => HSet.singleton h)
      | S n => kleisli f (power n f)
    end.

  (* denotational semantics *)
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
      fun h' => ex (fun n => power n (interpret p) h h')
  | Dup, (pk,h) => 
      HSet.singleton (pk, pk::h)
  end.

  Notation "'[|' p '|]'" := (interpret p) (at level 1).
  (* Denotational equivalence. This definition is useful since HSet.eq is
     an equivalence relation. Therefore Coq allows us to use tactics such
     as reflexivity, symmetry, and rewrite *)
  Notation "p === q" := 
    (forall h : H.t, HSet.eq ([|p|] h) ([|q|] h)) (at level 80).



  (** * NetKAT Axioms & useful corollaries *)

  (* some auxilliary lemmas about kleisli composition *)
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

  Lemma kleisli_right_id: forall p h, HSet.eq (p h) (kleisli p HSet.singleton h).
  Proof.
    intros p h h'.
    split; intros H.
      exists h'.
      auto.
    destruct H as [h'']. destruct H as  [H0 H1].
    unfold HSet.singleton in H1.
    subst h''.
    assumption.
  Qed.

  Lemma kleisli_left_id: forall p h, HSet.eq (p h) (kleisli HSet.singleton p h).
  Proof.
    intros p h h'.
    split; intros H.
      exists h.
      auto.
    destruct H as [h'']. destruct H as  [H0 H1].
    unfold HSet.singleton in H0.
    subst h''.
    assumption.
  Qed.

  Lemma power_slide: forall n f h, 
    HSet.eq (power (S n) f h) (kleisli (power n f) f h).
  Proof.
    intros n.
    induction n; intros f h.
    simpl. unfold HSet.singleton. unfold kleisli. split; intros H.
      destruct H as [h'']; destruct H as [H0 H1]. subst h''. exists h. auto.
      destruct H as [h'']; destruct H as [H0 H1]. subst h''. exists x. auto.
    assert (HSet.eq (kleisli f (power (S n) f) h) (kleisli (kleisli f (power n f)) f h)).
      rewrite -> kleisli_assoc.
      intros h'.
      split; intros H; destruct H as [h'']; destruct H as [H0 H1];
      exists h''; split; try(apply IHn); assumption.
    auto.
  Qed.

  Corollary power_slide': forall n f h, 
    HSet.eq (kleisli f (power n f) h) (kleisli (power n f) f h).
  Proof.
    apply power_slide.
  Qed.

  (* NetKAT axioms and useful corollaries *)
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

  Theorem ka_plus_zero : forall p : policy, p + Drop === p.
  Proof.
    intros p h.
    simpl.
    apply HSet.union_empty_right.
  Qed.

  Corollary ka_zero_plus: forall p : policy, Drop + p === p.
  Proof. 
    intros p h.
    rewrite -> ka_plus_comm; rewrite -> ka_plus_zero; reflexivity.
  Qed.

  Theorem ka_plus_idem : forall p : policy, p + p === p.
  Proof.
    intros p h.
    simpl.
    apply HSet.union_idem.
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

  Theorem ka_unroll_l : forall p : policy, Id + p;p* === p*.
  Proof.
    intros p h h'.
    split; intros H.
      destruct H as [H|H].
        simpl in H.
        unfold HSet.singleton in H.
        subst h'.
        exists 0.
        simpl.
        unfold HSet.singleton; reflexivity.
      destruct H as [h'']. destruct H as [H0 H1].
        destruct H1 as [n].
        exists (S n).
        simpl.
        exists h''.
        auto.
    destruct H as [n].
    destruct n; simpl in H.
      unfold HSet.singleton in H.
      subst h'.
      left.
      simpl; auto.
    right.
    destruct H as [h'']. destruct H as [H0 H1].
    exists h''.
    split; try assumption.
    exists n.
    assumption.
  Qed.

  Theorem ka_unroll_r : forall p : policy, Id + p*;p === p*.
  Proof.
    intros p h h'.
    split; intros H.
      destruct H as [H|H].
        simpl in H.
        unfold HSet.singleton in H.
        subst h'.
        exists 0.
        simpl.
        unfold HSet.singleton; reflexivity.
      destruct H as [h'']. destruct H as [H0 H1].
        destruct H0 as [n].
        exists (S n).
        simpl.
        apply power_slide.
        exists h''.
        auto.
    destruct H as [n].
    destruct n; simpl in H.
      unfold HSet.singleton in H.
      subst h'.
      left.
      simpl; auto.
    right.
    apply (power_slide' n [|p|] h) in H.
    destruct H as [h'']. destruct H as [H0 H1].
    exists h''.
    split; [exists n| ]; assumption.
  Qed.
    

  (** * Tactics for automated axiomatic reasoning *)
  
  Hint Rewrite ka_plus_assoc ka_plus_zero ka_zero_plus ka_plus_idem
    ka_seq_assoc ka_one_seq ka_seq_one ka_zero_seq ka_zero_plus ka_seq_zero.

  (* Tactic that tries to rewrite using all "safe" rules and
     then discharges all trivial goals. *)
  Ltac netkat :=
    try(simpl; reflexivity);
    try(repeat(rewrite -> ka_plus_zero));
    try(repeat(rewrite -> ka_zero_plus));
    try(repeat(rewrite -> ka_plus_idem));
    try(repeat(rewrite -> ka_seq_zero));
    try(repeat(rewrite -> ka_zero_seq));
    try(repeat(rewrite -> ka_seq_one));
    try(repeat(rewrite -> ka_one_seq));
    try(simpl; reflexivity).

  (* Tactic that does case splits on two policies and then tries
     to solve goals using axiomatic rewriting *)
  Ltac netkat_cases p q :=
    case p; case q;
    netkat;
    try (intros f);
    netkat;
    try (intros v);
    netkat.
    


End NetKAT.


