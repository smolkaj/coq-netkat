Require Import List Bool Relations Morphisms Equalities.
Import ListNotations.
Require Export Classes Field Value Packet History Sets.

Module NetKAT (F : FIELDSPEC) (V : VALUESPEC(F)).
  
  (** * Packets, Histories, and History Sets *)
  Module P := Packet.Packet(F)(V).
  Module H := History.History(F)(V)(P).
  

  (** * NetKAT Syntax.
     For simplicity, we restrict Filters to simple tests
     and provide a negated filter NFilter, instead of defining predicates.
     We do not lose expressivity (since all negations can be pushed down).
  *)
  Inductive policy : Set :=
    | Drop : policy
    | Id : policy
    | Filter  : forall f, V.t f -> policy
    | NFilter : forall f, V.t f -> policy
    | Mod : forall (f : F.t), V.t f -> policy
    | Union   : policy -> policy -> policy
    | Seq     : policy -> policy -> policy
    | Star    : policy -> policy
    | Dup     : policy.

  Implicit Type p q r : policy.

  Notation "f <- v" := (Mod f v) (at level 30, no associativity, format "f <- v") : netkat_scope.
  Notation "f == v" := (Filter f v) (at level 30, no associativity, format "f == v") : netkat_scope.
  Notation "f != v" := (NFilter f v) (at level 30, no associativity, format "f != v") : netkat_scope.
  Notation "p + q" := (Union p q) (at level 50, left associativity) : netkat_scope.
  Notation "p ;; q" := (Seq p q) (at level 40, left associativity) : netkat_scope.
  Notation "p *" := (Star p) (at level 31, left associativity, format "p *") : netkat_scope.
  Notation "pk [ f := v ]" := (P.mod pk f v) (at level 10, no associativity, format "pk [ f := v ]") : netkat_scope.
  Global Open Scope netkat_scope.
  Delimit Scope netkat_scrope with netkat.


  (** * NetKAT denotational Semantics *)

  (* auxilliary functions for (repeated) kleisli composition *) 
  Definition kleisli (f g : H.t -> set H.t) : H.t -> set H.t :=
    fun h h' => exists h'', f h h'' /\ g h'' h'.

  Fixpoint power n f :=
    match n with
      | O => @singleton H.t
      | S n => kleisli f (power n f)
    end.

  (* denotational semantics *)
  Fixpoint denot (p : policy) (h : H.t) : set H.t :=
  match p, h with
  | Drop, _ => 
      @empty H.t
  | Id, h => 
      singleton h
  | Filter f v, (pk,h) =>
      if v =d= pk f then singleton (pk,h)
      else @empty H.t
  | NFilter f v, (pk,h) =>
      if v <d> pk f then singleton (pk,h)
      else @empty H.t
  | Mod f v, (pk,h) => 
      singleton (pk[f:=v], h)
  | p+q, h =>
      union (denot p h) (denot q h)
  | p;;q, h =>
      kleisli (denot p) (denot q) h
  | p*, h =>
      fun h' => ex (fun n => power n (denot p) h h')
  | Dup, (pk,h) => 
      singleton (pk, pk::h)
  end.

  Notation "'[|' p '|]'" := (denot p) (at level 1) : netkat_scope.



  (* Denotational equivalence. *)
  Definition equiv : relation policy := 
    fun p q => forall h, eq ([|p|] h) ([|q|] h).

  Lemma equiv_refl : Reflexive equiv.
    Proof. intros p h. reflexivity. Qed.

  Lemma equiv_sym : Symmetric equiv.
  Proof. intros p q H h. symmetry. apply (H h). Qed.

  Lemma equiv_trans : Transitive equiv.
  Proof. intros p q r H1 H2 h. rewrite -> (H1 h). apply (H2 h). Qed.

  (* This allows us to use reflexivity, symmetry, and rewrite for denotational equivalence *)
  Instance equiv_equiv : Equivalence equiv.
  Proof. split; [apply equiv_refl | apply equiv_sym | apply equiv_trans]. Qed. 

  Notation "p === q" := (equiv p q) (at level 80) : netkat_scope.
  Notation "p <== q" := (p + q === q) (at level 80) : netkat_scope.


  (* The NetKAT operators are "proper" w.r.t. equivalence ===,
     i.e. p===q -> p + r === p + q, etc. We need to make Coq aware of this
     explicitly so we can use the rewrite tactic.
     See www.labri.fr/perso/casteran/CoqArt/TypeClassesTut/typeclassestut.pdf
     Section 3.5 for details. *)

  Lemma plus_equiv_right: forall p q r, q === r -> p + q === p + r.
  Proof.
    intros p q r H h h'.
    split; intros H0; (destruct H0; [left | right;apply H]); assumption.
  Qed.

  Lemma plus_equiv_left: forall p q r, p === q -> p + r === q + r.
  Proof.
    intros p q r H h h'.
    split; intros H0; (destruct H0; [left;apply H | right]); assumption.
  Qed.
   
  Instance plus_equiv_proper :
    Proper (equiv ==> equiv ==> equiv) Union.
  Proof.
    intros p p' Hp q q' Hq.
    assert (p'+q === p'+q') by auto using plus_equiv_right, Hq.
    assert (p+q === p'+q) by auto using plus_equiv_left, Hp.
    rewrite H0; rewrite H; reflexivity.
  Qed.


  Lemma seq_equiv_right: forall p q r, q === r -> p ;; q === p ;; r.
  Proof.
    intros p q r H h h'.
    split; intros H0; destruct H0 as [h'' [H0 H1]];
    apply H in H1; exists h''; auto.
  Qed.

  Lemma seq_equiv_left: forall p q r, p === q -> p ;; r === q ;; r.
  Proof.
    intros p q r H h h'.
    split; intros H0; destruct H0 as [h'' [H0 H1]];
    apply H in H0; exists h''; auto.
  Qed.

  Instance seq_equiv_proper :
    Proper (equiv ==> equiv ==> equiv) Seq.
  Proof. 
    intros p p' Hp q q' Hq.
    rewrite (seq_equiv_left _ _ _ Hp).
    rewrite (seq_equiv_right p' _ _ Hq).
    reflexivity.
  Qed.

 
  Lemma star_equiv: forall p q, p === q -> p* === q*.
  Proof.
    intros p q H h h'.
    split; 
      (intros H0; destruct H0 as [n]; exists n;
       generalize dependent h';  generalize dependent h;
       induction n; intuition);
      simpl in H0; destruct H0 as [h'' [H0 H1]];
      apply H in H0; simpl; exists h''; split; try(apply IHn); assumption.
  Qed.

  Instance star_equiv_proper :
    Proper (equiv ==> equiv) Star.
  Proof. intros p q. apply star_equiv; assumption. Qed.



  (** * NetKAT Axioms & useful corollaries *)

  (* some auxilliary lemmas about kleisli composition *)
  Lemma kleisli_assoc: forall f f' f'' h,
    eq (kleisli (kleisli f f') f'' h) (kleisli f (kleisli f' f'') h).
  Proof.
    intros p q r h0.
    intros h1.
    split; intros H; destruct H as [h' [H1 H2]];
    [destruct H1 as [h'' [H0 H1]] | destruct H2 as [h'' [H2 H3]]];
    repeat (eapply ex_intro; intuition eauto).
  Qed.

  Lemma kleisli_right_id: forall f h, eq (f h) (kleisli f (@singleton H.t) h).
  Proof.
    intros p h h'.
    split; intros H.
    + exists h'; intuition.
    + destruct H as [h'' [H0 H1]]. congruence.
  Qed.

  Lemma kleisli_left_id: forall f h, eq (f h) (kleisli (@singleton H.t) f h).
  Proof.
    intros p h h'.
    split; intros H.
    + exists h; intuition.
    + destruct H as [h'' [H0 H1]]. congruence.
  Qed.

  Lemma power_slide: forall n f h, 
    eq (power (S n) f h) (kleisli (power n f) f h).
  Proof.
    intros n.
    induction n; intros f h.
    + simpl. unfold kleisli. split; intros H; destruct H as [h'' [H0 H1]].
      - exists h. intuition congruence.
      - exists x. intuition congruence.
    + cut (eq (kleisli f (power (S n) f) h) (kleisli (kleisli f (power n f)) f h)); auto.
      rewrite -> kleisli_assoc. intros h'.
      split; intros H; destruct H as [h'' [H0 H1]];
      exists h''; split; try(apply IHn); assumption.
  Qed.

  Corollary power_slide': forall n f h, 
    eq (kleisli f (power n f) h) (kleisli (power n f) f h).
  Proof.
    apply power_slide.
  Qed.

  Lemma power_decompose n m f h h':
    power (m+n) f h h' <-> exists h'', power m f h h'' /\ power n f h'' h'.
  Proof.
    split; intro H; generalize dependent h; generalize dependent h';
    generalize dependent n; induction m; intros; simpl in *.
    - exists h. intuition.
    - destruct H as [h'' [H0 H1]].
      assert (H2 := IHm _ _ _ H1).
      destruct H2 as [h''' [H2 H3]].
      exists h'''; intuition simpl.
      exists h''; intuition.
    - destruct H as [h'' [H0 H1]]. congruence.
    - destruct H as [h'' [H0 H2]].
      destruct H0 as [h''' [H0 H1]].
      exists h'''; eauto.
    Qed.

  (* NetKAT axioms and useful corollaries *)
  Theorem ka_plus_assoc : forall p q r : policy, (p+q)+r === p+(q+r).
  Proof.
   intros p q r h.
   apply union_assoc.
  Qed.

  Theorem ka_plus_comm : forall p q : policy, p + q === q + p.
  Proof.
   intros p q h.
   simpl.
   apply union_comm.
  Qed.

  Theorem ka_plus_zero : forall p : policy, p + Drop === p.
  Proof.
    intros p h.
    simpl.
    apply union_empty_right.
  Qed.

  Corollary ka_zero_plus: forall p : policy, Drop + p === p.
  Proof. 
    intros p.
    rewrite -> ka_plus_comm; rewrite -> ka_plus_zero; reflexivity.
  Qed.

  Theorem ka_plus_idem : forall p : policy, p + p === p.
  Proof.
    intros p h.
    simpl.
    apply union_idem.
  Qed.

  Theorem ka_seq_assoc : forall p q r : policy, (p;;q);;r === p;;(q;;r).
  Proof.
    intros p q r h.
    simpl.
    apply kleisli_assoc.
  Qed.

  Theorem ka_one_seq : forall p : policy, Id;; p === p.
  Proof.
    intros p h h'.
    split; intro H.
    + destruct H as [h''[H0 H1]]. simpl in H0. congruence.
    + simpl. eapply ex_intro; eauto.
  Qed.

  Theorem ka_seq_one : forall p : policy, p;; Id === p.
  Proof.
    intros p h h'.
    split; intro H.
    + destruct H as [h''[H0 H1]]. simpl in H1. congruence.
    + simpl. eapply ex_intro; eauto.
  Qed.

  Theorem ka_seq_dist_l : forall p q r : policy,
    p;; (q + r) === p;;q + (p;; r).
  Proof.
    intros p q r h h''.
    split; intro H.
    + destruct H as [h' [H0 [H1|H1]]]; [left | right]; exists h'; auto.
    + repeat destruct H; exists x; intuition eauto.
      - apply union_mono_left; assumption.
      - apply union_mono_right; assumption.
  Qed.

  Theorem ka_seq_dist_r : forall p q r : policy,
    (p + q);; r === p;;r + q;; r.
  Proof.
    intros p q r h h''.
    split; intro H.
    + destruct H as [h' [[H1|H1] H0]]; [left | right]; exists h'; auto.
    + repeat destruct H; exists x; intuition eauto.
      - apply union_mono_left; assumption.
      - apply union_mono_right; assumption.
  Qed.

  Theorem ka_zero_seq : forall p : policy, Drop;; p === Drop.
  Proof.
    intros p h h'.
    split; intros H; repeat destruct H; eauto.
  Qed.

  Theorem ka_seq_zero : forall p : policy, p;; Drop === Drop.
  Proof.
    intros p h h'.
    split; intros H; repeat destruct H; eauto.
  Qed.

  Theorem ka_unroll_l : forall p : policy, Id + p;;p* === p*.
  Proof.
    intros p h h'.
    split; intros H; repeat destruct H.
    + exists 0. congruence.
    + destruct H0 as [n H0]. exists (S n).
      simpl. exists x. auto.
    + destruct x; simpl in H; [left|right].
      - congruence.
      - repeat destruct H. exists x0. intuition eauto.
        exists x. assumption.
  Qed.

  Theorem ka_unroll_r : forall p : policy, Id + p*;;p === p*.
  Proof.
    intros p h h'.
    split; intros H; repeat destruct H.
    + exists 0. congruence.
    + exists (S x0).
      simpl. apply power_slide. exists x. auto.
    + destruct x; simpl in H; [left|right].
      - congruence.
      - apply power_slide' in H.
        repeat destruct H. exists x0. intuition eauto.
        exists x. assumption.
  Qed.

  Lemma ka_seq_mon_left: forall p q r, p <== q -> p;;r <== q;;r.
  Proof.
    intros p q r H h h'.
    split; intros H0.
    + repeat destruct H0; exists x; intuition.
      apply H. left. assumption.
    + right. assumption.
  Qed.

  Lemma ka_seq_mon_right: forall p q r, q <== r -> p;;q <== p;;r.
  Proof.
    intros p q r H h h'.
    split; intros H0.
    + repeat destruct H0; exists x; intuition.
      apply H. left. assumption.
    + right; assumption.
  Qed.

  Lemma ka_plus_mon_left: forall p q r, p<==q -> p + r <== q + r.
  Proof.
    intros p q r H h h'.
    split; intros H0.
    + destruct H0 as [[H0|H0]|[H0|H0]]; [left|right|left|right]; auto.
      apply H; left; assumption.
    + right; assumption.
  Qed.

  Lemma ka_plus_mon_right: forall p q r, q<==r -> p + q <== p + r.
  Proof.
    intros p q r H h h'.
    split; intros H0.
    + destruct H0 as [[H0|H0]|[H0|H0]]; [left|right|left|right]; auto.
      apply H; left; assumption.
    + right; assumption.
  Qed.

  Lemma ka_plus_leq: forall p q r, (p + q <== r) <-> (p <== r /\ q <== r).
  Proof.
    intros p q r.
    split; intro H.
      split;intros h h';split; intro H'.
        destruct H'. apply H. left. left. assumption. assumption.
        right; assumption.
        apply H. destruct H' as [H0|H0]; [left;right|right]; assumption.
        right; assumption.
    destruct H as [H0 H1].
    intros h h'.
    split; intro H.
      destruct H as [H|H].
        destruct H as [H|H]; [apply H0 | apply H1]; left; assumption.
        assumption.
    right. assumption.
  Qed.

  (*
  Theorem ka_lfp_l: forall p q r, (q + p;r <== r) -> (p*;q <== r).
  Proof.
    intros p q r H.
    rewrite -> ka_plus_leq in H.
    destruct H as [H0 H1].
    intros h h'.
    split; intros H.
      destruct H.
        destruct H as [h'']; destruct H as [H2 H3]. destruct H2 as [n].
        induction n.
          apply H0. left. simpl in H. unfold HSet.singleton in H. subst h''. assumption.
        simpl in H. apply power_slide' in H.
          destruct H as [h''']. destruct H as [H2 H4].
          apply (IHn h'''). assumption.
 
  Qed.
  *)
    

  (** * Tactics for automated axiomatic reasoning *)
  Create HintDb netkat.
  Hint Rewrite ka_plus_assoc ka_plus_zero ka_zero_plus ka_plus_idem
    ka_seq_assoc ka_one_seq ka_seq_one ka_zero_seq ka_zero_plus
    ka_seq_zero : netkat.

  (* Tactic that tries to rewrite using all "safe" rules and
     then discharges all trivial goals. *)
  Ltac netkat :=
    simpl; try reflexivity;
    autorewrite with netkat using (simpl; try reflexivity).

  (* Tactic that does case splits on policies and then tries
     to solve goals using axiomatic rewriting *)
Ltac netkat_cases :=
intros;
(match goal with
  | [ p:policy, q:policy, r:policy |- _ ] =>
      destruct p; destruct q; destruct r
  | [ p:policy, q:policy |- _ ] => destruct p; destruct q
  | [ p:policy |- _ ] => destruct p
  | _ => idtac
end); netkat.

Ltac netkat_induction id :=
  induction id as [ | | | | | p1 IH1 p2 IH2 | p1 IH1 p2 IH2 | p0 IH | ];
  netkat;
  match goal with
    | [IH1: _ === _, IH2: _ === _ |- _ ] => 
        first [rewrite -> IH1; rewrite <- IH1];
        first [rewrite -> IH2; rewrite <- IH2]
    | [IH: _ === _ |- _] => first [rewrite -> IH | rewrite <- IH]
  end;
  netkat.
    


End NetKAT.


