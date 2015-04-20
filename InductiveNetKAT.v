Require Export NetKAT Misc.
Require Import List Coq.Program.Equality Bool Omega.
Require Import Relations Relations.Relation_Operators.
Require Import Arith.Wf_nat.
Import ListNotations.

Ltac invert id := inversion id; try (subst); eauto.

Module NetKAT' (F : FIELDSPEC) (V : VALUESPEC(F)).

  Include NetKAT.NetKAT(F)(V).
  

  Inductive bstep : policy -> H.t -> H.t -> Prop :=
  | BstepId : forall h, bstep Id h h
  | BstepFilter : forall f v pk h, pk f = v -> bstep (Filter f v) (pk,h) (pk,h)
  | BstepNFilter : forall f v pk h, pk f <> v -> bstep (NFilter f v) (pk,h) (pk,h)
  | BstepMod : forall f v pk h, bstep (Mod f v) (pk,h) (pk[f:=v], h)
  | BstepPlusLeft : forall h h' p q, bstep p h h' -> bstep (p+q) h h'
  | BstepPlusRight : forall h h' p q, bstep q h h' -> bstep (p+q) h h'
  | BstepSeq : forall h h' h'' p q, bstep p h h' -> bstep q h' h'' -> bstep (p;;q) h h''
  | BstepStarRefl : forall h p, bstep (p*) h h
  | BstepStarTrans : forall h h' h'' p, bstep p h h' -> bstep (p*) h' h'' -> bstep (p*) h h''
  | BstepDup : forall pk h, bstep Dup (pk,h) (pk,pk::h).

  (* Notation "'[||' p '||]'" := (bstep p) (at level 1). *)

  Hint Constructors bstep.

  Lemma bstep_interpret : forall p h h', bstep p h h' -> interpret p h h'.
  Proof.
    intros p h h' H.
    induction H; simpl; try (simpl in H); auto.
    - rewrite <- V.eqb_eq in H.
      rewrite -> H.
      unfold HSet.singleton; reflexivity.
    - rewrite <- V.eqb_eq in H.
      rewrite if_negb.
      case (V.eqb f (pk f) v) eqn:H'; eauto.
    - left; assumption.
    - right; assumption.
    - exists h'. intuition.
    - exists 0; simpl; auto.
    - destruct IHbstep2 as [n].
      exists (S n). simpl. exists h'. intuition.
  Qed.

  Lemma interpret_bstep : forall p h h', interpret p h h' -> bstep p h h'.
  Proof.
    intros p.
    induction p; intros h h' H; destruct h as [pk h];
    simpl in H; try (unfold HSet.empty in H); try (unfold HSet.singleton in H);
    try (subst h'; constructor); intuition.
    - case (V.eqb f (pk f) t) eqn: H'; intuition.
      + rewrite V.eqb_eq in H'. subst h'. auto.
    - case (V.eqb f (pk f) t) eqn: H'; simpl in H; intuition.
      + subst h'. constructor. simpl. rewrite <- V.eqb_eq. intuition. congruence.
    - destruct H; [apply BstepPlusLeft|apply BstepPlusRight]; intuition.
    - destruct H as [h'']. apply (BstepSeq _ h''); intuition.
    - destruct H as [n].
      generalize dependent pk; generalize dependent h; generalize dependent h';
      induction n; intros h' h pk H; simpl in H.
      + unfold HSet.singleton in H. subst h'. constructor.
      + destruct H as [h'']. apply (BstepStarTrans _ h'');
        destruct h'' as [pk'' h'']; intuition.
    Qed.


Arguments V.eqb {f} _ _.

Inductive sstep : prod policy H.t -> prod policy H.t -> Prop :=
| sstep_Filter_pass :
    forall pk h f v, (pk f) = v -> sstep (f==v, (pk,h)) (Id, (pk,h))
| sstep_Filter_drop :
    forall pk h f v, (pk f) <> v -> sstep (f==v, (pk,h)) (Drop, (pk,h))
| sstep_NFilter_pass :
    forall f v pk h, (pk f) <> v -> sstep (f!=v, (pk,h)) (Id, (pk,h))
| sstep_NFilter_drop :
    forall f v pk h, (pk f) = v -> sstep (f!=v, (pk,h)) (Drop, (pk,h))
| sstep_Mod :
    forall f v pk h, sstep (f<-v, (pk,h)) (Id, (pk[f:=v],h))
| sstep_Union_left :
    forall p q h, sstep (p+q, h) (p, h)
| sstep_Union_right :
    forall p q h, sstep (p+q, h) (q, h)
| sstep_Seq_progress :
    forall p q h r h', sstep (p, h) (r, h') -> sstep (p;;q, h) (r;;q, h')
| sstep_Seq_finish :
    forall q h, sstep (Id;;q, h) (q, h)
| sstep_Seq_fail :
    forall q h, sstep (Drop;;q, h) (Drop, h)
| sstep_Star_unfold :
    forall p h, sstep (p*,h) (p;;p*, h)
| sstep_Star_finish :
    forall p h, sstep (p*, h) (Id,h)
| sstep_Dup :
    forall pk h, sstep (Dup, (pk,h)) (Id, (pk,pk::h)).

Hint Constructors sstep.

Lemma sstep_mono : forall p pk h q pk' h',
  sstep (p,(pk,h)) (q,(pk',h')) -> length h <= length h'.
Proof.
  intros. dependent induction H; simpl; eauto.
Qed.

Lemma sstep_progress :
  forall p, (p=Id) \/ (p=Drop) \/ (forall h, exists r h', sstep (p,h) (r,h')).
Proof.
  intros.
  induction p; first [auto;fail | right;right;intro;destruct h as [pk h] ]; eauto.
  + destruct (V.eq_dec f (pk f) t); eauto.
  + destruct (V.eq_dec f (pk f) t); eauto.
  + dependent destruction IHp1; eauto; dependent destruction H; subst; eauto.
    assert (H':= H (pk,h)); clear H.
    destruct H' as [r]; destruct H as [h']; exists (r;;p2); exists h'; eauto.
Qed.

Inductive npower {A : Type} (R : relation A) : nat -> relation A :=
| npower0 : forall x, npower R 0 x x
| npowerS : forall n x y z, R x y -> npower R n y z -> npower R (S n) x z.
Hint Constructors npower.

Hint Constructors clos_refl_trans_1n.

Lemma clos_trans_refl_nat :
  forall {A} R x y, clos_refl_trans_1n A R x y <-> exists n, npower R n x y.
Proof.
  split; intros.
  + dependent induction H.
    - exists 0; eauto.
    - destruct IHclos_refl_trans_1n as [n]; exists (S n). eauto.
  + destruct H as [n].
    generalize dependent x; generalize dependent y.
    dependent induction n; intros; invert H.
Qed.

Definition ssteps := clos_refl_trans_1n (prod policy H.t) sstep.
Hint Unfold ssteps.

Lemma clos_rt1n_trans : forall X R x y z, clos_refl_trans_1n X R x y ->
  clos_refl_trans_1n X R y z -> clos_refl_trans_1n X R x z.
Proof. intros.
  apply clos_rt_rt1n; eapply rt_trans; eapply clos_rt1n_rt; eauto.
Qed.

Lemma ssteps_bstep : forall p h1 h2, ssteps (p,h1) (Id,h2) -> bstep p h1 h2.
Proof.
  intros.
  unfold ssteps in H.
  apply clos_trans_refl_nat in H.
  destruct H as [n].
  generalize dependent h2; generalize dependent h1; generalize dependent p.
  dependent induction n; intros; invert H.
  destruct y as [q h3].
  assert (bstep q h3 h2) by intuition.
  clear IHn H H2.
  generalize dependent h2.
  dependent induction H1; intros; invert H0.
Qed.

Lemma ssteps_seq_assoc : forall p q r h1 h2,
  ssteps (p;;(q;;r), h1) (r, h2) -> ssteps (p;;q;;r, h1) (r, h2).
Proof.
  intros.
  unfold ssteps in H.
  apply clos_trans_refl_nat in H;
  destruct H as [n];
  generalize dependent h2; generalize dependent h1; generalize dependent r;
  generalize dependent q; generalize dependent p;
  dependent induction n; intros; invert H.
  - admit.
  - invert H1; invert H2.
    * subst x n h'; clear IHn H H6 H1 H2. admit.
    * eright; eauto. apply IHn; eauto.
    * admit.
    * eright; eauto. apply clos_trans_refl_nat; eauto.
    * invert H0.  
Qed.

Lemma bstep_ssteps : forall p q h1 h2, bstep p h1 h2 -> ssteps (p;;q,h1) (q,h2).
Proof.
  intros. generalize dependent q.
  dependent induction H; intros; subst; eauto 7.
  + assert (H0 := IHbstep q0); eauto.
  + assert (H0 := IHbstep q0); eauto.
  + assert (H1 := IHbstep1 (q;;q0)); assert (H2 := IHbstep2 q0).
    apply ssteps_seq_assoc. eauto using clos_rt1n_trans.
  + clear H H0. assert (H0 := IHbstep1 (p*;;q)); assert (H1 := IHbstep2 q).
    eright. apply sstep_Seq_progress. apply sstep_Star_unfold.
    apply ssteps_seq_assoc. eauto using clos_rt1n_trans.
Qed.

Lemma sstep_id_right : forall p h1 h2,
  ssteps (p;;Id, h1) (Id, h2) -> ssteps (p,h1) (Id,h2).
Proof.
  intros.
  apply clos_rt1n_rt in H; apply clos_rt_rtn1 in H.
  invert H. destruct y as [q h3]. cut (q = Id;;Id).
  + intro H2. subst q. apply clos_rtn1_rt in H1. apply clos_rt_rt1n in H1.
    apply clos_trans_refl_nat in H1.
    destruct H1 as [n].
    generalize dependent h3; generalize dependent h2;
    generalize dependent h1; generalize dependent p. 
    dependent induction n; intros; invert H1.
    - inversion H0; eauto.
    - invert H0. destruct y as [q h3]. invert H3.
      * eright; eauto. eapply IHn; eauto. eright; eauto.
        apply clos_rt_rtn1. apply clos_rt1n_rt.
        eapply clos_trans_refl_nat. eauto.
      * invert H4; invert H2.
      * invert H4; invert H2.
  + apply clos_rtn1_rt in H1; apply clos_rt_rt1n in H1;
    apply clos_trans_refl_nat in H1; destruct H1 as [n].
    generalize dependent p; generalize dependent h1;
    generalize dependent q; generalize dependent h2;
    generalize dependent h3.
    dependent induction n; intros; invert H1.
    - invert H0.
    - destruct y as [r h4]. invert H3.
      * assert (H6:=H4);
        pattern n in H6; apply ex_intro in H6.
        apply clos_trans_refl_nat in H6.
        apply (IHn h3 h2 q H0 h4 r0).
        eright; eauto.
        apply clos_rt_rtn1; apply clos_rt1n_rt; assumption.
        assumption.
      * invert H4. invert H0. invert H2.
      * invert H4. invert H0. invert H2.
Qed.

Corollary bstep_ssteps_iff : forall p h1 h2,
  bstep p h1 h2 <-> ssteps (p,h1) (Id,h2).
Proof.
  split.
  + intro H. apply sstep_id_right. apply bstep_ssteps. assumption.
  + apply ssteps_bstep.
Qed.

Definition A p (h h' : H.t) :=
  let (pk, h) := h in
  let (pk',_) := h' in
  ssteps (p, (pk,h)) (Id, (pk',h)).

(* FIXME: fucked up case where q does not exist *)
Definition T p (h h' : H.t) q :=
  let (pk, h) := h in
  let (pk',_) := h' in
  ssteps (p, (pk,h)) (Dup;;q, (pk',h)).

Hint Unfold A.
Hint Unfold T.

Fixpoint A' (p : policy) :=
match p with
  | q+r => A' q + A' r
  | q;;r => A' q ;; A' r
  | q* => (A' q)*
  | Dup => Drop
  | x => x 
end.

Functional Scheme A'_ind := Induction for A' Sort Prop.

Fixpoint T' (p : policy) :=
match p with
  | q+r => T' q + T' r
  | q;;r => (A' q;; T' r) + (T' q;; r)
  | q* => (A' q)*;; (T' q);; q*
  | Dup => Id
  | x => Drop
end.

Fixpoint subt_fn p q :=
match q with
  | r;;s => p = q \/ subt_fn p r \/ subt_fn p s
  | r+s => p = q \/ subt_fn p r \/ subt_fn p s
  | r* => p = q \/ subt_fn p r
  | _ => p = q
end.
Functional Scheme subt_fn_ind := Induction for subt_fn Sort Prop.

Inductive subt p : policy -> Prop :=
  | subt_refl : subt p p
  | subt_plus_left : forall q r, subt p q -> subt p (q+r)
  | subt_plus_right : forall q r, subt p r -> subt p (q+r)
  | subt_seq_left : forall q r, subt p q -> subt p (q;;r)
  | subt_seq_right : forall q r, subt p r -> subt p (q;;r)
  | subt_star : forall q, subt p q -> subt p (q*).
Hint Constructors subt.

Lemma subt_iff : forall p q, subt p q <-> subt_fn p q.
Proof.
  split; intro H.
  + induction H; simpl; intuition.
    case p; simpl; intuition.
  + functional induction (subt_fn p q); eauto;
    intuition; subst; eauto.
Qed.


Lemma A'_dup_free : forall p, not (subt Dup (A' p)).
Proof.
  intros.
  functional induction (A' p); intuition; dependent destruction H; eauto.
Qed.

Lemma sstep_dup_free : forall p pk h q pk' h',
  sstep (p,(pk,h)) (q,(pk',h')) -> not (subt Dup p) -> h=h'.
Proof.
  intros. dependent induction H; eauto.
  intuition.
Qed.

Lemma sstep_dup_free_preservation : forall p pk h q pk' h',
  sstep (p,(pk,h)) (q,(pk',h')) -> not (subt Dup p) -> not (subt Dup q).
Proof.
  intros.
  dependent induction H; intro contra; inversion contra; intuition. eauto.
Qed.

Corollary ssteps_dup_free : forall p pk h q pk' h',
  ssteps (p,(pk,h)) (q,(pk',h')) -> not (subt Dup p) -> h=h'.
Proof.
  intros.
  dependent induction H; eauto.
  destruct y as [r [pk'' h'']].
  assert (h = h'') by eauto using sstep_dup_free; subst h''.
  eauto using sstep_dup_free_preservation.
Qed.

Corollary bstep_dup_free : forall p pk pk' h h',
  bstep p (pk,h) (pk',h') -> not (subt Dup p) -> h=h'.
Proof.
 intros. apply bstep_ssteps_iff in H.
 eapply ssteps_dup_free; eauto.
Qed.


Lemma A'_A : forall p h h',[|(A' p)|] h h' -> A p h h'.
Proof.
  intros.
  unfold A.
  destruct h as [pk h]; destruct h' as [pk' h'].
  apply interpret_bstep in H. apply bstep_ssteps_iff .
  generalize dependent h'; generalize dependent pk';
  generalize dependent h; generalize dependent pk.
  functional induction (A' p); intros;
  try (dependent destruction H; eauto; fail).
  + dependent destruction H. destruct h'0 as [pk'' h''].
    eapply BstepSeq.
    - eapply IHp0. apply H.
    - eapply IHp1. apply bstep_ssteps_iff in H.
      assert (h=h'') by eauto using A'_dup_free, ssteps_dup_free.
      subst; eauto.
  + assert (bstep (A' (q *)) (pk, h) (pk', h')) by (simpl; assumption).
    assert (h=h') by eauto using A'_dup_free, bstep_dup_free.
    subst h'; clear H0.
    dependent induction H; eauto. destruct h' as [pk'' h'].
    eapply BstepStarTrans. eapply IHp0; eauto.
    eapply IHbstep2; eauto.
    replace h' with h. reflexivity.
    eapply bstep_dup_free; eauto using A'_dup_free.
Qed.

Import ListNotations.
Record state : Type := mkState {
  e : H.t -> H.t -> Prop;
  d : H.t -> H.t -> nat -> Prop
}.

Check state.

Record nfa : Type := {
  states : list state 
}.

Set Implicit Arguments.
Definition shift (n:nat) :=
  map (fun s => {| e:= s.(e);  d:= (fun x y m => s.(d) x y (m-n)) |}).
Hint Unfold shift.

Check Is_true.

Definition closed (a : list state) := 
  forall s, In s a -> forall x y n, s.(d) x y n -> n < length a.
Hint Unfold closed.

Require Import FunctionalExtensionality.

Lemma shift0 : forall a, shift 0 a = a.
Proof.
 intros.
 induction a; auto.
 simpl. rewrite IHa. f_equal.
 destruct a; f_equal; simpl.
 extensionality x; extensionality y; extensionality m.
 intuition.
Qed.

Hint Rewrite shift0.
Hint Resolve shift0.

Definition dummy := {| e := fun _ _ => False; d := fun _ _ _ => False |}.
Hint Unfold dummy.


Lemma cons_dummy : forall a, closed a -> closed(dummy :: shift 1 a).
Proof.
  intros.
  unfold closed.
  intros. invert H0.
  + inversion H1.
  + unfold shift in H2. rewrite in_map_iff in H2.
    destruct H2 as [s']. destruct H2. rewrite <- H2 in H1; simpl in H1.
    cut (n < length a). simpl.
    admit. admit.
Qed.

Fixpoint automatize (p : policy) : list state :=
match p with
  | Dup => 
      [ mkState (bstep Drop) (fun x y n => x=y /\ n=1) ;
        mkState (bstep Id)   (fun _ _ _ => False) ]
  | x => [ mkState (bstep x) (fun _ _ _ => False) ]
end.

Functional Scheme automatize_ind := Induction for automatize Sort Prop.

End NetKAT'.