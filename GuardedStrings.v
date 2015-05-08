Require Import List Coq.Program.Equality Bool Omega FunctionalExtensionality.
Import ListNotations.
Require Export NetKAT InductiveNETKAT Sets Misc Classes.


Ltac invert H := inversion H; subst; clear H.
Ltac gd id := generalize dependent id.



Module GS (F : FIELDSPEC) (V : VALUESPEC(F)).
Include  InductiveNETKAT.NetKAT'(F)(V).

(* For now, assume that the set of packets is finite as an axiom.
   This will follow automatically once we show that
   Finite X -> Finite Y -> Finite (X->Y).                        *)
Axiom P_finite : Finite P.t.
Global Instance : Finite P.t := P_finite.
Global Instance value_eqtype (f : F.t) : EqType (V.t f) := (V.eq_dec f). 








(** guarded strings *******************************************)

Inductive gs := GS : P.t -> list P.t -> P.t -> gs.
Arguments GS a w b : rename.
Hint Constructors gs.
Notation "a ~( w )~ b" := (GS a w b) (at level 1, format "a ~( w )~ b").

Global Program Instance : EqType gs := fun x y => match x,y with
  a~(w)~b, a'~(w')~b' => if (a,w,b) =d= (a',w',b') then left _ else right _
end.

Parameters (a b : P.t) (w : list P.t).
Check (a~(w)~b).

Definition gs_length (gs : gs) :=
  let '_~(w)~_ := gs in length w.

Definition gs_conc (s1 s2 : gs) :=
  let 'a~(w)~b := s1 in
  let 'b'~(v)~c := s2 in
  if b =d= b' then Some (a~(w++v)~c) else None.

Definition take (n:nat) (s:gs) (c : P.t) : gs :=
  let 'a~(w)~b := s in
  let w' := firstn n w in
  a~(w')~c.

Definition drop (n:nat) (c : P.t) (s:gs) : gs :=
  let 'a~(w)~b := s in
  let w' := skipn n w in
  c~(w')~b.

Theorem conc_take_drop (s: gs) (n : nat) c : 
  gs_conc (take n s c) (drop n c s) = Some s.
Proof.
  gd s; destruct n; intros; destruct s as [a w b].
  + simpl. destruct (c =d= c); intuition auto.
  + simpl. destruct (c =d= c); intuition auto.
    destruct w; intuition simpl.
    rewrite firstn_skipn. reflexivity.
Qed.

(** End guarded strings #######################################*)










(** languages over guarded strings *****************************)

Definition gs_lang := gs -> bool.

Definition gs_lang_union L1 L2 := [$ s : gs | s \in L1 || s \in L2 ].

Theorem lang_union_correct L1 L2 s :
  (s \in L1 = true \/ s \in L2 = true) <-> s \in gs_lang_union L1 L2 = true.
Proof. rewrite <- orb_true_iff. unfold gs_lang_union. intuition. Qed.
Hint Resolve lang_union_correct.

Check existsb.

Definition gs_lang_conc L1 L2 := [$ s : gs | [$ exists a | 
  existsb (fun n => take n s a \in L1 && drop n a s \in L2) (seq 0 (S (gs_length s))) ] ].

Lemma firstn_app {X} (xs ys : list X) : firstn (length xs) (xs ++ ys) = xs.
Proof. gd xs; gd ys; induction xs; intros; intuition simpl. congruence. Qed.

Lemma skipn_app {X} (xs ys : list X) : skipn (length xs) (xs ++ ys) = ys.
Proof. gd xs; gd ys; induction xs; intros; intuition simpl. Qed.

Theorem lang_conc_correct L1 L2 s :
  (exists s1 s2, (Some s = gs_conc s1 s2) /\ (s1 \in L1 = true) /\ (s2 \in L2 = true))
  <-> (s \in gs_lang_conc L1 L2 = true).
Proof.
  split; intro H.
  + destruct H as [s1 [s2 [H0 [H1 H2]]]].
    destruct s1 as [a w b]; destruct s2 as [b' v c].
    simpl in H0. destruct (b =d= b'); invert H0.
    unfold gs_lang_conc. apply exists_iff. exists b'.
    apply existsb_exists. exists (length w).
    split.
    - clear H1; clear H2; induction w; simpl; intuition auto.
      simpl in IHw; destruct IHw; intuition auto.
      repeat right. rewrite <- seq_shift. apply in_map. assumption.
    - simpl. rewrite firstn_app; rewrite skipn_app.
      rewrite H1; rewrite H2. auto.
  + unfold gs_lang_conc in H; rewrite existsb_exists in H.
    destruct H as [c [_ H]]. rewrite existsb_exists in H.
    destruct H as [n [_ H]]. rewrite andb_true_iff in H.
    exists (take n s c). exists (drop n c s).
    intuition try fail. symmetry. apply conc_take_drop.
Qed.
Hint Resolve lang_conc_correct.

(** End languages over guarded strings ########################*)











(** NFAs over guarded strings **********************************)

Record nfa := {
  nfa_state :> Type;
  nfa_finite :> Finite nfa_state;
  nfa_eqtype :> EqType nfa_state;
  nfa_s : nfa_state;
  nfa_accept : nfa_state -> P.t -> P.t -> bool;
  nfa_trans : nfa_state -> P.t -> P.t -> nfa_state -> bool
}.

Global Instance nfa_is_finite (A : nfa) : Finite (nfa_state A) := nfa_finite A.
Global Instance nfa_is_eqtype (A : nfa) : EqType (nfa_state A) := nfa_eqtype A.
Arguments nfa_accept {A} q a b : rename.
Arguments nfa_trans {A} q a b q' : rename.


Fixpoint accept_n {A : nfa} (q : A) gs n :=
match gs with
  | a~([])~b => nfa_accept q a b
  | a~(b::w)~c =>
  match n with
  | O => false
  | S n => [$ exists q' | nfa_trans q a b q' && accept_n q' b~(w)~c n ]
  end
end.

Definition accept {A : nfa} (q : A) gs := accept_n q gs (gs_length gs).
Hint Unfold accept.

Inductive accept_prop {A : nfa} (q : A) : gs -> Prop :=
  | accept_atom : forall a b, nfa_accept q a b = true -> accept_prop q a~([])~b
  | accept_trans : forall a b c w q', nfa_trans q a b q' = true -> accept_prop q' b~(w)~c -> 
      accept_prop q a~(b::w)~c.
Hint Constructors accept_prop.

Theorem accept_correct (A : nfa) (q : A) gs : accept_prop q gs <-> accept q gs = true.
Proof.
  destruct gs as [a w b].
  split; intro H; gd q; gd a; gd b; induction w; intros;
  unfold accept in *; simpl;  try invert H; auto.
  + apply exists_iff; exists q'.
    apply andb_true_iff. intuition eauto.
  + apply exists_iff in H1. destruct H1 as [q' H1].
    apply andb_true_iff in H1; destruct H1 as [H1 H2].
    eauto.
Qed.

Definition nfa_lang (A : nfa) := [$ gs | accept (nfa_s A) gs ].
Hint Unfold nfa_lang.






(** primitive automata ****************************************************)

(*

Definition nfa_empty :=
  {| nfa_s := tt; nfa_accept q a b := false; nfa_trans q a b q' := false |}.

Definition nfa_id :=
  {| nfa_s := tt; nfa_accept q a b := (a =b= b); nfa_trans q a b q' := false |}. 

Definition nfa_singleton a b :=
  {| nfa_s := tt; nfa_trans q a b q' := false;
     nfa_accept q a' b' := if a =d= a' then (if b =d= b' then true else false)
                           else false
  |}.

Definition nfa_filter f :=
  {| nfa_s := tt; nfa_accept q a b := f a; nfa_trans q a b q' := false |}.

Definition nfa_mod m :=
  {| nfa_s := tt; nfa_accept q a b := (b =b= m a); nfa_trans q a b q' := false |}.

Lemma nfa_empty_correct : nfa_lang nfa_empty = pred0.
Proof.
  extensionality s.
  unfold nfa_lang.
  unfold accept; destruct s as [a [ |b w] c]; simpl; reflexivity.
Qed.

Lemma nfa_id_correct : nfa_lang nfa_id = [$ s | let 'a~(w)~b := s in (a =b= b) && (w =b= [])].
Proof.
  apply pred_eq_intro. intro s; destruct s as [a w b]; unfold nfa_lang.
  rewrite <- accept_correct. rewrite andb_true_iff.
  split; intro H; invert H.
  + invert H1. intuition.
  + invert H2.
  + rewrite eqb_eq in H1. subst w. eauto.
Qed.

Lemma nfa_singleton_correct a b : 
  nfa_lang (nfa_singleton a b) = [$ w | w =b= a~([])~b ].
Proof.
  extensionality x. unfold nfa_lang, accept.
  destruct (x =d= a~([])~b); subst; simpl.
  + rewrite eqb_refl.
    destruct (a =d= a); destruct (b =d= b); congruence.
  + rewrite <- eqb_eq_false in n. rewrite n.
    destruct x as [a' [ | b' w] c]; simpl; auto.
    destruct (a =d= a'); destruct (b =d= c); try congruence.
    subst; rewrite eqb_refl in n. assumption.
Qed.

*)

Definition nfa_pred p :=
  {| nfa_s := tt; nfa_accept q a b := p a b; nfa_trans q a b q' := false |}.

Lemma nfa_pred_correct p : 
  nfa_lang (nfa_pred p) = [$ s | let 'a~(w)~b := s in (p a b) && (w =b= [])].
Proof.
  apply pred_eq_intro. intro s; destruct s as [a w b]; unfold nfa_lang.
  rewrite <- accept_correct.
  split; intro H; invert H; simpl in *; try apply andb_true_iff; intuition.
  + rewrite andb_true_iff in H1. destruct H1 as [H0 H1]; rewrite eqb_eq in H1.
    subst w. auto.
Qed.



Definition nfa_dup :=
  {| nfa_s := false;
     nfa_accept q a b := q && (a =b= a);
     nfa_trans q a b q' :=  negb q && q' && (a =b= b) |}.

Lemma nfa_dup_correct : 
  nfa_lang nfa_dup = [$ s | let 'a~(w)~b := s in (a =b= b) && (w =b= [a])].
Proof. admit. Qed.
    



(** nfa_union *****************************************************************)
  
Definition nfa_union (A B : nfa) :=
  {| nfa_s := None;
     nfa_accept q a b := 
       match q with
         | None => nfa_accept (nfa_s A) a b || nfa_accept (nfa_s B) a b
         | Some (inl q) => @nfa_accept A q a b
         | Some (inr q) => @nfa_accept B q a b
       end;
     nfa_trans q a b q' :=
       match q,q' with
         | _, None | Some (inl _), Some (inr _) | Some (inr _), Some (inl _) => false
         | None, Some (inl q') => nfa_trans (nfa_s A) a b q'
         | None, Some (inr q') => nfa_trans (nfa_s B) a b q'
         | Some (inl q), Some (inl q') => @nfa_trans A q a b q'
         | Some (inr q), Some (inr q') => @nfa_trans B q a b q'
       end
  |}.

Lemma nfa_union_correct_left (A B : nfa) (q:A) gs :
  @accept_prop (nfa_union A B) (Some (inl q)) gs <-> accept_prop q gs.
Proof.
  destruct gs as [a w b].
  gd a; gd b; gd q; induction w; intros;
  split; intro H; inversion H; simpl in *; eauto 2.
  + destruct q' as [[q'|q']| ]; inversion H2. econstructor; eauto.
    apply IHw. assumption.
  + econstructor. instantiate (1 := Some (inl q')). simpl. assumption.
    rewrite IHw. assumption.
Qed.

Lemma nfa_union_correct_left' (A B : nfa) (q:A) : 
  [$ gs | @accept (nfa_union A B) (Some (inl q)) gs ] = [$ gs | accept q gs].
Proof.
  apply pred_eq_intro.
  intro gs. repeat rewrite <- accept_correct. apply nfa_union_correct_left.
Qed.

Lemma nfa_union_correct_right (A B : nfa) (q:B)  gs :
  @accept_prop (nfa_union A B) (Some (inr q)) gs <-> accept_prop q gs.
Proof.
  destruct gs as [a w b].
  gd a; gd b; gd q; induction w; intros;
  split; intro H; inversion H; simpl in *; eauto 2.
  + destruct q' as [[q'|q']| ]; inversion H2. econstructor; eauto.
    apply IHw. assumption.
  + econstructor. instantiate (1 := Some (inr q')). simpl. assumption.
    rewrite IHw. assumption.
Qed.

Lemma nfa_union_correct_right' (A B : nfa) (q:B) : 
  [$ gs | @accept (nfa_union A B) (Some (inr q)) gs ] = [$ gs | accept q gs].
Proof.
  apply pred_eq_intro.
  intro gs. repeat rewrite <- accept_correct. apply nfa_union_correct_right.
Qed.

Lemma nfa_union_correct A B :
  nfa_lang (nfa_union A B) = gs_lang_union (nfa_lang A) (nfa_lang B).
Proof.
  unfold nfa_lang.
  apply pred_eq_intro.
  intro gs. rewrite <- lang_union_correct.
  repeat rewrite <- accept_correct.
  destruct gs as [a [ | b w] c];
  split; intro H; [ |destruct H as [H|H]| |destruct H as [H|H]];
  inversion H; simpl in *.
  - destruct (orb_prop _ _ H1) as [H3|H3]; eauto.
  - constructor. simpl. rewrite H1; simpl; reflexivity.
  - constructor. simpl. apply orb_true_intro; auto.
  - destruct q' as [[q'|q']| ]; inversion H2; [left|right];
    [rewrite nfa_union_correct_left in H5 | rewrite nfa_union_correct_right in H5];
    eauto.
  - econstructor. instantiate (1 := Some (inl q')); simpl; assumption.
    apply nfa_union_correct_left. assumption.
  - econstructor. instantiate (1 := Some (inr q')); simpl; assumption.
    apply nfa_union_correct_right. assumption.
Qed.






(** nfa_seq *****************************************************************************)


Section nfa_seq.

Definition nfa_seq A1 A2 : nfa :=
 {| nfa_s := inl (nfa_s A1);
    nfa_accept q a b :=
      match q with
        | inl q => [$ exists c | (nfa_accept q a c) && (nfa_accept (nfa_s A2) c b)]
        | inr q => nfa_accept q a b
      end;
    nfa_trans q a b q' :=
      match q,q' with
        | inl q, inl q' => nfa_trans q a b q'
        | inl q, inr q' => [$ exists c | (nfa_accept q a c) && (nfa_trans (nfa_s A2) c b q')]
        | inr q, inr q' => nfa_trans q a b q'
        | inr q, inl q' => false
      end
 |}.

Lemma bool_iff P1 P2 B1 B2 :
  (P1 <-> B1 = true) -> (P2 <-> B2 = true) -> (P1 <-> P2) -> B1=B2.
Proof.
  intros H1 H2 H.
  assert(B1 = true <-> B2 = true) by (rewrite <- H1; rewrite <- H2; assumption).
  case_eq B1; case_eq B2; intuition congruence.
Qed.

Lemma seq_inr A1 A2 q gs :
  @accept (nfa_seq A1 A2) (inr q) gs = accept q gs.
Proof.
  apply (bool_iff (@accept_prop (nfa_seq A1 A2) (inr q) gs) (accept_prop q gs));
  try apply accept_correct.
  destruct gs as [a w b].
  split; intro H; gd a; gd b; gd q; induction w; intros; invert H; simpl in *; auto.
  - destruct q'; eauto 4. invert H2.
  - econstructor. instantiate (1 := inr q'). simpl. assumption. eauto.
Qed.

Lemma seq_inl A1 A2 q s :
  (exists s1 s2, Some s = gs_conc s1 s2 /\ accept_prop q s1
                                        /\ s2 \in nfa_lang A2 = true) 
  <-> (@accept (nfa_seq A1 A2) (inl q) s = true).
Proof. admit. Qed.

Lemma seq_correct A1 A2 :
  nfa_lang (nfa_seq A1 A2) = gs_lang_conc (nfa_lang A1) (nfa_lang A2).
Proof. 
  apply pred_eq_intro. intro gs. rewrite <- lang_conc_correct.
  unfold nfa_lang. simpl. rewrite <- seq_inl.
  split; intro H; destruct H as [s1 [s2 [H0 [H1 H2]]]];
  exists s1; exists s2; intuition; apply accept_correct; assumption.
Qed.

End nfa_seq.






(* NetKAT to NFA ***************************************************************)

Fixpoint netkat_nfa (p : policy) : nfa :=
match p with
  | Drop  => nfa_pred (fun _ _ => false)
  | Id    => nfa_pred (fun _ _ => true)
  | Dup   => nfa_dup
  | f==n  => nfa_pred (fun p _ => (p f) =b= n)
  | f!=n  => nfa_pred (fun p _ => negb ((p f) =b= n))
  | f<-n  => nfa_pred (fun p p' => p' =b= p[f:=n])
  | q+r   => nfa_union (netkat_nfa q) (netkat_nfa r)
  | q;;r  => nfa_seq (netkat_nfa q) (netkat_nfa r)
  | q*    => nfa_pred (fun _ _ => false)
end.


Theorem netkat_nfa_correct (p : policy) a b w :
  (| p |) (a,[]) (b,w) <-> (a~(w)~b \in nfa_lang (netkat_nfa p) = true).
Proof.
  split; intro H.
  + dependent induction H; unfold nfa_lang;
    try solve [unfold accept; simpl; auto 2].
    - unfold accept; simpl; auto. apply negb_true_iff.
      apply eqb_eq.
    -



End GS.