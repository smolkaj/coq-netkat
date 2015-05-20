(** NetKAT Automata & Language Theory *)

Require Import List Coq.Program.Equality Bool Omega FunctionalExtensionality Recdef.
Import ListNotations.
Require Export NetKAT InductiveNETKAT Sets Misc Classes Tactics.

Ltac invert H := inversion H; subst; clear H.



(** NetKAT language model.  ********************************************)
(* See the original NetKAT paper *)

Module Automata (F : FIELDSPEC) (V : VALUESPEC(F)).

Include  InductiveNETKAT.NetKAT(F)(V).



(** Guarded NetKAT Strings *******************************************)

(* P ; (P;dup)* ; P *)
Inductive gs := 
  | GS : P.t -> list P.t -> P.t -> gs.

Hint Constructors gs.

Global Arguments GS a w b : rename.

Notation "a ~( w )~ b" := (GS a w b) (at level 1, format "a ~( w )~ b").


(* equality on guarded NetKAT strings is decidable, since equality on packets
   is decidable *)
Global Program Instance : EqType gs := fun x y => match x,y with
  a~(w)~b, a'~(w')~b' => if (a,w,b) =d= (a',w',b') then left _ else right _
end.


Definition gs_length (gs : gs) :=
  let '_~(w)~_ := gs in length w.

(* Dexter also calls this the "fusion product",
   see "Automata on Guarded Strings and Applications" *)
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
  destruct s as [a w b]. destruct n; simpl.
  + split_if; intuition idtac.
  + split_if; intuition idtac.
    destruct w; intuition simpl.
    rewrite firstn_skipn. reflexivity.
Qed.

(** End Guarded NetKAT Strings #######################################*)







(** decidable languages over guarded NetKAT strings *****************************)

Definition gs_lang := gs -> bool.


(** UNION ****)

Definition gs_lang_union L1 L2 := [$ s : gs | s \in L1 || s \in L2 ].

Theorem lang_union_correct L1 L2 s :
  (s \in L1 = true \/ s \in L2 = true) <-> s \in gs_lang_union L1 L2 = true.
Proof. rewrite <- orb_true_iff. unfold gs_lang_union. intuition. Qed.



(** CONC ****)

Definition gs_lang_conc L1 L2 := [$ s : gs | [$ exists a | 
  existsb (fun n => take n s a \in L1 && drop n a s \in L2) (seq 0 (S (gs_length s))) ] ].

Lemma firstn_app {X} (xs ys : list X) : firstn (length xs) (xs ++ ys) = xs.
Proof. induction xs; intros; intuition simpl. congruence. Qed.

Lemma skipn_app {X} (xs ys : list X) : skipn (length xs) (xs ++ ys) = ys.
Proof. induction xs; intros; intuition simpl. Qed.

Theorem lang_conc_correct L1 L2 s :
  (exists s1 s2, (Some s = gs_conc s1 s2) /\ (s1 \in L1 = true) /\ (s2 \in L2 = true))
  <-> (s \in gs_lang_conc L1 L2 = true).
Proof.
  split; intro H.
  + steffen.
    destruct s1 as [a w b]; destruct s2 as [b' v c].
    simpl in H. split_if; invert H.
    unfold gs_lang_conc. apply exists_iff. exists b'.
    apply existsb_exists. exists (length w).
    split.
    - clear H1; clear H0; induction w; simpl; intuition auto.
      simpl in IHw; destruct IHw; intuition auto.
      repeat right. rewrite <- seq_shift. apply in_map. assumption.
    - simpl. rewrite firstn_app; rewrite skipn_app.
      rewrite H1; rewrite H0. auto.
  + unfold gs_lang_conc in H; rewrite existsb_exists in H.
    steffen.
    exists (take x0 s x). exists (drop x0 x s).
    intuition idtac. symmetry. apply conc_take_drop.
Qed.


(* missing: kleene star *)
Parameter gs_lang_star : gs_lang -> gs_lang.



(** End languages over guarded strings ########################*)
















(** NetKAT NFAs over guarded strings **************************************)
(* See "A Coalgebraic Decision Procedure for NetKAT" for details *)

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



(* We must define acceptance with "fuel" n as otherwise Coq cannot be convinced
   that accept terminates. *)
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
  | accept_atom : forall a b, 
      nfa_accept q a b = true -> accept_prop q a~([])~b
  (* - - -  - - - - - - -  - - - - - - - - - - - - - - - - *)
  | accept_trans : forall a b c w q',
     nfa_trans q a b q' = true -> accept_prop q' b~(w)~c -> 
        accept_prop q a~(b::w)~c.

Hint Constructors accept_prop.


Theorem accept_correct (A : nfa) (q : A) gs : accept_prop q gs <-> accept q gs = true.
Proof.
  destruct gs as [a w b].
  split; intro H; gd q; gd a; gd b; induction w; intros;
  unfold accept in *; simpl;  try invert H; steffen; eauto.
  + exists q'. steffen. intuition eauto.
Qed.


Definition nfa_lang (A : nfa) := [$ gs | accept (nfa_s A) gs ].
Hint Unfold nfa_lang.






(** primitive automata ****************************************************)

Definition nfa_pred p :=
  {| nfa_s := tt; 
     nfa_accept q a b := p a b; 
     nfa_trans q a b q' := false |}.


Lemma nfa_pred_correct p : 
  nfa_lang (nfa_pred p) = [$ s | let 'a~(w)~b := s in (p a b) && (w =b= [])].
Proof.
  apply pred_eq_intro. intro s; destruct s as [a w b]; unfold nfa_lang.
  rewrite <- accept_correct.
  split; intro H; invert H; simpl in *; intuition; steffen.
  subst w. auto.
Qed.



Definition nfa_dup :=
  {| nfa_s := false;
     nfa_accept q a b := q && (a =b= b);
     nfa_trans q a b q' := (negb q) && q' && (a =b= b) |}.


Lemma nfa_dup_correct : 
  nfa_lang nfa_dup = [$ s | let 'a~(w)~b := s in (a =b= b) && (w =b= [a])].
Proof. 
  apply pred_eq_intro; intro s; destruct s as [a w b]; unfold nfa_lang;
  rewrite <- accept_correct; split; intro H; steffen.
  + invert H. invert H1. invert H2. invert H4. invert H1.
    steffen. subst. split; congruence.
    invert H2. steffen. congruence.
  + subst. right with (q':=true); intuition; simpl.
    apply eqb_refl. left. simpl. apply eqb_refl.
Qed.
    



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
                                        /\ accept_prop (nfa_s A2) s2) 
  <-> (@accept (nfa_seq A1 A2) (inl q) s = true).
Proof.
  split; intro H.
  + destruct s as [a w c].
    destruct H as [[a' u b] [[b' v c'] [H1 [H2 H3]]]].
    apply accept_correct. gd a; gd w; gd c; gd b'; gd v; induction H2; intros.
    - rewrite <- conc_take_drop with (n:=0) (c:=b') in H1.
      simpl in H1. repeat split_if; invert H1; try congruence.
      invert H3.
      * left. simpl. apply exists_iff. exists b'. intuition.
      * eright. instantiate (1:=inr q'). simpl. apply exists_iff.
        exists b'. intuition. rewrite accept_correct in *. rewrite seq_inr.
        assumption.
   - simpl in H1. split_if; invert H1. eright. instantiate (1 := inl q').
     simpl; assumption. eapply IHaccept_prop. eassumption. simpl.
     split_if; intuition.
 + apply accept_correct in H. dependent induction H; simpl in H.
   - steffen. exists (a~([])~x); exists (x~([])~b). intuition eauto 2.
     simpl. split_if; intuition.
   - destruct q' as [q'|q'].
     * assert (exists s1 s2 : gs,
                  Some b~(w)~c = gs_conc s1 s2 /\
                  accept_prop q' s1 /\ accept_prop (nfa_s A2) s2) by eauto.
       steffen. destruct s1 as [b' u d]; destruct s2 as [d' v c'].
       simpl in H1. split_if; invert H1.
       exists a~(b'::u)~d'; exists d'~(v)~c'; intuition eauto 2.
       simpl. split_if; intuition.
     * steffen. exists a~([])~x; exists x~(b::w)~c; intuition eauto 2.
       simpl. split_if; intuition. eright with (q':=q'); eauto.
       rewrite accept_correct in *. rewrite <- seq_inr with (A1:=A1).
       assumption.
Qed.

Lemma nfa_seq_correct A1 A2 :
  nfa_lang (nfa_seq A1 A2) = gs_lang_conc (nfa_lang A1) (nfa_lang A2).
Proof. 
  apply pred_eq_intro. intro gs. rewrite <- lang_conc_correct.
  unfold nfa_lang. simpl. rewrite <- seq_inl.
  split; intro H; destruct H as [s1 [s2 [H0 [H1 H2]]]];
  exists s1; exists s2; intuition; apply accept_correct; assumption.
Qed.

End nfa_seq.







(** nfa_star *****************************************************************************)
(* TO BE IMPLEMENTED *)

Parameter nfa_star : nfa -> nfa.






(* NetKAT to NFA ***************************************************************)
(* this is Thompson's construction for NetKAT *)

Fixpoint netkat_nfa (p : policy) : nfa :=
match p with
  | Drop  => nfa_pred (fun _ _ => false)
  | Id    => nfa_pred (fun p p' => p =b= p')
  | Dup   => nfa_dup
  | f==n  => nfa_pred (fun p p' => (p =b= p') && ((p f) =b= n))
  | f!=n  => nfa_pred (fun p p' => (p =b= p') && ((p f) <b> n))
  | f<-n  => nfa_pred (fun p p' => p' =b= p[f:=n])
  | q+r   => nfa_union (netkat_nfa q) (netkat_nfa r)
  | q;;r  => nfa_seq (netkat_nfa q) (netkat_nfa r)
  | q*    => nfa_star (netkat_nfa q)
end.

Theorem netkat_nfa_correct (p : policy) a b v w :
  (| p |) (a,v) (b,w++v) <-> (a~(rev w)~b \in nfa_lang (netkat_nfa p) = true).
Proof.
  split; intro H.
  + dependent induction H; simpl;
    try (symmetry in x; rewrite <- app_nil_l in x; apply app_inv_tail in x; subst w);
    first [rewrite nfa_pred_correct | rewrite nfa_dup_correct | 
           rewrite nfa_union_correct; apply lang_union_correct |
           rewrite nfa_seq_correct; apply lang_conc_correct | idtac];
    steffen; repeat split; eauto 3.
    - destruct h' as [c u']. destruct (bstep_prefix H) as [u H1]. subst u'.
      destruct (bstep_prefix H0) as [u' H1]. rewrite app_assoc in H1.
      assert (w=u'++u) by eauto using app_inv_tail. subst w. clear H1.
      rewrite rev_app_distr. exists (a~(rev u)~c); exists (c~(rev u')~b).
      simpl. rewrite <- app_assoc in IHbstep2. split_if; intuition eauto 2.
    - (* star case 1 *) admit.
    - (* star case 2 *) admit.
    - replace w with [b]. intuition.
      apply app_inv_tail with (l:=v). auto.
  + gd a; gd b; gd v; gd w; induction p; intros; simpl in *;
    first [rewrite nfa_pred_correct in H | rewrite nfa_dup_correct in H | 
           rewrite nfa_union_correct in H; apply lang_union_correct in H |
           rewrite nfa_seq_correct in H; apply lang_conc_correct in H | idtac];
    steffen; intuition;
    try (assert (w=[]) by auto using rev_eq_nil; subst; simpl; eauto).
    - destruct s1 as [a' v' c]; destruct s2 as [c' u' b'].
      unfold gs_conc in H. split_if; invert H.
      assert (w = rev(v'++u')) by (rewrite <- H4; auto using rev_involutive). subst w.
      rewrite <- (rev_involutive v') in H0. 
      rewrite <- (rev_involutive u') in H1.
      rewrite rev_app_distr. rewrite <- app_assoc.
      econstructor; eauto.
    - (* star case *) admit.
    - subst b. assert (w=[a]) by auto using rev_eq_singleton; subst w.
      simpl; eauto.
Qed.

End Automata.
