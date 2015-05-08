Require Import List Coq.Program.Equality Bool Omega FunctionalExtensionality.
Import ListNotations.
Require Export NetKAT Sets Misc Classes.


Ltac invert H := inversion H; subst; clear H.
Ltac gd id := generalize dependent id.



Module GS (F : FIELDSPEC) (V : VALUESPEC(F)).
Include NetKAT.NetKAT(F)(V).

(* For now, assume that the set of packets is finite as an axiom.
   This will follow automatically once we show that
   Finite X -> Finite Y -> Finite (X->Y).                        *)
Axiom P_finite : Finite P.t.
Global Instance : Finite P.t := P_finite.






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

Check existsb.

Definition gs_lang_conc L1 L2 := [$ s : gs | [$ exists a | 
  existsb (fun n => take n s a \in L1 && drop n a s \in L2) (seq 0 (gs_length s)) ] ].

Theorem lang_conc_correct L1 L2 s :
  (exists s1 s2, (Some s = gs_conc s1 s2) /\ (s1 \in L1 = true) /\ (s2 \in L2 = true))
  <-> (s \in gs_lang_conc L1 L2 = true).
Proof.
  split; intro H.
  + destruct H as [s1 [s2 [H0 [H1 H2]]]].
    destruct s1 as [a w b]; destruct s2 as [b' v c].
    simpl in H0. destruct (b =d= b'); invert H0.
    simpl.






(** End languages over guarded strings ########################*)











(** NFAs **)

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

(** primitive automata **)

Definition nfa_empty :=
  {| nfa_s := tt; nfa_accept q a b := false; nfa_trans q a b q' := false |}.

Definition nfa_singleton a b :=
  {| nfa_s := tt; nfa_trans q a b q' := false;
     nfa_accept q a' b' := if a =d= a' then (if b =d= b' then true else false)
                           else false
  |}.

Lemma nfa_empty_correct : nfa_lang nfa_empty = pred0.
Proof.
  extensionality s.
  unfold nfa_lang.
  unfold accept; destruct s as [a [ |b w] c]; simpl; reflexivity.
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



(** Section nfa_union **)
  
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
  nfa_lang (nfa_union A B) = [$ w | w \in nfa_lang A || w \in nfa_lang B ].
Proof.
  unfold nfa_lang.
  apply pred_eq_intro.
  intro gs. rewrite orb_true_iff. repeat rewrite <- accept_correct.
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

(** End nfa_union **)


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

Lemma seq_correct A1 A2 q gs :

Lemma seq_inl A1 A2 q gs : reflect
  (exists w1 w2, [/\ w = w1 ++ w2 , nfa_accept A1 x w1 & w2 \in nfa_lang A2])
  (nfa_accept (nfa_conc A1 A2) (inl x) w).

End nfa_seq.




Definition residual a b L :=
  [ b'~c)~w | eqb b b' && a~b)~(c::w) \in L ].




Definition star L := fix lstar gs :=
  let 'a~b)~w := gs in
  match w with
  | [] -> true
  | c::w -> \in residual a b 



Definition gs := prod (prod P.t P.t) (list P.t).

(* language of guarded strings *)

Definition gs_lang := pred gs.

Definition e_lang : gs_lang := @empty gs.
Definition id_lang : gs_lang := fun gs => 
  let (gs',_) := gs in
  let (pk,pk') := gs in
  pk=pk'.

(* finite union *)
(* decidable set: X -> bool *)


End GS.