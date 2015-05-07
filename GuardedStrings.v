Require Import List Coq.Program.Equality Bool Omega Recdef.
Import ListNotations.
Require Export NetKAT Sets Misc Classes.

Print Visibility.



Module GS (F : FIELDSPEC) (V : VALUESPEC(F)).
Include NetKAT.NetKAT(F)(V).

(*
Inductive gs := GS : list P.t -> P.t -> P.t -> gs.
Hint Constructors gs. *)

Definition gs := prod (prod P.t P.t) (list P.t).
Notation "a ~ b # w" := (pair (pair a b) w) (at level 0).
Notation "[ a ~ b # w | B ]" := (fun s => let 'a~b#w := s in B)
  (at level 0, a ident, b ident, w ident).

Definition gs_length (gs : gs) :=
 let '_~_#w := gs in length w.

(* guarded strings *)
Definition gs_lang := (pred gs).

Implicit Types (a b c d : P.t) (w : list P.t) (L : gs_lang).

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
  | a~b#[] => nfa_accept q a b
  | a~b#(c::w) =>
  match n with
  | O => false
  | S n => [$ exists q' | nfa_trans q a b q' && accept_n q' b~c#w n ]
  end
end.

Definition accept {A : nfa} (q : A) gs := accept_n q gs (gs_length gs).

Inductive accept_prop {A : nfa} (q : A) : gs -> Prop :=
  | accept_atom : forall a b, nfa_accept q a b = true -> accept_prop q a~b#[]
  | accept_trans : forall a b c w q', nfa_trans q a b q' = true -> accept_prop q' b~c#w -> 
      accept_prop q a~b#(c::w).
Hint Constructors accept_prop.

Ltac invert H := inversion H; subst; clear H.
Ltac gd id := generalize dependent id.

Theorem accept_correct (A : nfa) (q : A) gs : accept_prop q gs <-> accept q gs = true.
Proof.
  destruct gs as [[a b] w].
  split; intro H; gd q; gd a; gd b; induction w; intros;
  unfold accept in *; simpl;  try invert H; auto.
  + apply exists_iff; exists q'.
    apply andb_true_iff. intuition eauto.
  + apply exists_iff in H1. destruct H1 as [x H1].
    apply andb_true_iff in H1; destruct H1 as [H1 H2].
    eauto.
Qed.

Definition nfa_lang (A : nfa) := [$ gs | accept (nfa_s A) gs ].

Definition residual a b L :=
  [ b'~c#w | eqb b b' && a~b#(c::w) \in L ].


Definition star L := fix lstar gs :=
  let 'a~b#w := gs in
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