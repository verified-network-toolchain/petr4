Require Import Monads.Monad.
Require Import Monads.State.
Require Import Lia.

Require Import Coq.Init.Nat.

Declare Scope hoare_scope_wp.
Delimit Scope hoare_scope_wp with hoare_wp.
Open Scope hoare_scope_wp.

Definition Pred (State: Type) := State -> Prop. 
(* These postconditions are unary; they relate a value and the final state. 
 * To connect the final state to the initial state we will wrap the triple in a 
 * binder, e.g. 
 * forall n, {{ fun s => s = n }} increment {{ fun _ s' => s' = n + 1 }}
 *)
Definition Post (State: Type) (Value: Type) := Value -> Pred State. 
Definition top {State: Type} : Pred State := fun _ => True.
Hint Unfold top : core.

Definition hoare_triple_wp
    {State Exception Result: Type}
    {P: Pred State}
    {c: @state_monad State Exception Result}
    {Q: Post State (Result + Exception)} : Prop := 
  forall st, P st -> 
    let (v, st') := c st in
      Q v st'
    .

Notation "{{ P }} c {{ Q }}" := (@hoare_triple_wp _ _ _ P c Q) (at level 90) : hoare_scope_wp.
Ltac mysimp := 
    unfold Pred, Post, hoare_triple_wp, state_return, state_bind, get_state, put_state in * ; intros ; 
      repeat (match goal with
                | [ H : _ /\ _ |- _] => destruct H
                | [ H : (_ * _)%type |- _] => destruct H
                | [ H : (_ + _)%type |- _] => destruct H
                | [ H1 : forall _, ?P1 _ -> _, H2 : ?P1 ?h |- _] => 
                  generalize (H1 h H2) ; clear H1 ; intros
                | [ H1 : forall _ _ _, ?P1 _ _ -> _, H2 : ?P1 ?x ?h |- _] => 
                  generalize (H1 _ _ _ H2) ; clear H1 ; intros
                | [ H : match ?e with | Some _ => _ | None => _ end |- _ ] => 
                  destruct e
                | [ |- _ /\ _ ] => split
                | [ H : exists _, _ |- _] => destruct H
                | [ H : Some ?x = Some ?y |- _ ] => inversion H ; clear H ; subst
                | [ H : inl ?x = inl ?y |- _ ] => inversion H ; clear H ; subst
                | [ H : inr ?x = inr ?y |- _ ] => inversion H ; clear H ; subst
                | _ => assert False ; [ lia | contradiction ]
              end) ; subst ; simpl in * ; try firstorder ; auto with arith.

Lemma weaken_pre 
  {State Exception Result:Type} 
  {P1: Pred State} 
  {c: @state_monad State Exception Result}
  {Q : Post State (Result + Exception)} :
  {{ P1 }} c {{ Q }} ->
  forall (P2: Pred State), (forall h, P2 h -> P1 h) ->
  {{ P2 }} c {{ Q }}.
Proof.
  mysimp.
Qed.
(* Lemma hoare_consequence {State Exception Result: Type} {c: @state_monad State Exception Result}:
  forall {P P': @Pred State} {Q Q': Result + Exception -> State -> @Pred State},
  {{ P }} c {{ Q }} ->
  (forall i, P' i -> P i) ->
  (forall v i f, Q v i f -> Q' v i f) ->
  {{ P' }} c {{ Q' }}.
Proof.
  intros.
  unfold hoare_triple_partial in *.
  intros.
  specialize (H0 st).
  specialize (H st).
  specialize (H0 H2).
  specialize (H H0).
  destruct (c st).
  specialize (H1 s st s0).
  auto.
Qed. *)

Lemma return_wp {State Exception Result: Type} {Q: Post State (Result + Exception)} (x: Result) : 
  {{ Q (inl x) }} 
    @state_return State Exception Result x 
  {{ Q }}.
Proof.
  mysimp.
Qed.

Lemma fail_wp {State Exception Result: Type} {Q: Post State (Result + Exception)} (e: Exception) : 
  {{ Q (inr e) }} 
    @state_fail State Exception Result e 
  {{ Q }}.
Proof.
  mysimp.
Qed.


Lemma get_wp {State Exception: Type} {Q: Post State (State + Exception)} :
  {{ fun s => Q (inl s) s }} @get_state State Exception {{ Q }}.
Proof.
  mysimp.
Qed.

Lemma put_wp {State Exception Result: Type} {Q: Post State (unit + Exception)} f :
  {{ fun s => Q (inl tt) (f s) }} @put_state State Exception f {{ Q }}.
Proof.
  mysimp.
Qed.


Lemma bind_wp
  {State A B Exception: Type}
  {P: Pred State}
  {P': Post State (A + Exception)}
  {Q: Post State (B + Exception)}
  {c: @state_monad State Exception A}
  {f: A -> @state_monad State Exception B}
  :
  {{ P }} c {{ P' }} ->
  (forall r: A, {{ P' (inl r) }} (f r) {{ Q }}) ->
  (forall (e: Exception) s, P' (inr e) s -> Q (inr e) s) ->
  {{ P }} c >>= f {{ Q }}.
Proof.
  mysimp.
  cbv.
  destruct (c st).
  destruct s.
  specialize (H0 a s0).
    - 
      destruct (f a s0).
      destruct s.
      mysimp.
      mysimp.
    -
      specialize (H1 e s0).
      mysimp.
Qed.

Lemma cond_pre 
  {State Exception Result: Type} 
  {P Q b} 
  {c1 c2 : @state_monad State Exception Result}: 
  {{ fun s => P s /\ b = true }} c1 {{ Q }} ->
  {{ fun s => P s /\ b = false }} c2 {{ Q }} ->
  {{ P }} if b then c1 else c2 {{ Q }}.
Proof.
  intros.
  destruct b; mysimp.
Qed.

Lemma cond_pre2 
  {State Exception Result: Type} 
  {P1 P2 Q b} 
  {c1 c2 : @state_monad State Exception Result}: 
  {{ fun s => P1 s /\ b = true }} c1 {{ Q }} -> 
  {{ fun s => P2 s /\ b = false }} c2 {{ Q }} ->
  {{ fun s => (b = true -> P1 s) /\ (b = false -> P2 s) }}
    if b then c1 else c2
  {{ Q }}.
Proof.
  intros.
  destruct b; mysimp.
Qed.
