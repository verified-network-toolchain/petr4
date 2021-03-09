Require Import Monads.Monad.
Require Import Monads.State.
Require Import Lia.

Require Import Coq.Init.Nat.

Declare Scope hoare_scope.
Delimit Scope hoare_scope with hoare.
Open Scope hoare_scope.

Definition Pred {State: Type} := State -> Prop. 
Definition top {State: Type} : @Pred State := fun _ => True.
Hint Unfold top : core.

Definition hoare_triple_partial
    {State Exception Result: Type}
    {P: @Pred State}
    {c: @state_monad State Exception Result}
    {Q: Result + Exception -> State -> @Pred State} : Prop := 
  forall st, P st -> 
    let (v, st') := c st in
      Q v st st'
    .

Notation "{{ P }} c {{ Q }}" := (@hoare_triple_partial _ _ _ P c Q) (at level 90) : hoare_scope.
Ltac gregsimp := 
    unfold Pred, hoare_triple_partial, top in * ; intros ; 
      repeat (match goal with
                | [ H : _ /\ _ |- _] => destruct H
                | [ H : (_ * _)%type |- _] => destruct H
                | [ H1 : forall _, ?P1 _ -> _, H2 : ?P1 ?h |- _] => 
                  generalize (H1 h H2) ; clear H1 ; intros
                | [ H1 : forall _ _ _, ?P1 _ _ -> _, H2 : ?P1 ?x ?h |- _] => 
                  generalize (H1 _ _ _ H2) ; clear H1 ; intros
                | [ H : match ?e with | Some _ => _ | None => _ end |- _ ] => 
                  destruct e
                | [ |- _ /\ _ ] => split
                | [ H : exists _, _ |- _] => destruct H
                | [ H : Some ?x = Some ?y |- _ ] => inversion H ; clear H ; subst
                | _ => assert False ; [ lia | contradiction ]
              end) ; subst ; simpl in * ; try firstorder ; auto with arith.

Lemma hoare_consequence {State Exception Result: Type} {c: @state_monad State Exception Result}:
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
Qed.

Lemma hoare_return {State Exception Result: Type} (x: Result) : 
  {{ top }} @state_return State Exception Result x {{ fun r st st' => r = inl x /\ st = st' }}.
Proof.
  cbv. intros. auto.
Qed.

Lemma hoare_fail {State Exception Result: Type}  (exc: Exception) : 
  {{ top }} @state_fail State Exception Result exc {{ fun r st st' => r = inr exc /\ st = st' }}.
Proof.
  cbv. intros. auto.
Qed.

Lemma hoare_get {State Exception: Type} :
  {{ top }} @get_state State Exception {{ fun r s s' => s = s' /\ r = inl s }}.
Proof.
  cbv. intros. auto.
Qed.

Lemma hoare_get' {State Exception: Type} {P}:
  {{ fun s => P s }} @get_state State Exception {{ fun r s s' => P s /\ s = s' /\ r = inl s}}.
Proof.
  cbv. intros. auto.
Qed.

Lemma hoare_put {State Exception: Type} :
  forall f, {{ top }} @put_state State Exception f {{ fun _ s s' => s' = f s}}.
Proof.
  cbv. intros. auto.
Qed.

Lemma hoare_put' {State Exception: Type} {P} :
  forall f, {{ fun s => P (f s) }} @put_state State Exception f {{ fun _ s s' => P (f s) /\ s' = f s}}.
Proof.
  cbv. intros. auto.
Qed.


Lemma hoare_bind
  {State A B Exception: Type}
  {P: @Pred State}
  {P': A + Exception -> @Pred State}
  {Q: A + Exception -> State -> @Pred State}
  {Q': A + Exception -> B + Exception -> State -> @Pred State}
  {c: @state_monad State Exception A}
  {f: A -> @state_monad State Exception B}
  :
  {{ P }} c {{ Q }} ->
  (forall r: A, {{ P' (inl r) }} (f r) {{ Q' (inl r)}}) ->
  (forall (e: Exception) (st: State), P' (inr e) st -> Q' (inr e) (inr e) st st) ->
    (* (forall (e: Exception) (st: State), P st -> Q (inr e) st st -> *)
  {{ fun st_init => P st_init /\ forall (r: A + Exception) (st: State), Q r st_init st -> P' r st}}
  c >>= f
  {{ fun r st_init st_final => exists a st_middle, Q a st_init st_middle /\ Q' a r st_middle st_final }}.
Proof.
  cbv.
  intros.
  specialize (H st).
  induction (c st).
  induction a.
  
  2 : {
    destruct H2 as [H2 H3].
    exists (inr b0).
    exists b.
    split.
    - auto.
    -
      specialize (H3 (inr b0) b).
      specialize (H1 b0 b).
      auto.
  }
  specialize (H0 a b).
  destruct H2 as [H2 H3].
  specialize (H3 (inl a) b).
  induction (f a b).
  exists (inl a).
  exists b.
  split.
  - auto.
  - auto.
Qed.

Lemma hoare_bind'
  {State A B Exception: Type}
  {P: @Pred State}
  {P': A -> @Pred State}
  {Q: A + Exception -> State -> @Pred State}
  {Q': A -> B + Exception -> State -> @Pred State}
  {c: @state_monad State Exception A}
  {f: A -> @state_monad State Exception B}
  :
  {{ P }} c {{ Q }} ->
  (forall r: A, {{ P' r }} (f r) {{ Q' r }}) ->
  {{ 
    fun st_init => 
      P st_init /\ 
      forall (r: A) (st: State), 
        Q (inl r) st_init st -> P' r st
  }}
  c >>= f
  {{ 
    fun r st_init st_final => 
      exists st_middle, 
      (exists a, Q (inl a) st_init st_middle /\ Q' a r st_middle st_final) \/
      (exists e, Q (inr e) st_init st_middle)
  }}.
Proof.
Admitted.


Notation "x <-- c ; f" := (hoare_bind c (fun x => f) _)
  (right associativity, at level 84, c at next level) : hoare_scope.
Notation "x <-- c ;; f" := (hoare_bind' c (fun x => f))
  (right associativity, at level 84, c at next level) : hoare_scope.
Notation "c ;;; f" := (hoare_bind c (fun _ => f)) (right associativity, at level 84) : hoare_scope.
