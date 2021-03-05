Require Import Monads.Monad.
Require Import Monads.State.
Require Import Lia.

Declare Scope hoare_scope.
Delimit Scope hoare_scope with hoare.
Open Scope hoare_scope.

Definition Pred {State: Type} := State -> Prop. 
Definition top {State: Type} : @Pred State := fun _ => True.
Hint Unfold top : core.

(* TODO: I think we can make this total by changing Q to take (Result + Exception) as second argument *)
Definition hoare_triple_partial
    {State Exception Result: Type}
    {P: @Pred State}
    {c: @state_monad State Exception Result}
    {Q: Result -> State -> @Pred State} : Prop := 
  forall st, P st -> 
    match c st with 
    | (inr _, _)    => True
    | (inl v, st')  => Q v st st'
    end.

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

Lemma hoare_consequence {State Exception Result: Type} :
  forall (P P': @Pred State) (Q Q': Result -> State -> @Pred State) (c: @state_monad State Exception Result),
  (forall i, P' i -> P i) ->
  (forall v i f, Q v i f -> Q' v i f) ->
  {{ P }} c {{ Q }} ->
  {{ P' }} c {{ Q' }}.
Proof.
  intros.
  unfold hoare_triple_partial in *.
  intros.
  specialize (H1 st).
  specialize (H st).
  specialize (H H2).
  specialize (H1 H).
  destruct (c st).
  destruct s.
    -   
      specialize (H0 r st s0).
      auto.
    - auto.
Qed.

Lemma hoare_return {State Exception Result: Type} (x: Result) : 
  {{ top }} @state_return State Exception Result x {{ fun r st st' => r = x /\ st = st' }}.
Proof.
  cbv. intros. auto.
Qed.

Lemma hoare_fail {State Exception Result: Type} : 
  forall (P: @Pred State) (Q: Result -> State -> @Pred State) (exc: Exception), {{ P }} state_fail exc {{ Q }}.
Proof.
  cbv. intros. auto.
Qed.

Lemma hoare_get {State Exception: Type} :
  {{ top }} @get_state State Exception {{ fun r s s' => s = s' /\ r = s }}.
Proof.
  cbv. intros. auto.
Qed.

Lemma hoare_put {State Exception: Type} :
  forall f, {{ top }} @put_state State Exception f {{ fun _ s s' => s' = f s}}.
Proof.
  cbv. intros. auto.
Qed.

Lemma hoare_bind
  {State A B Exception: Type}
  {P: @Pred State}
  {P': A -> @Pred State}
  {Q: A -> State -> @Pred State}
  {Q': A -> B -> State -> @Pred State}
  {c: @state_monad State Exception A}
  {f: A -> @state_monad State Exception B}
  :
  {{ P }} c {{ Q }} ->
  (forall r: A, {{ P' r }} (f r) {{ Q' r}}) ->
  {{ fun st_init => P st_init /\ forall (r: A) (st: State), Q r st_init st -> P' r st}}
  c >>= f
  {{ fun r st_init st_final => exists a st_middle, Q a st_init st_middle /\ Q' a r st_middle st_final }}.
Proof.
  cbv.
  intros.
  specialize (H st).
  induction (c st).
  induction a.
  specialize (H0 a b).
  destruct H1 as [H1 H2].
  specialize (H2 a b).
  induction (f a b).
  induction a0.
  -
    exists a.
    exists b.
    auto.
  - auto.
  - auto.
Qed.
