Require Import Poulet4.Monads.Monad.
Require Import Poulet4.Monads.State.

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
  cbv. intros.
  specialize (H st). 
  destruct H1 as [H1 H2].
  specialize (H H1).
  destruct (c st).
  destruct s.
    - 
      specialize (H0 a s0).
      destruct (f a s0).
      exists s0.
      destruct s.
      -- left.
        exists a.
        split.
        --- trivial.
        ---
          apply H0.
          eapply H2. 
          trivial.
      -- left.
      exists a.
      split.
      --- trivial.
      ---
        apply H0.
        eapply H2. 
        trivial.
    - exists s0.
      right.
      exists e.
      trivial.
Qed.

Notation "x <-- c ;; f" := (hoare_bind c (fun x => f))
  (right associativity, at level 84, c at next level) : hoare_scope.
Notation "c ;;; f" := (hoare_bind c (fun _ => f)) (right associativity, at level 84) : hoare_scope.

Lemma hoare_cond 
  {State Exception Result : Type} 
  {c1 c2: @state_monad State Exception Result}
  {P: @Pred State}
  {Q1 Q2 b}: 
  {{ fun st => P st /\ b = true }} c1 {{ Q1 }} ->
  {{ fun st => P st /\ b = false }} c2 {{ Q2 }} -> 
  {{ P }} if b then c1 else c2 {{ fun r s st => Q1 r s st \/ Q2 r s st}}.
Proof.
  cbv. intros.
  destruct b.
  - specialize (H st).
    assert (P st /\ true = true).
    split; trivial.
    specialize (H H2).
    destruct (c1 st).
    left. trivial.
  - specialize (H0 st).
    assert (P st /\ false = false).
    split; trivial.
    specialize (H0 H2).
    destruct (c2 st).
    right. trivial.
Qed.

Lemma hoare_return' {State Exception Result: Type} {P} (x: Result) : 
  {{ P }} @state_return State Exception Result x {{ fun r st st' => P st' /\ r = inl x /\ st = st' }}.
Proof.
  cbv. intros. auto.
Qed.
