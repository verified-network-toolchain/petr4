Require Import Poulet4.Monads.Monad.
Require Import Poulet4.Monads.State.

Require Import Lia.

Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.

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
Definition bot {State: Type} : Pred State := fun _ => False.

Hint Unfold top : core.
Hint Unfold bot: core.


Definition hoare_total_wp
  {State Exception Result: Type}
  {P: Pred State}
  {c: @state_monad State Exception Result}
  {Q: Post State (Result + Exception)}
    : Prop := 
  forall st, P st -> 
  let (v, st') := c st in
    Q v st'.

Notation "{{ P }} c {{ Q }}" := (@hoare_total_wp _ _ _ P c Q) 
  ( at level 90,
    format "'{{'  P  '}}'  '[  ' c ']'  '{{'  Q  '}}'"
  ) : hoare_scope_wp.

Definition hoare_partial_wp
  {State Exception Result: Type}
  {P: Pred State}
  {c: @state_monad State Exception Result}
  {Q: Post State Result}
    : Prop := 
  forall st, P st -> 
  let (v, st') := c st in
  match v with 
  | inl r => Q r st'
  | inr _ => False
  end.

Notation "<< P >> c << Q >>" := (@hoare_partial_wp _ _ _ P c Q) 
  ( at level 90,
    format "'[hv  ' '<<'  P  '>>' ']'  '[hv  ' c ']'  '[hv  ' '<<'  Q  '>>' ']'"
  ) : hoare_scope_wp.


Ltac mysimp := 
  unfold Pred, Post, hoare_total_wp, hoare_partial_wp, state_return, state_bind, get_state, put_state in * ; intros ; 
  repeat (
    match goal with
    | [ H : ?P |- ?P ] => exact H
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


Lemma strengthen_pre_t
  {State Exception Result:Type} 
  {P1: Pred State} 
  {P2: Pred State}
  {c: @state_monad State Exception Result}
  {Q : Post State (Result + Exception)} 
  :
  {{ P1 }} c {{ Q }} ->
  (forall h, P2 h -> P1 h) ->
  {{ P2 }} c {{ Q }}.
Proof.
  mysimp.
Qed.

Lemma strengthen_pre_p
  {State Exception Result:Type} 
  {P1: Pred State} 
  {P2: Pred State}
  {c: @state_monad State Exception Result}
  {Q : Post State Result} 
  :
  << P1 >> c << Q >> ->
  (forall h, P2 h -> P1 h) ->
  << P2 >> c << Q >>.
Proof.
  mysimp.
Qed.

Lemma return_wp_t {State Exception Result: Type} 
  {Q: Post State (Result + Exception)} 
  (x: Result) : 
  {{ Q (inl x) }} 
    @state_return State Exception Result x 
  {{ Q }}.
Proof.
  mysimp.
Qed.

Lemma return_wp_p {State Exception Result: Type} 
  {Q: Post State Result} 
  (x: Result) : 
  << Q x >> 
    @state_return State Exception Result x 
  << Q >>.
Proof.
  mysimp.
Qed.


Lemma fail_wp_t {State Exception Result: Type} 
  {Q: Post State (Result + Exception)}
  (e: Exception) : 
  {{ Q (inr e)}} 
    @state_fail State Exception Result e 
  {{ Q }}.
Proof.
  mysimp.
Qed.

Lemma fail_wp_p {State Exception Result: Type} 
  {Q: Post State Result}
  (e: Exception) : 
  << bot >> 
    @state_fail State Exception Result e 
  << Q >>.
Proof.
  mysimp.
Qed.

Lemma get_wp_t {State Exception: Type} 
  {Q: Post State (State + Exception)}
  :
  {{ fun s => Q (inl s) s }} 
    @get_state State Exception 
  {{ Q }}.
Proof.
  mysimp.
Qed.

Lemma get_wp_p {State Exception: Type} 
  {Q: Post State State }
  :
  << fun s => Q s s >> 
    @get_state State Exception 
  << Q >>.
Proof.
  mysimp.
Qed.

Lemma put_wp_t {State Exception: Type} 
  {Q: Post State (unit + Exception)}  
  f :
  {{ fun s => Q (inl tt) (f s) }} 
    @put_state State Exception f 
  {{ Q }}.
Proof.
  mysimp.
Qed.

Lemma put_wp_p {State Exception: Type} 
  {Q: Post State unit}  
  f :
  << fun s => Q tt (f s) >> 
    @put_state State Exception f 
  << Q >>.
Proof.
  mysimp.
Qed.

Lemma bind_wp_t
  {State A B Exception: Type}
  {P: Pred State}
  {Pa: A -> Pred State}
  {Pe: Exception -> Pred State}
  {Q: Post State (B + Exception)}
  {c: @state_monad State Exception A}
  {f: A -> @state_monad State Exception B}
  :
  {{ P }} c {{ fun r s => 
    match r with 
    | inl a => Pa a s
    | inr e => Pe e s 
    end
    }} ->
  (forall r: A, {{ Pa r }} (f r) {{ Q }}) -> 
  (forall (e: Exception) (st: State), Pe e st -> Q (inr e) st) ->
  {{ P }} c >>= f {{ Q }}.
Proof.
  intros.
  mysimp.
  mysimp.
  destruct (c st).
  destruct s.
    - eapply H0.  
      trivial.
    - eapply H1.
      trivial.
Qed.

Lemma bind_wp_p
  {State A B Exception: Type}
  {P: Pred State}
  {P': Post State A}
  {Q: Post State B}
  {c: @state_monad State Exception A}
  {f: A -> @state_monad State Exception B}
  :
  << P >> c << P' >> ->
  (forall r: A, << P' r >> (f r) << Q >>) -> 
  << P >> c >>= f << Q >>.
Proof.
  intros.
  mysimp.
  mysimp.
  destruct (c st).
  destruct s.
    - eapply H0.  
      trivial.
    - trivial.
Qed.

Lemma cond_wp_t
  {State Exception Result: Type} 
  {P1 P2 Q} 
  {c1 c2 : @state_monad State Exception Result} b: 
  (b = true -> {{ P1 }} c1 {{ Q }}) ->
  (b = false -> {{ P2 }} c2 {{ Q }}) ->
  {{ fun s => if b then P1 s else P2 s }} 
    if b then c1 else c2 
  {{ Q }}.
Proof.
  intros.
  destruct b; mysimp.
Qed.

Lemma cond_wp_p
  {State Exception Result: Type} 
  {P1 P2 Q} 
  {c1 c2 : @state_monad State Exception Result}
  b: 
  (b = true -> << P1 >> c1 << Q >>) ->
  (b = false -> << P2 >> c2 << Q >>) ->
  << fun s => if b then P1 s else P2 s >> 
    if b then c1 else c2 
  << Q >>.
Proof.
  intros.
  destruct b; mysimp.
Qed.

Lemma case_nat_wp_t
  {State Exception Result: Type} 
  {P1 P2 Q c1} 
  {c2: nat -> @state_monad State Exception Result} n : 
  (n = 0 -> {{ fun s => P1 s }} c1 {{ Q }}) ->
  (forall n', n = S n' -> 
    {{ fun s => P2 n' s }} 
      c2 n'
    {{ Q }}) ->
  {{ 
    match n with 
    | 0 => P1
    | S n' => P2 n' 
    end
  }}
    match n with 
    | 0 => c1 
    | S n' => c2 n'
    end
  {{
    Q
  }}.
Proof.
  destruct n; mysimp.
Qed.

Lemma case_nat_wp_p
  {State Exception Result: Type} 
  {P1 P2 Q c1} 
  {c2: nat -> @state_monad State Exception Result} n : 
  (n = 0 -> << fun s => P1 s >> c1 << Q >>) ->
  (forall n', n = S n' -> 
    << fun s => P2 n' s >> 
      c2 n'
    << Q >>) ->
  << 
    match n with 
    | 0 => P1
    | S n' => P2 n' 
    end
  >>
    match n with 
    | 0 => c1 
    | S n' => c2 n'
    end
  <<
    Q
  >>.
Proof.
  destruct n; mysimp.
Qed.

Lemma case_list_wp_t
  {State Exception Result A: Type} 
  {P1 P2 Q c1} 
  {c2: A -> list A -> @state_monad State Exception Result} xs :
  (xs = nil -> {{ fun s => P1 s }} c1 {{ Q }}) ->
  (forall x xs', xs = x :: xs' -> 
    {{ fun s => P2 x xs' s }} 
      (c2 x xs') 
    {{ Q }}
  ) ->
  {{ 
    match xs with 
    | nil => P1
    | x :: xs' => P2 x xs' 
    end
  }}
    match xs with 
    | nil => c1 
    | x :: xs' => c2 x xs'
    end
  {{
    Q
  }}.
Proof.
  destruct xs; mysimp.
Qed.

Lemma case_list_wp_p
  {State Exception Result A: Type} 
  {P1 P2 Q c1} 
  {c2: A -> list A -> @state_monad State Exception Result} 
  xs :
  (xs = nil -> << fun s => P1 s >> c1 << Q >>) ->
  (forall x xs', xs = x :: xs' -> 
    << fun s => P2 x xs' s >> 
      (c2 x xs') 
    << Q >>
  ) ->
  << 
    match xs with 
    | nil => P1
    | x :: xs' => P2 x xs' 
    end
  >>
    match xs with 
    | nil => c1 
    | x :: xs' => c2 x xs'
    end
  <<
    Q
  >>.
Proof.
  destruct xs; mysimp.
Qed.

Lemma case_sum_wp_t
  {State Exception Result A B: Type} 
  {P1 P2 Q}
  {c1: A -> @state_monad State Exception Result} 
  {c2: B -> @state_monad State Exception Result} x : 
  (forall a, x = inl a -> {{ fun s => P1 a s }} c1 a {{ Q }} ) -> 
  (forall b, x = inr b -> {{ fun s => P2 b s }} c2 b {{ Q }} ) ->
  {{ 
    match x with 
    | inl a => P1 a
    | inr b => P2 b
    end
  }}
    match x with 
    | inl a => c1 a
    | inr b => c2 b
    end
  {{
    Q
  }}.
Proof.
  destruct x; mysimp.
Qed.

Lemma case_sum_wp_p
  {State Exception Result A B: Type} 
  {P1 P2 Q}
  {c1: A -> @state_monad State Exception Result} 
  {c2: B -> @state_monad State Exception Result} x : 
  (forall a, x = inl a -> << fun s => P1 a s >> c1 a << Q >> ) -> 
  (forall b, x = inr b -> << fun s => P2 b s >> c2 b << Q >> ) ->
  << 
    match x with 
    | inl a => P1 a
    | inr b => P2 b
    end
  >>
    match x with 
    | inl a => c1 a
    | inr b => c2 b
    end
  <<
    Q
  >>.
Proof.
  destruct x; mysimp.
Qed.

Lemma case_option_wp_t
  {State Exception Result A: Type} 
  {P1 P2 Q c1} 
  {c2: A -> @state_monad State Exception Result} x : 
  (x = None -> {{ fun s => P1 s }} c1 {{ Q }}) ->
  (forall x', x = Some x' -> {{ fun s => P2 x' s }} c2 x' {{ Q }}) ->
  {{ 
    match x with 
    | None => P1
    | Some x' => P2 x' 
    end
  }}
    match x with 
    | None => c1
    | Some x' => c2 x'
    end
  {{
    Q
  }}.
Proof.
  destruct x; mysimp.
Qed.

Lemma case_option_wp_p
  {State Exception Result A: Type} 
  {P1 P2 Q c1} 
  {c2: A -> @state_monad State Exception Result} x : 
  (x = None -> << fun s => P1 s >> c1 << Q >>) ->
  (forall x', x = Some x' -> << fun s => P2 x' s >> c2 x' << Q >>) ->
  << 
    match x with 
    | None => P1
    | Some x' => P2 x' 
    end
  >>
    match x with 
    | None => c1
    | Some x' => c2 x'
    end
  <<
    Q
  >>.
Proof.
  destruct x; mysimp.
Qed.

Lemma hoare_consequence_t
  {State Exception Result:Type} 
  {P1: Pred State} 
  {P2: Pred State}
  {Q1: Post State (Result + Exception)}
  {Q2: Post State (Result + Exception)}
  {c: @state_monad State Exception Result}
  :
  {{ P1 }} c {{ Q1 }} ->
  (forall h, P2 h -> P1 h) ->
  (forall v h, Q1 v h -> Q2 v h) ->
  {{ P2 }} c {{ Q2 }}.
Proof.
  mysimp.
  destruct (c st).
  mysimp.
Qed.

Lemma hoare_consequence_p
  {State Exception Result:Type} 
  {P1: Pred State} 
  {P2: Pred State}
  {Q1: Post State Result}
  {Q2: Post State Result}
  {c: @state_monad State Exception Result}
  :
  << P1 >> c << Q1 >> ->
  (forall h, P2 h -> P1 h) ->
  (forall v h, Q1 v h -> Q2 v h) ->
  << P2 >> c << Q2 >>.
Proof.
  mysimp.
  destruct (c st).
  mysimp.
Qed.

Lemma weaken_post_t
  {State Exception Result:Type} 
  {P: Pred State} 
  {Q1: Post State (Result + Exception)}
  {Q2: Post State (Result + Exception)}
  {c: @state_monad State Exception Result} :
  {{ P }} c {{ Q1 }} -> 
  (forall v s, Q1 v s -> Q2 v s) ->
  {{ P }} c {{ Q2 }}.
Proof.
  intros.
  apply (hoare_consequence_t H).
  mysimp.
  intros.
  apply H0; trivial.
Qed.

Lemma weaken_post_p
  {State Exception Result:Type} 
  {P: Pred State} 
  {Q1: Post State Result}
  {Q2: Post State Result}
  {c: @state_monad State Exception Result} :
  << P >> c << Q1 >> -> 
  (forall v s, Q1 v s -> Q2 v s) ->
  << P >> c << Q2 >>.
Proof.
  intros.
  apply (hoare_consequence_p H).
  mysimp.
  intros.
  apply H0; trivial.
Qed.

Ltac wp :=
  match goal with
  | [ |- {{ _ }} mbind _ _ {{ _ }} ] => eapply bind_wp_t
  | [ |- {{ _ }} get_state {{ _ }} ] => eapply get_wp_t
  | [ |- {{ _ }} put_state ?e {{ _ }} ] => eapply (put_wp_t e)
  | [ |- {{ _ }} state_fail ?e {{ _ }} ] => eapply (fail_wp_t e)
  | [ |- {{ _ }} state_return ?e {{ _ }} ] => eapply (return_wp_t e)
  | [ |- {{ _ }} if _ then _ else _ {{ _ }} ] => eapply cond_wp_t
  | [ |- {{ _ }} match ?e with | 0 => _ | S _ => _ end {{ _ }} ] => eapply (case_nat_wp_t e)
  | [ |- {{ _ }} match ?e with | nil => _ | _ :: _ => _ end {{ _ }} ] => eapply (case_list_wp_t e)
  | [ |- {{ _ }} match ?e with | Some _ => _ | None => _ end {{ _ }} ] => eapply (case_option_wp_t e)
  | [ |- {{ _ }} match ?e with | inl _ => _ | inr _ => _ end {{ _ }} ] => eapply (case_sum_wp_t e)
  | [ |- << _ >> mbind _ _ << _ >> ] => eapply bind_wp_p
  | [ |- << _ >> get_state << _ >> ] => eapply get_wp_p
  | [ |- << _ >> put_state ?e << _ >> ] => eapply (put_wp_p e)
  | [ |- << _ >> state_fail ?e << _ >> ] => eapply (fail_wp_p e)
  | [ |- << _ >> state_return ?e << _ >> ] => eapply (return_wp_p e)
  | [ |- << _ >> if _ then _ else _ << _ >> ] => eapply cond_wp_p
  | [ |- << _ >> match ?e with | 0 => _ | S _ => _ end << _ >> ] => eapply (case_nat_wp_p e)
  | [ |- << _ >> match ?e with | nil => _ | _ :: _ => _ end << _ >> ] => eapply (case_list_wp_p e)
  | [ |- << _ >> match ?e with | Some _ => _ | None => _ end << _ >> ] => eapply (case_option_wp_p e)
  | [ |- << _ >> match ?e with | inl _ => _ | inr _ => _ end << _ >> ] => eapply (case_sum_wp_p e)
  end.


Definition Norm {A State Exception} (f: A -> State -> Prop) : Post State (A + Exception) := fun r s => 
  match r with 
  | inl v => f v s
  | inr _ => False
end.

Lemma lift_partial {State Exception Result: Type}:
  forall (P: Pred State) (c: @state_monad State Exception Result) (Q: Post State Result),
  << P >> c << Q >> ->
  {{ P }} c {{ Norm Q }}.
Proof.
  mysimp.
Qed.

(* It turns out that hoare triples over a monad form a monad as well! Using this insight,
   we can automate much of the intermediate plumbing for partial correctness proofs. 
   The notation below allows for building such proofs; see examples/Hoare.v for usage.

   Alas, the dual postconditions for total correctness seem to preclude similar plumbing
   for total correctness proofs. 
 *)
Notation "x <-- c ; f" := (bind_wp_p c (fun x => f))
  (right associativity, at level 84, c at next level) : hoare_scope_wp.
Notation "c ;;; f" := (bind_wp_p c (fun _:unit => f))
  (right associativity, at level 84) : hoare_scope_wp.

(* Build a weakest-precondition spec from a direct-style spec *)
Definition build_wp 
  {State Exception Result: Type}
  (c: @state_monad State Exception Result) 
  (pre: Pred State)
  (Q: Post State Result)
  (T: State -> (Result * State))
  := 
  << fun s => pre s /\ let (r, s') := T s in Q r s' >>
    c
  << Q >>.

Lemma build_wp_corr 
  {State Exception Result: Type} 
  {c: @state_monad State Exception Result}
  {P}
  {T: State -> (Result * State)}:
  (forall s, 
    << fun s' => s = s' /\ P s' >> 
      c 
    << fun r s' => let (r', s'') := T s in r' = r /\ s'' = s' >>) ->
  forall Q, build_wp c P Q T. 
Proof.
  intros.
  unfold build_wp, hoare_partial_wp in *.
  intros.
  destruct H0.
  specialize (H st st).
  assert (st = st /\ P st).
  split; trivial.
  specialize (H H2).
  destruct (c st).
  destruct s.
  - destruct (T st).
    destruct H.
    rewrite <- H3. rewrite <- H. trivial.
  - contradiction.
Qed.

(* script for inlining obligations generated by wp of the form 
  H1 -> H2 -> ... ?H -> ... -> ?Goal,
  which solves by applying ?H to the goal
*)
Ltac app_ex := 
  intros; repeat match goal with 
  | [ H : _ |- _ ] => exact H 
  | [ H : (_ /\ _)%type |- _] => destruct H
  | [ H : (exists _, _)%type |- _] => destruct H
  end.

Ltac wp_trans :=
  repeat (intros; wp).