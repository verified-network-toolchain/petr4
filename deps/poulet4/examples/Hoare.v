Require Import Poulet4.Monads.Monad.
Require Import Poulet4.Monads.State.
Require Import Poulet4.Monads.Hoare.WP.
Require Import Lia.

Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.

(* Using the WP hoare calculus, we can reason about output states and results for monadic programs.
   
  To reason about programs that might fail under a precondition P, we must use a total hoare calculus, notated by: 
    {{ P }} potentially_failing_program {{ Q }}.
    For such programs Q must handle both the normal and error cases, and so is a function 
    (Result + Exception) -> State -> Prop.

  While this total calculus is expressive, it's convenient to restrict the scope to
  partial triples, in which the program will never fail under a precondition P.
  For this we notate a partial hoare triple as 
  << P >> always_successful_program << Q >>.

  A benefit of partial triples is that we can use the monadic properties of the specification calculus
  to automate proofs. See the bottom of this file for examples.
*)

(* Consider a silly program with a single nat as state, that increments the nat and
 * immediately fails. We can prove that this program A) always fails and B) increments the state.
 *)
Example fail_incr n:
  {{ fun s => s = n }}
    @put_state nat unit (fun x => x + 1) ;; @state_fail nat unit nat tt
  {{ fun ve s => 
    match ve with 
    | inl _ => False (* property A), the program always fails *)
    | inr _ => s = n + 1 (* property B), the final state is one larger than the initial state *)
    end
  }}.
Proof.
  wp.
  all: swap 2 1. 
  intros.
  eapply strengthen_pre_t.
  wp.
  intros.
  simpl.
  apply H.
  all: swap 2 1.
  intros.
  apply H.
  
  eapply strengthen_pre_t.
  wp.
  mysimp.
Qed.

(* Similarly, consider a program that checks a condition and fails if the condition is true.
   We can prove that this program will always fail if the condition is true.
*)
Example cond_fail b:
  {{ fun s => s = b /\ b = true }}
    if b then state_fail tt else state_return true
  {{ fun r s => r = inr tt }}.
Proof.
  eapply strengthen_pre_t.
  repeat wp.
  mysimp.
Qed.

(* Another interesting program is one that can either succeed or fail, and on failure cases,
 * always sets the state to 0. We can prove that either it succeeded or the state is always 0.
 *)
Definition either_or (n: nat): @state_monad nat unit bool := 
  match n with 
  | 0 => state_return true
  | S n' => put_state (fun _ => 0) ;; state_fail tt
  end.

Example eo_pres n:
  {{ top }}
    either_or n
  {{ fun r s => 
    match r with 
    | inl r' => r' = true
    | inr _  => s = 0
    end
  }}.
Proof.
  unfold either_or.
  eapply strengthen_pre_t.
  wp.
  eapply strengthen_pre_t.
  wp.
  intros.
  destruct H as [it _].
  exact it.

  eapply strengthen_pre_t.
  wp.
  all: swap 2 1.
  intros.
  eapply strengthen_pre_t.
  wp.
  intros.
  exact H.
  wp.
  intros.
  simpl.
  exact H.
  intros.
  simpl.
  destruct H as [n' [_ it]].
  exact it.
  mysimp.
  destruct n; mysimp.
Qed.


(* We can also combine the either_or program with a function that reads the state,
 * and prove the same postcondition. We can further leverage the proof of either_or
 * halfway through the proof.
 *)
Definition get_branch : @state_monad nat unit bool := 
  n <- get_state ;; either_or n.

Example branch_splits : 
  {{ top }}
    get_branch
  {{ fun r s => 
    match r with 
    | inl r' => r' = true
    | inr _  => s = 0
    end
   }}.
Proof.
  eapply strengthen_pre_t.
  unfold get_branch.
  wp.
  all: swap 2 1.

  intros.
  apply (eo_pres r). (* reuse a prior proof *)
  wp.
  intros.
  exact H.
  mysimp.
Qed.

(* While our hoare calculi do not have primitives for loops, we can still easily
 * prove properties about left-folds using Coq's induction tactic. 
 * Consider a function that takes an input n and increments a state n times.
 * We can prove that it correctly performs the addition.
 *)

Fixpoint iter_incr (n: nat) : @state_monad nat unit unit :=
  match n with 
  | 0 => skip
  | S n' => iter_incr n' ;; put_state (fun x => x + 1)
  end.

Example iter_incr_t n m:
  {{ fun s => s = n }}
    iter_incr m
  {{ Norm (fun r s' => s' = n + m )}}. (* the function does not error and adds the numbers *)
Proof.
  induction m.
  - unfold iter_incr.
    mysimp.
  - unfold iter_incr. fold iter_incr.
    eapply strengthen_pre_t.
    wp.
    all: swap 2 1.
    intros. 
    wp.
    eapply weaken_post_t.
    apply IHm.
    all: swap 2 1.
    intros.
    exact H.
    mysimp.
    lia.
    mysimp.
Qed.

  
(* While the proofs before were not painful, there is still room for automation.
 * Consider a function that increments the state and then immediatly gets the state.
 * In total correctness, we can prove the returned value is one larger than the  
 * input state using two applications of bind.
 *)

Example get_incr_t n:
  {{ fun s => s = n  }}
    @put_state nat unit (fun x => x + 1) ;; @get_state nat unit
  {{ Norm (fun r s => r = n + 1) }}.
Proof.
  wp.
  all: swap 2 1.
  intros. 
  wp.
  all: swap 2 1.
  intros.
  apply H.
  mysimp.
Qed.

(* Notice that this function never fails, so we can use the partial calculus as well.
 * With the partial calculus we can use the monadic proof combinators and build
 * a proof skeleton using refine and strengthen_pre_p for a substantially shorter proof.
 * C
 *)

Example get_incr_p n:
  << fun s => s = n  >>
    @put_state nat unit (fun x => x + 1) ;; @get_state nat unit
  << fun r s => r = n + 1 >>.
Proof.
  refine (strengthen_pre_p ( 
    @put_wp_p nat unit _ (fun x => x + 1) ;;; @get_wp_p nat unit _
  ) _). 
  (* Notice that Coq filled in the details of bind and so we are left to prove that 
     our specific precondition actually entails the weakest precondition.
     (spoiler: it does, because we gave a logically equivalent precondition ) 
  *)
  mysimp.
Qed.

(* The conditional fail example from before can be similarly automated. *)

Example cond_fail_p b:
  << fun s => s = b /\ b = false >>
    if b then state_fail tt else state_return true
  << fun r s => r = true >>.
Proof.
  refine (strengthen_pre_p ( 
    cond_wp_p (fail_wp_p tt) (return_wp_p true)
  ) _).
  mysimp.
Qed.

(* But what about loops? It's a bit more subtle here, but we can in fact use the same technique. *)

Example iter_incr_n_p n m:
  << fun s => s = n >>
    iter_incr m
  << fun _ s' => s' = n + m >>.
Proof.
  induction m.

  (* The base case is as before. *)
  - unfold iter_incr.
    mysimp.

  (* In the recursive case, the question becomes "what to put as the first triple in the hoare proof?"
   * A natural fit is the inductive hypothesis! It almost works, but the post condition needs
   * to be massaged to align with the weakest-precondition of the final state update.
   * So to do this, we wrap the inductive hypothesis with weaken_post_p.
   *)
  - unfold iter_incr. fold iter_incr.
    refine (strengthen_pre_p (
      weaken_post_p IHm _ ;;; put_wp_p (fun x => x + 1)
    ) _);
    (* viola! and we are left with some trivial math constraints. *)
    lia.
Qed.

Example incr n :
  << fun s => s = n >>
    put_state (Exception := unit) (fun x => x + 1)
  << fun r s' => s' = n + 1 >>.
Proof.
  eapply strengthen_pre_p.
  wp.
  mysimp.
Qed.

Fixpoint iter_repeat {A} (n: nat) (val: A) : @state_monad (list A) unit unit :=
  match n with 
  | 0 => skip
  | S n' => iter_repeat n' val ;; put_state (fun xs => xs ++ (val :: nil)) 
  end.

Lemma iter_repeat_n {A} (n: nat) (val: A) (xs: list A): 
  << fun s => s = xs >>
    iter_repeat n val
  << fun _ s' => length s' = length xs + n >>.
Proof.
  induction n.
  - unfold iter_repeat.
    mysimp.
  - unfold iter_repeat. fold (iter_repeat (A := A)).
    refine (strengthen_pre_p (
      IHn ;;; (strengthen_pre_p (put_wp_p (fun xs => xs ++ (val :: nil))) _)
    ) _).
    + intros. 
      rewrite last_length.
      rewrite H.
      lia.
    + auto.
Qed.

Lemma iter_repeat_post {A} (a: nat) (b: nat) (val: A): 
  << fun s => length s = a >>
    iter_repeat b val
  << fun _ s' => length s' = a + b >>.
Admitted.
 
Example repeat_twice {A} xs a b (val: A):
  << fun s => s = xs >>
    iter_repeat a val ;; 
    iter_repeat b val
  << fun _ s' => length s' = length xs + a + b >>.
Proof.
  refine ( strengthen_pre_p (
    iter_repeat_post _ _ _ ;;;
    iter_repeat_post _ _ _
  ) _ ).
  mysimp.
Qed.
