Require Import Monads.Monad.
Require Import Monads.State.
Require Import Monads.Hoare.WP.
Require Import Lia.

Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.


Definition either_or (n: nat): @state_monad nat unit bool := 
  match n with 
  | 0 => state_return true
  | S n' => put_state (fun _ => 0) ;; state_fail tt
  end.
  
Example get_incr n:
  {{ fun s => s = n  }}
    @put_state nat unit (fun x => x + 1) ;; @get_state nat unit
  {{ Norm (fun r s => r = n + 1) }}.
Proof.
  eapply bind_wp.
  all: swap 2 1.
  intros. 
  eapply get_wp.
  all: swap 2 1.
  intros.
  apply H.
  mysimp.
Qed.


Example fail_incr n:
  {{ fun s => s = n }}
    @put_state nat unit (fun x => x + 1) ;; @state_fail nat unit nat tt
  {{ fun ve s => 
    match ve with 
    | inl _ => False
    | inr _ => s = n + 1
    end
  }}.
Proof.
  eapply bind_wp.
  all: swap 2 1. 
  intros.
  eapply strengthen_pre.
  eapply fail_wp.
  intros.
  simpl.
  apply H.
  all: swap 2 1.
  intros.
  apply H.


  eapply strengthen_pre.
  eapply put_wp.
  mysimp.
  Unshelve.
  exact unit.
Qed.

Example cond_fail b:
  {{ fun s => s = b /\ b = true }}
    if b then state_fail tt else state_return true
  {{ fun r s => r = inr tt }}.
Proof.
  eapply strengthen_pre.
  repeat wp.
  mysimp.
Qed.
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
  eapply strengthen_pre.
  eapply (case_nat_wp n).
  eapply strengthen_pre.
  eapply return_wp.
  intros.
  destruct H as [it _].
  exact it.

  eapply strengthen_pre.
  eapply bind_wp.
  all: swap 2 1.
  intros.
  eapply strengthen_pre.
  eapply fail_wp.
  intros.
  exact H.
  eapply put_wp.
  intros.
  simpl.
  exact H.
  intros.
  simpl.
  destruct H as [n' [_ it]].
  exact it.
  mysimp.
  destruct n; mysimp.
  Unshelve.
  exact unit.
Qed.

Example eo_pres' n:
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
  eapply strengthen_pre.
  wp.
  eapply strengthen_pre.
  wp.

  intros.
  destruct H as [it _].
  exact it.

  wp.
  all: swap 2 1.
  intros.
  eapply strengthen_pre.
  wp.
  intros.
  exact H.
  eapply strengthen_pre.
  wp.
  intros.
  destruct H as [n' [eq it]].
  exact it.
  intros.
  exact H.
  destruct n; mysimp.
  Unshelve.
  exact unit.
Qed.

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
  eapply strengthen_pre.
  unfold get_branch.
  wp.
  all: swap 2 1.

  intros.
  apply (eo_pres r).
  wp.
  intros.
  exact H.
  mysimp.
Qed.

Fixpoint iter_incr (n: nat) : @state_monad nat unit unit :=
  match n with 
  | 0 => skip
  | S n' => iter_incr n' ;; put_state (fun x => x + 1)
  end.

Lemma iter_incr_n n m:
  {{ fun s => s = n }}
    iter_incr m
  {{ Norm (fun r s' => s' = n + m )}}.
Proof.
  induction m.
  - unfold iter_incr.
    mysimp.
  - unfold iter_incr. fold iter_incr.
    eapply strengthen_pre.
    wp.
    all: swap 2 1.
    intros. 
    wp.
    eapply weaken_post.
    apply IHm.
    all: swap 2 1.
    intros.
    exact H.
    mysimp.
    lia.
    mysimp.
  Unshelve.
  exact unit.
Qed.
  