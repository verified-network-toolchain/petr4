From Hammer Require Import Tactics.
From Hammer Require Import Reflect.

(* Syntax for arithmetic expressions over a single variable *)
Inductive var := X.
Inductive exp :=
| Var (v: var)
| Lit (n: nat)
| Plus (e1 e2: exp)
| Mul (e1 e2: exp).

(* Semantics for expressions *)
Fixpoint eval (ex: exp) (x: nat) :=
  match ex with 
  | Var X => x
  | Lit n => n
  | Plus e1 e2 =>
    eval e1 x + eval e2 x
  | Mul e1 e2 =>
    eval e1 x * eval e2 x
  end.

(* Simple propositional formulae over arithmetic expressions *)
Inductive formula : Type :=
| Eq (e1 e2: exp)
| Not (f: formula)
| And (f1 f2: formula)
| Or (f1 f2: formula).

(* Checking whether x satisfies the formula f[x] by turning it into a
   Coq proposition. *)
Fixpoint sat (f: formula) (x: nat) : Prop :=
  match f with
  | Eq e1 e2 => eval e1 x = eval e2 x
  | Not f => ~ sat f x
  | And f1 f2 => sat f1 x /\ sat f2 x
  | Or f1 f2 => sat f1 x \/ sat f2 x
  end.

(* Transition system for the forward algorithm. *)
Inductive guess : bool -> formula -> nat -> Type :=
| GuessInit :
    forall f,
      guess false f 0
| GuessWrong :
    forall f x,
      ~ sat f x ->
      guess false f x ->
      guess false f (S x)
| GuessRight :
    forall f x,
      sat f x ->
      guess false f x ->
      guess true f x.

(* Soundness of algorithm *)
Lemma guess_sound:
  forall f x,
    guess true f x ->
    sat f x.
Proof.
  intros f x H.
  inversion H.
  assumption.
Defined.
(* Leaving guess_sound transparent with Defined. allows
   half_ten_is_five', below, to reduce to eq_refl. *)

Theorem half_ten_is_five:
  sat (Eq (Plus (Var X) (Var X)) (Lit 10)) 5.
Proof.
  cbv.
  exact eq_refl.
Qed.
Print half_ten_is_five.

Theorem half_ten_is_five':
  { x: nat | sat (Eq (Plus (Var X) (Var X)) (Lit 10)) x}.
Proof.
  repeat match goal with
         (* Final step. *)
         | g: guess true ?f ?x |- _ =>
           exists x; exact (guess_sound _ _ g)
         (* Intermediate steps. *)
         | g: guess false ?f ?x |- _ =>
           pose proof (GuessRight f x ltac:(sauto) g)
         | g: guess false ?f ?x |- _ =>
           pose proof (GuessWrong f x ltac:(sauto) g)
         (* Initial condition: pick out the initial algorithm state from the goal. *)
         | |- { z: nat | sat ?f z } =>
           pose proof (GuessInit f)
         end.
Defined.
Print half_ten_is_five'.
Eval cbv in (proj1_sig half_ten_is_five').
Eval cbv in (proj2_sig half_ten_is_five').

(* Transition system for the backward algorithm. *)
Inductive reaches : formula -> nat -> Type :=
| ReachesSat:
    forall f x,
      sat f x ->
      reaches f x
| ReachesStep:
    forall f x,
      reaches f (S x) ->
      reaches f x.

Lemma reaches_sound:
  forall f,
    reaches f 0 ->
    {n: nat | sat f n}.
Proof.
  intros f H.
  induction H.
  - exists x; assumption.
  - exact IHreaches.
Defined.

Theorem half_ten_is_five'':
  { x: nat | sat (Eq (Plus (Var X) (Var X)) (Lit 10)) x}.
Proof.
  apply reaches_sound.
  sauto.
Defined.
Print half_ten_is_five''.
Eval cbv in (proj1_sig half_ten_is_five'').
Eval cbv in (proj2_sig half_ten_is_five'').

Theorem half_ten_is_five''':
  { x: nat | sat (Eq (Plus (Var X) (Var X)) (Lit 10)) x}.
Proof.
  apply reaches_sound.
  repeat (constructor;
          match goal with
          | |- reaches _ _ => idtac
          | |- _ => sauto
          end).
Defined.
(* Note that the proof term is the same as half_ten_is_five''. *)
Print half_ten_is_five'''.
Eval cbv in (proj1_sig half_ten_is_five''').
Eval cbv in (proj2_sig half_ten_is_five''').


