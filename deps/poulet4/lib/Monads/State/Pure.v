Require Export Poulet4.Monads.Monad.
Require Import Coq.Program.Basics.

Local Open Scope program_scope.

Definition State (S A : Type) : Type := S -> A * S.

Definition return_state {S A : Type} (x : A) : State S A :=
  fun s => (x, s).

Definition bind_state {S A B : Type} (m : State S A) (f : A -> State S B) : State S B :=
  fun s =>
    let (x, s) := m s in
    (f x) s.

Definition get_state {S : Type} : State S S := fun s => (s, s).

Global Instance StateMonad {S : Type} : Monad (State S) :=
  { mret := @return_state S;
    mbind := @bind_state S;
  }.

Definition gets_state {S A : Type} (f : S -> A) : State S A := get_state >>| f.

Definition put_state {S : Type} (s : S) : State S unit := const (tt, s).

Definition modify_state {S : Type} (f : S -> S) : State S unit :=
  fun s => (tt, f s).

Definition run_state {S A : Type} (m : State S A) : S -> A * S := m.

Definition eval_state {S A : Type} (m : State S A) : S -> A :=
  fst ∘ run_state m.

Definition exec_state {S A : Type} (m : State S A) : S -> S :=
  snd ∘ run_state m.
