Require Export Poulet4.Monads.Monad.
Require Import Coq.Program.Basics.

Local Open Scope program_scope.

(** A "pure" state monad, i.e. one that does not compute a [Result] *)
Definition State (S A : Type) : Type := S -> A * S.

(** [return_state x] is a computes [x] given an initial state *)
Definition return_state {S A : Type} (x : A) : State S A :=
  fun s => (x, s).

(** [bind_state m f] first computes a value [x] using [m] and then
    computes a new value and state with [f] *)
Definition bind_state {S A B : Type} (m : State S A) (f : A -> State S B) : State S B :=
  fun s =>
    let (x, s) := m s in
    (f x) s.

Global Instance StateMonad {S : Type} : Monad (State S) :=
  { mret := @return_state S;
    mbind := @bind_state S;
  }.

(** [get_state] is computes the the internal state *)
Definition get_state {S : Type} : State S S := fun s => (s, s).

(** [put_state s] embeds the [s] into the state *)
Definition put_state {S : Type} (s : S) : State S unit := const (tt, s).

(** [run_state m s] executes the state monad [m] with initial state [s],
    yielding a pair of the computed the result and final state *)
Definition run_state {S A : Type} (m : State S A) : S -> A * S := m.

(** Same as [run_state], but only returns the final computation. *)
Definition eval_state {S A : Type} (m : State S A) : S -> A :=
  fst ∘ run_state m.
