Require Export Poulet4.Monads.Monad.

(** A more general version of [Monads.Statee]. *)
(* TODO: change [Monads.Statee] to this
   more general definition and fix dependencies. *)

Open Scope monad.

Definition State (St : Type) (A : Type) : Type := St -> A * St.

Section State.
  Context {St : Type}.

  Definition State_ret {A : Type} (a : A) : State St A := fun st => (a, st).

  Definition State_bind {A B : Type} (m : State St A) (f : A -> State St B) : State St B :=
    fun st => let '(a, st') := m st in f a st'.
End State.

Global Instance State_monad_inst (St : Type) : Monad (State St) :=
  { mret A := @State_ret St A ; mbind A B := @State_bind St A B }.
