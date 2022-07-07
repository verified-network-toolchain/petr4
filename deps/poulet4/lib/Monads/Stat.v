Require Export Poulet4.Monads.Monad.

(** A more general version of [Monads.Statee]. *)
(* TODO: change [Monads.State] to this
   more general definition and fix dependencies. *)

Open Scope monad.

Definition State (St : Type) (A : Type) : Type := St -> A * St.

Section State.
  Context {St : Type}.

  Definition State_ret {A : Type} (a : A) : State St A := fun st => (a, st).

  Definition State_bind {A B : Type} (m : State St A) (f : A -> State St B) : State St B :=
    fun st => let '(a, st') := m st in f a st'.

  Definition State_get : State St St := fun st => (st, st).

  Definition State_put (st : St) : State St unit := fun _ => (tt, st).

  Check List.fold_right.

  Definition
    State_fold_right
    {A B : Type}
    (f : B -> A -> State St A)
    (a : A) (l : list B) : State St A :=
    fun st => List.fold_right (fun b '(a,st) => f b a st) (a, st) l.
End State.

Global Instance State_monad_inst (St : Type) : Monad (State St) :=
  { mret A := @State_ret St A ; mbind A B := @State_bind St A B }.
