Require Export Coq.Lists.List.
Import ListNotations.

Section FoldRightIndex.
  Context {A B : Type}.
  Variables (f : nat -> B -> A -> A) (init : A).

  Fixpoint fold_righti_help (n : nat) (bs : list B) : A :=
    match bs with
    | [] => init
    | b :: bs => f n b (fold_righti_help (S n) bs)
    end.

  Definition fold_righti : list B -> A := fold_righti_help 0.
End FoldRightIndex.

Require Export Poulet4.Monads.Monad.

Open Scope monad.

Definition StateT (ST : Type) (M : Type -> Type) (A : Type) : Type :=
  ST -> M (A * ST)%type.

Section StateT.
  Context {ST : Type} {M : Type -> Type} `{M_Monad : Monad M}.

  Definition state_return {A : Type} (a : A) : StateT ST M A :=
    fun st => mret (a, st).

  Definition get_state : StateT ST M ST :=
    fun st => mret (st, st).

  Definition put_state (st : ST) : StateT ST M unit :=
    fun _ => mret (tt, st).

  Definition
    state_bind {A B : Type} (m : StateT ST M A)
    (f : A -> StateT ST M B) : StateT ST M B :=
    fun st => let* '(a, st) := m st in f a st.

  Definition state_lift {A : Type} (m : M A) : StateT ST M A :=
    fun st => let^ a := m in (a, st).

  Definition
    state_fold_right
    {A B : Type}
    (f : B -> A -> StateT ST M A)
    (a : A) (l : list B) : StateT ST M A :=
    fun st => List.fold_right (fun b m => let* '(a, st) := m in f b a st) (mret (a, st)) l.

  Definition
    state_fold_righti
    {A B : Type}
    (f : nat -> B -> A -> StateT ST M A)
    (a : A) (l : list B) : StateT ST M A :=
    fun st => fold_righti (fun i b m => let* '(a, st) := m in f i b a st) (mret (a, st)) l.
End StateT.
  
Global Instance
       StateT_monad (ST : Type) (M : Type -> Type)
       `{M_Monad : Monad M} : Monad (StateT ST M) :=
  { mret := @state_return ST _ M_Monad
  ; mbind := @state_bind ST _ M_Monad }.

Definition
  state_list_map
  {ST : Type} {M : Type -> Type} `{M_Monad : Monad M}
  {A B : Type} (f : A -> StateT ST M B)
  : list A -> StateT ST M (list B) :=
  state_fold_right
    (fun (a : A) (bs : list B) =>
       let^ b := f a in b :: bs) [].

Definition
  state_list_mapi
  {ST : Type} {M : Type -> Type} `{M_Monad : Monad M}
  {A B : Type} (f : nat -> A -> StateT ST M B)
  : list A -> StateT ST M (list B) :=
  state_fold_righti
    (fun (i : nat) (a : A) (bs : list B) =>
       let^ b := f i a in b :: bs) [].

Global Instance identity_monad : Monad (fun A => A) :=
  { mret := fun _ a => a
  ; mbind := fun _ _ a f => f a }.

Definition State (ST : Type) := StateT ST (fun x => x).

Definition
  State_lift {ST : Type} {M : Type -> Type}
  `{M_Monad : Monad M} {A : Type}
  (m : State ST A) : StateT ST M A :=
  fun st => mret (m st).
