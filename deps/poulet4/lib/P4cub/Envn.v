Require Export Coq.Classes.EquivDec.

Require Import Poulet4.Monads.Monad.
Require Import Poulet4.Monads.Option.

Declare Custom Entry p4env.

(** * Environments *)
Module Env.

(** Definition of environments. *)
Definition t (D T : Type) : Type := D -> option T.

(** The empty environment. *)
Definition empty (D T : Type) : t D T := fun _ => None.

Section EnvDefs.
  Context {D T : Type}.

  Context {equiv_rel : D -> D -> Prop}.

  Context {HEquiv : Equivalence equiv_rel}.

  Context {HE : EqDec D equiv_rel}.

  (** Updating the environment. *)
  Definition bind (x : D) (v : T) (e : t D T) : t D T :=
    fun y => if x == y then Some v else e y.
  (**[]*)

  (** Scope Shadowing, [e1] shadows [e2]. *)
  Definition scope_shadow (e1 e2 : t D T) : t D T :=
    fun x => e1 x ;; e2 x.
  (**[]*)

  (* TODO: whatever lemmas needed. *)
End EnvDefs.

Module EnvNotations.
  Notation "'!{' env '}!'" := env (env custom p4env at level 99).
  Notation "x" := x (in custom p4env at level 0, x constr at level 0).
  Notation "'∅'" := (empty _ _) (in custom p4env at level 0, no associativity).
  Notation "x ↦ v ';;' e"
    := (bind x v e)
         (in custom p4env at level 40, e custom p4env,
             right associativity).
  Notation "e1 ≪ e2"
           := (scope_shadow e1 e2)
                (in custom p4env at level 41, e1 custom p4env,
                    e2 custom p4env, right associativity).
End EnvNotations.
End Env.
