Require Export Coq.Classes.EquivDec.

Require Import Poulet4.Monads.Monad.
Require Import Poulet4.Monads.Option.

Declare Custom Entry p4env.

(** * Environments *)
Module Env.

(** Definition of environments. *)
Definition t (D T : Type) : Type := list (D * T).

(** The empty environment. *)
Definition empty (D T : Type) : t D T := nil.

Section EnvDefs.
  Context {D T : Type}.

  Context {equiv_rel : D -> D -> Prop}.

  Context {HEquiv : Equivalence equiv_rel}.

  Context {HE : EqDec D equiv_rel}.

  (** Looking up values in the environment. *)
  Fixpoint find (x: D) (e: t D T) : option T :=
    match e with
    | nil => None
    | (y, v) :: e' =>
      if HE x y
      then Some v
      else find x e'
    end.
  (**[]*)

  (** Updating the environment. *)
  Definition bind (x : D) (v : T) (e : t D T) : t D T :=
    (x, v) :: e.
  (**[]*)

  (** Scope Shadowing, [e1] shadows [e2]. *)
  Definition scope_shadow (e1 e2 : t D T) : t D T :=
    e1 ++ e2.
  (**[]*)

  Fixpoint keys (e: t D T) : list D := 
    match e with 
    | nil => nil
    | (y, v) :: e' =>
      let keys' := keys e' in 
      match find y e' with
      | None => y::keys'
      | _ => keys'
      end
    end.
  (* TODO: whatever lemmas needed. *)
End EnvDefs.

Definition map_keys {D T D'} (f: D -> D') : t D T -> t D' T :=
  List.map (fun '(k, v) => (f k, v)).

Definition map_vals {D T T'} (f: T -> T') : t D T -> t D T' :=
  List.map (fun '(k, v) => (k, f v)).

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
