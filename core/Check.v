(** * Typechecking *)

From CORE Require Export AST.

(** * Environments *)

(** Note how the type of the environment's domain
    is an argument to the environment functor. *)
Module Env (DOM : P4Data).
  Import DOM.
  Module DU := P4DataUtil DOM.
  Import DU.

  (** Definition of environments. *)
  Definition env (T : Type) : Type := t -> option T.

  (** The empty environment. *)
  Definition empty (T : Type) : env T := fun _ => None.

  Section EnvDefs.
    Context {T : Type}.

    (** Updating the environment. *)
    Definition bind (x : t) (v : T) (e : env T) : env T :=
      fun y => if x =? y then Some v else e y.

    (* TODO: whatever lemmas needed. *)
  End EnvDefs.
End Env.

(** * Expression Typechecking *)
Module CheckExpr (LOC INT BIGINT NAME : P4Data).
  Module EXPR := Expr LOC INT BIGINT NAME.
  Export EXPR.

  Module NM := Env NAME.
  Module LM := Env LOC.

  (** Typing context. *)
  Definition gam : Type := NM.env t.

  (** Type variable context. *)
  Definition del : Type := NM.env t.

  (** Typing store. *)
  Definition xi : Type := LM.env t.

  Reserved Notation "g ',' d '|=' exp '\in' typ '\goes' drc"
           (at level 40, exp custom p4expr,
            typ custom p4type at level 0).

  (** Expression typing as a relation. *)
  Inductive check (g : gam) (d : del) : e -> t -> dir -> Prop :=
    | chk_int (n : INT.t) :
        g, d |=  Int n \in int \goes DIn
    where "gm ',' dl '|=' exp '\in' typ '\goes' drc"
      := (check gm dl exp typ drc).
End CheckExpr.
