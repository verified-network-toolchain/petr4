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
    | chk_bool (b : bool) :
        g, d |= BOOL b \in Bool \goes DIn
    | chk_int (n : INT.t) :
        g, d |=  Int n \in int \goes DIn
    | chk_bitstring (w : INT.t) (v : BIGINT.t) :
        g, d |= w @ v \in bit<w> \goes DIn
    | chk_var (x : NAME.t) (ty : t) :
        g x = Some ty ->
        g, d |= Var x :: ty end \in ty \goes DInOut
   | chk_not (exp : e) :
       g, d |= exp \in Bool \goes DIn ->
       g, d |= ! exp :: Bool end \in Bool \goes DIn
   | chk_bitnot (w : INT.t) (exp : e) :
       g, d |= exp \in bit<w> \goes DIn ->
       g, d |= ~ exp :: bit<w> end \in bit<w> \goes DIn
   | chk_uminus (exp : e) :
       g, d |= exp \in int \goes DIn ->
       g, d |= - exp :: int end \in int \goes DIn
   | chk_plus (e1 e2 : e) :
       g, d |= e1 \in int \goes DIn ->
       g, d |= e2 \in int \goes DIn ->
       g, d |= + e1 :: int e2 :: int end \in int \goes DIn
   | chk_minus (e1 e2 : e) :
       g, d |= e1 \in int \goes DIn ->
       g, d |= e2 \in int \goes DIn ->
       g, d |= -- e1 :: int e2 :: int end \in int \goes DIn
   | chk_plussat (n : INT.t) (e1 e2 : e) :
       g, d |= e1 \in bit<n> \goes DIn ->
       g, d |= e2 \in bit<n> \goes DIn ->
       g, d |= |+| e1 :: bit<n> e2 :: bit<n> end \in bit<n> \goes DIn
   | chk_minussat (n : INT.t) (e1 e2 : e) :
       g, d |= e1 \in bit<n> \goes DIn ->
       g, d |= e2 \in bit<n> \goes DIn ->
       g, d |= |-| e1 :: bit<n> e2 :: bit<n> end \in bit<n> \goes DIn
   | chk_bitand (n : INT.t) (e1 e2 : e) :
       g, d |= e1 \in bit<n> \goes DIn ->
       g, d |= e2 \in bit<n> \goes DIn ->
       g, d |= & e1 :: bit<n> e2 :: bit<n> end \in bit<n> \goes DIn
   | chk_bitor (n : INT.t) (e1 e2 : e) :
       g, d |= e1 \in bit<n> \goes DIn ->
       g, d |= e2 \in bit<n> \goes DIn ->
       g, d |= | e1 :: bit<n> e2 :: bit<n> end \in bit<n> \goes DIn
   | chk_bitxor (n : INT.t) (e1 e2 : e) :
       g, d |= e1 \in bit<n> \goes DIn ->
       g, d |= e2 \in bit<n> \goes DIn ->
       g, d |= ^ e1 :: bit<n> e2 :: bit<n> end \in bit<n> \goes DIn
   | chk_and (e1 e2 : e) :
       g, d |= e1 \in Bool \goes DIn ->
       g, d |= e2 \in Bool \goes DIn ->
       g, d |= && e1 :: Bool e2 :: Bool end \in Bool \goes DIn
   | chk_or (e1 e2 : e) :
       g, d |= e1 \in Bool \goes DIn ->
       g, d |= e2 \in Bool \goes DIn ->
       g, d |= || e1 :: Bool e2 :: Bool end \in Bool \goes DIn
   where "gm ',' dl '|=' exp '\in' typ '\goes' drc"
      := (check gm dl exp typ drc).
End CheckExpr.
