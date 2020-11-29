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
Module CheckExpr (LOC NAME : P4Data) (INT BIGINT : P4Numeric).
  Module IU := P4NumericUtil(INT).
  Infix "+" := IU.add (at level 50, left associativity).

  Module E := Expr LOC NAME INT BIGINT.
  Module F := E.F.
  Export E.ExprNotations.

  Module NM := Env NAME.
  Module LM := Env LOC.

  (** Available error names. *)
  Definition errors : Type := NM.env unit.

  (** Available matchkinds. *)
  Definition matchkinds : Type := NM.env unit.

  (** Typing context. *)
  Definition gam : Type := NM.env E.t.

  Reserved Notation "'$' ers ',,' mks ',,' gm '$' '|=' ex '\in' ty '\goes' dr"
           (at level 40, ex custom p4expr, ty custom p4type at level 0).

  (** Expression typing as a relation. *)
  Inductive check (errs : errors) (mkds : matchkinds)
            (g : gam) : dir -> E.e -> E.t -> Prop :=
    (* Literals. *)
    | chk_bool (b : bool) :
        $ errs ,, mkds ,, g $ |= BOOL b \in Bool \goes DIn
    | chk_int (n : INT.t) :
        $ errs ,, mkds ,, g $ |=  Int n \in int \goes DIn
    | chk_bitstring (w : INT.t) (v : BIGINT.t) :
        $ errs ,, mkds ,, g $ |= w @ v \in bit<w> \goes DIn
    | chk_var (x : NAME.t) (ty : E.t) :
        g x = Some ty ->
        $ errs ,, mkds ,, g $ |= Var x :: ty end \in ty \goes DInOut
   (* Unary operations. *)
   | chk_not (exp : E.e) :
       $ errs ,, mkds ,, g $ |= exp \in Bool \goes DIn ->
       $ errs ,, mkds ,, g $ |= ! exp :: Bool end \in Bool \goes DIn
   | chk_bitnot (w : INT.t) (exp : E.e) :
       $ errs ,, mkds ,, g $ |= exp \in bit<w> \goes DIn ->
       $ errs ,, mkds ,, g $ |= ~ exp :: bit<w> end \in bit<w> \goes DIn
   | chk_uminus (exp : E.e) :
       $ errs ,, mkds ,, g $ |= exp \in int \goes DIn ->
       $ errs ,, mkds ,, g $ |= - exp :: int end \in int \goes DIn
   (* Binary Operations. *)
   | chk_plus (e1 e2 : E.e) :
       $ errs ,, mkds ,, g $ |= e1 \in int \goes DIn ->
       $ errs ,, mkds ,, g $ |= e2 \in int \goes DIn ->
       $ errs ,, mkds ,, g $
         |= + e1 :: int e2 :: int end \in int \goes DIn
   | chk_minus (e1 e2 : E.e) :
       $ errs ,, mkds ,, g $ |= e1 \in int \goes DIn ->
       $ errs ,, mkds ,, g $ |= e2 \in int \goes DIn ->
       $ errs ,, mkds ,, g $
         |= -- e1 :: int e2 :: int end \in int \goes DIn
   | chk_plussat (n : INT.t) (e1 e2 : E.e) :
       $ errs ,, mkds ,, g $ |= e1 \in bit<n> \goes DIn ->
       $ errs ,, mkds ,, g $ |= e2 \in bit<n> \goes DIn ->
       $ errs ,, mkds ,, g $
         |= |+| e1 :: bit<n> e2 :: bit<n> end \in bit<n> \goes DIn
   | chk_minussat (n : INT.t) (e1 e2 : E.e) :
       $ errs ,, mkds ,, g $ |= e1 \in bit<n> \goes DIn ->
       $ errs ,, mkds ,, g $ |= e2 \in bit<n> \goes DIn ->
       $ errs ,, mkds ,, g $
         |= |-| e1 :: bit<n> e2 :: bit<n> end \in bit<n> \goes DIn
   | chk_bitand (n : INT.t) (e1 e2 : E.e) :
       $ errs ,, mkds ,, g $ |= e1 \in bit<n> \goes DIn ->
       $ errs ,, mkds ,, g $ |= e2 \in bit<n> \goes DIn ->
       $ errs ,, mkds ,, g $
         |= & e1 :: bit<n> e2 :: bit<n> end \in bit<n> \goes DIn
   | chk_bitor (n : INT.t) (e1 e2 : E.e) :
       $ errs ,, mkds ,, g $ |= e1 \in bit<n> \goes DIn ->
       $ errs ,, mkds ,, g $ |= e2 \in bit<n> \goes DIn ->
       $ errs ,, mkds ,, g $
            |= | e1 :: bit<n> e2 :: bit<n> end \in bit<n> \goes DIn
   | chk_bitxor (n : INT.t) (e1 e2 : E.e) :
       $ errs ,, mkds ,, g $ |= e1 \in bit<n> \goes DIn ->
       $ errs ,, mkds ,, g $ |= e2 \in bit<n> \goes DIn ->
       $ errs ,, mkds ,, g $
         |= ^ e1 :: bit<n> e2 :: bit<n> end \in bit<n> \goes DIn
   | chk_and (e1 e2 : E.e) :
       $ errs ,, mkds ,, g $ |= e1 \in Bool \goes DIn ->
       $ errs ,, mkds ,, g $ |= e2 \in Bool \goes DIn ->
       $ errs ,, mkds ,, g $
            |= && e1 :: Bool e2 :: Bool end \in Bool \goes DIn
   | chk_or (e1 e2 : E.e) :
       $ errs ,, mkds ,, g $ |= e1 \in Bool \goes DIn ->
       $ errs ,, mkds ,, g $ |= e2 \in Bool \goes DIn ->
       $ errs ,, mkds ,, g $
         |= || e1 :: Bool e2 :: Bool end \in Bool \goes DIn
   | chk_le (e1 e2 : E.e) :
       $ errs ,, mkds ,, g $ |= e1 \in int \goes DIn ->
       $ errs ,, mkds ,, g $ |= e2 \in int \goes DIn ->
       $ errs ,, mkds ,, g $
            |= <= e1 :: int e2 :: int end \in Bool \goes DIn
   | chk_ge (e1 e2 : E.e) :
       $ errs ,, mkds ,, g $ |= e1 \in int \goes DIn ->
       $ errs ,, mkds ,, g $ |= e2 \in int \goes DIn ->
       $ errs ,, mkds ,, g $
         |= >= e1 :: int e2 :: int end \in Bool \goes DIn
   | chk_lt (e1 e2 : E.e) :
       $ errs ,, mkds ,, g $ |= e1 \in int \goes DIn ->
       $ errs ,, mkds ,, g $ |= e2 \in int \goes DIn ->
       $ errs ,, mkds ,, g $
         |= < e1 :: int e2 :: int end \in Bool \goes DIn
   | chk_gt (e1 e2 : E.e) :
       $ errs ,, mkds ,, g $ |= e1 \in int \goes DIn ->
       $ errs ,, mkds ,, g $ |= e2 \in int \goes DIn ->
       $ errs ,, mkds ,, g $
         |= > e1 :: int e2 :: int end \in Bool \goes DIn
   | chk_eq (ty : E.t) (e1 e2 : E.e) :
       $ errs ,, mkds ,, g $ |= e1 \in ty \goes DIn ->
       $ errs ,, mkds ,, g $ |= e2 \in ty \goes DIn ->
       $ errs ,, mkds ,, g $
         |= == e1 :: ty e2 :: ty end \in Bool \goes DIn
   | chk_neq (ty : E.t) (e1 e2 : E.e) :
       $ errs ,, mkds ,, g $ |= e1 \in ty \goes DIn ->
       $ errs ,, mkds ,, g $ |= e2 \in ty \goes DIn ->
       $ errs ,, mkds ,, g $
         |= != e1 :: ty e2 :: ty end \in Bool \goes DIn
   | chk_shl (n : INT.t) (e1 e2 : E.e) :
       $ errs ,, mkds ,, g $ |= e1 \in bit<n> \goes DIn ->
       $ errs ,, mkds ,, g $ |= e2 \in int \goes DIn ->
       $ errs ,, mkds ,, g $
         |= << e1 :: bit<n> e2 :: int end \in bit<n> \goes DIn
   | chk_shr (n : INT.t) (e1 e2 : E.e) :
       $ errs ,, mkds ,, g $ |= e1 \in bit<n> \goes DIn ->
       $ errs ,, mkds ,, g $ |= e2 \in int \goes DIn ->
       $ errs ,, mkds ,, g $
         |= >> e1 :: bit<n> e2 :: int end \in bit<n> \goes DIn
   | chk_plusplus (m n w : INT.t) (e1 e2 : E.e) :
       m + n = w ->
       $ errs ,, mkds ,, g $ |= e1 \in bit<m> \goes DIn ->
       $ errs ,, mkds ,, g $ |= e2 \in bit<n> \goes DIn ->
       $ errs ,, mkds ,, g $
         |= ++ e1 :: bit<m> e2 :: bit<n> end \in bit<w> \goes DIn
   (* Member expressions. *)
   | chk_hdr_mem (he : E.e) (x : NAME.t)
                 (fields : F.fs E.t) (tx : E.t) (dr : dir) :
       In (x, tx) fields ->
       $ errs ,, mkds ,, g $ |= he \in hdr { fields } \goes dr ->
       $ errs ,, mkds ,, g $
         |= [ he :: hdr { fields } ] x \in tx \goes dr
   | chk_rec_mem (re : E.e) (x : NAME.t)
                 (fields : F.fs E.t) (tx : E.t) (dr : dir) :
       In (x, tx) fields ->
       $ errs ,, mkds ,, g $ |= re \in rec { fields } \goes dr ->
       $ errs ,, mkds ,, g $
         |= [ re :: rec { fields } ] x \in tx \goes dr
   (* Records. *)
   | chk_rec_lit (efs : F.fs E.e) (tfs : F.fs E.t) :
      F.relfs (check errs mkds g DIn) efs tfs ->
      $ errs ,, mkds ,, g $ |= rec { efs } \in rec { tfs } \goes DIn
   (* Errors and matchkinds. *)
   | chk_error (err : NAME.t) :
       errs err = Some tt ->
       $ errs ,, mkds ,, g $ |= Error err \in error \goes DIn
   | chk_matchkind (mkd : NAME.t) :
       mkds mkd = Some tt ->
       $ errs ,, mkds ,, g $ |= Matchkind mkd \in error \goes DIn
   (* Action and extern calls. TODO: directions. *)
   | chk_call (params : F.fs E.t) (args : F.fs E.e)
              (returns : E.t) (callee : E.e) :
       $ errs ,, mkds ,, g $
         |= callee \in params |-> returns \goes DIn ->
       F.relfs (check errs mkds g DIn) args params ->
       $ errs ,, mkds ,, g $
         |= call callee :: {{ params |-> returns }} with args end
         \in returns \goes DIn
   where "'$' ers ',,' mks ',,' gm  '$' '|=' ex '\in' ty '\goes' dr"
           := (check ers mks gm dr ex ty).
End CheckExpr.
