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

(** * Typechecking *)
Module Typecheck (NAME : P4Data) (INT BIGINT : P4Numeric).
  Module IU := P4NumericUtil(INT).
  Infix "+" := IU.add (at level 50, left associativity).

  Module P := P4 NAME INT BIGINT.

  Module E := P.Expr.
  Module S := P.Stmt.

  Module F := E.F.
  Import E.ExprNotations.

  Module NM := Env NAME.

  (** Available error names. *)
  Definition errors : Type := NM.env unit.

  (** Available matchkinds. *)
  Definition matchkinds : Type := NM.env unit.

  (** Typing context. *)
  Definition gam : Type := NM.env E.t.

  Reserved Notation "'$' ers ',,' mks ',,' gm '$' '|=' ex '\in' ty"
           (at level 40, ex custom p4expr, ty custom p4type at level 0).

  (** Expression typing as a relation. *)
  Inductive check (errs : errors) (mkds : matchkinds)
            (g : gam) : E.e -> E.t -> Prop :=
    (* Literals. *)
    | chk_bool (b : bool) :
        $ errs ,, mkds ,, g $ |= BOOL b \in Bool
    | chk_int (n : INT.t) :
        $ errs ,, mkds ,, g $ |=  Int n \in int
    | chk_bitstring (w : INT.t) (v : BIGINT.t) :
        $ errs ,, mkds ,, g $ |= w @ v \in bit<w>
    | chk_var (x : NAME.t) (ty : E.t) :
        g x = Some ty ->
        $ errs ,, mkds ,, g $ |= Var x :: ty end \in ty
   (* Unary operations. *)
   | chk_not (exp : E.e) :
       $ errs ,, mkds ,, g $ |= exp \in Bool ->
       $ errs ,, mkds ,, g $ |= ! exp :: Bool end \in Bool
   | chk_bitnot (w : INT.t) (exp : E.e) :
       $ errs ,, mkds ,, g $ |= exp \in bit<w>  ->
       $ errs ,, mkds ,, g $ |= ~ exp :: bit<w> end \in bit<w>
   | chk_uminus (exp : E.e) :
       $ errs ,, mkds ,, g $ |= exp \in int ->
       $ errs ,, mkds ,, g $ |= - exp :: int end \in int
   (* Binary Operations. *)
   | chk_plus (e1 e2 : E.e) :
       $ errs ,, mkds ,, g $ |= e1 \in int ->
       $ errs ,, mkds ,, g $ |= e2 \in int ->
       $ errs ,, mkds ,, g $
         |= + e1 :: int e2 :: int end \in int
   | chk_minus (e1 e2 : E.e) :
       $ errs ,, mkds ,, g $ |= e1 \in int ->
       $ errs ,, mkds ,, g $ |= e2 \in int ->
       $ errs ,, mkds ,, g $
         |= -- e1 :: int e2 :: int end \in int
   | chk_plussat (n : INT.t) (e1 e2 : E.e) :
       $ errs ,, mkds ,, g $ |= e1 \in bit<n> ->
       $ errs ,, mkds ,, g $ |= e2 \in bit<n> ->
       $ errs ,, mkds ,, g $
         |= |+| e1 :: bit<n> e2 :: bit<n> end \in bit<n>
   | chk_minussat (n : INT.t) (e1 e2 : E.e) :
       $ errs ,, mkds ,, g $ |= e1 \in bit<n> ->
       $ errs ,, mkds ,, g $ |= e2 \in bit<n> ->
       $ errs ,, mkds ,, g $
         |= |-| e1 :: bit<n> e2 :: bit<n> end \in bit<n>
   | chk_bitand (n : INT.t) (e1 e2 : E.e) :
       $ errs ,, mkds ,, g $ |= e1 \in bit<n> ->
       $ errs ,, mkds ,, g $ |= e2 \in bit<n> ->
       $ errs ,, mkds ,, g $
         |= & e1 :: bit<n> e2 :: bit<n> end \in bit<n>
   | chk_bitor (n : INT.t) (e1 e2 : E.e) :
       $ errs ,, mkds ,, g $ |= e1 \in bit<n> ->
       $ errs ,, mkds ,, g $ |= e2 \in bit<n> ->
       $ errs ,, mkds ,, g $
            |= | e1 :: bit<n> e2 :: bit<n> end \in bit<n>
   | chk_bitxor (n : INT.t) (e1 e2 : E.e) :
       $ errs ,, mkds ,, g $ |= e1 \in bit<n>  ->
       $ errs ,, mkds ,, g $ |= e2 \in bit<n> ->
       $ errs ,, mkds ,, g $
         |= ^ e1 :: bit<n> e2 :: bit<n> end \in bit<n>
   | chk_and (e1 e2 : E.e) :
       $ errs ,, mkds ,, g $ |= e1 \in Bool ->
       $ errs ,, mkds ,, g $ |= e2 \in Bool ->
       $ errs ,, mkds ,, g $
            |= && e1 :: Bool e2 :: Bool end \in Bool
   | chk_or (e1 e2 : E.e) :
       $ errs ,, mkds ,, g $ |= e1 \in Bool ->
       $ errs ,, mkds ,, g $ |= e2 \in Bool ->
       $ errs ,, mkds ,, g $
         |= || e1 :: Bool e2 :: Bool end \in Bool
   | chk_le (e1 e2 : E.e) :
       $ errs ,, mkds ,, g $ |= e1 \in int ->
       $ errs ,, mkds ,, g $ |= e2 \in int ->
       $ errs ,, mkds ,, g $
            |= <= e1 :: int e2 :: int end \in Bool
   | chk_ge (e1 e2 : E.e) :
       $ errs ,, mkds ,, g $ |= e1 \in int ->
       $ errs ,, mkds ,, g $ |= e2 \in int ->
       $ errs ,, mkds ,, g $
         |= >= e1 :: int e2 :: int end \in Bool
   | chk_lt (e1 e2 : E.e) :
       $ errs ,, mkds ,, g $ |= e1 \in int ->
       $ errs ,, mkds ,, g $ |= e2 \in int ->
       $ errs ,, mkds ,, g $
         |= < e1 :: int e2 :: int end \in Bool
   | chk_gt (e1 e2 : E.e) :
       $ errs ,, mkds ,, g $ |= e1 \in int ->
       $ errs ,, mkds ,, g $ |= e2 \in int ->
       $ errs ,, mkds ,, g $
         |= > e1 :: int e2 :: int end \in Bool
   | chk_eq (ty : E.t) (e1 e2 : E.e) :
       $ errs ,, mkds ,, g $ |= e1 \in ty ->
       $ errs ,, mkds ,, g $ |= e2 \in ty ->
       $ errs ,, mkds ,, g $
         |= == e1 :: ty e2 :: ty end \in Bool
   | chk_neq (ty : E.t) (e1 e2 : E.e) :
       $ errs ,, mkds ,, g $ |= e1 \in ty ->
       $ errs ,, mkds ,, g $ |= e2 \in ty ->
       $ errs ,, mkds ,, g $
         |= != e1 :: ty e2 :: ty end \in Bool
   | chk_shl (n : INT.t) (e1 e2 : E.e) :
       $ errs ,, mkds ,, g $ |= e1 \in bit<n> ->
       $ errs ,, mkds ,, g $ |= e2 \in int ->
       $ errs ,, mkds ,, g $
         |= << e1 :: bit<n> e2 :: int end \in bit<n>
   | chk_shr (n : INT.t) (e1 e2 : E.e) :
       $ errs ,, mkds ,, g $ |= e1 \in bit<n> ->
       $ errs ,, mkds ,, g $ |= e2 \in int ->
       $ errs ,, mkds ,, g $
         |= >> e1 :: bit<n> e2 :: int end \in bit<n>
   | chk_plusplus (m n w : INT.t) (e1 e2 : E.e) :
       m + n = w ->
       $ errs ,, mkds ,, g $ |= e1 \in bit<m> ->
       $ errs ,, mkds ,, g $ |= e2 \in bit<n> ->
       $ errs ,, mkds ,, g $
         |= ++ e1 :: bit<m> e2 :: bit<n> end \in bit<w>
   (* Member expressions. *)
   | chk_hdr_mem (he : E.e) (x : NAME.t)
                 (fields : F.fs E.t) (tx : E.t) :
       In (x, tx) fields ->
       $ errs ,, mkds ,, g $ |= he \in hdr { fields } ->
       $ errs ,, mkds ,, g $
         |= [ he :: hdr { fields } ] x \in tx
   | chk_rec_mem (re : E.e) (x : NAME.t)
                 (fields : F.fs E.t) (tx : E.t) :
       In (x, tx) fields ->
       $ errs ,, mkds ,, g $ |= re \in rec { fields } ->
       $ errs ,, mkds ,, g $
         |= [ re :: rec { fields } ] x \in tx
   (* Records. *)
   | chk_rec_lit (efs : F.fs E.e) (tfs : F.fs E.t) :
      F.relfs (check errs mkds g) efs tfs ->
      $ errs ,, mkds ,, g $ |= rec { efs } \in rec { tfs }
   (* Errors and matchkinds. *)
   | chk_error (err : NAME.t) :
       errs err = Some tt ->
       $ errs ,, mkds ,, g $ |= Error err \in error
   | chk_matchkind (mkd : NAME.t) :
       mkds mkd = Some tt ->
       $ errs ,, mkds ,, g $ |= Matchkind mkd \in error
   (* Action and extern calls. TODO: directions. *)
   | chk_call (params : F.fs E.t) (args : F.fs E.e)
              (returns : E.t) (callee : E.e) :
       $ errs ,, mkds ,, g $ |= callee \in {{ params |-> returns }} ->
       F.relfs (check errs mkds g) args params ->
       $ errs ,, mkds ,, g $
         |= call callee :: {{ params |-> returns }} with args end \in returns
   where "'$' ers ',,' mks ',,' gm  '$' '|=' ex '\in' ty"
           := (check ers mks gm ex ty).
  (*[]*)

  Import S.StmtNotations.

  (** Statement signals. *)
  (*  Inductive signal : Set := SIG_Cont | SIG_Return. *)

  (*  Declare Custom Entry p4signal.

  Notation "x"
      := x (in custom p4signal at level 0, x constr at level 0).
  Notation "'C'" := SIG_Cont (in custom p4signal at level 0).
  Notation "'R'" := SIG_Return (in custom p4signal at level 0). *)

  Reserved Notation "'#' errs ',,' mks ',,' g1 '#' '|=' s '=|' g2"
           (at level 40, s custom p4stmt).

  Inductive check_stmt (errs : errors) (mkds : matchkinds)
    (g : gam) : S.s -> gam -> Prop :=
    | chk_skip :
        # errs ,, mkds ,, g # |= skip =| g
    | chk_seq (s1 s2 : S.s) (g1 g2 : gam) :
        (* My statement notation doesn't work. *)
        check_stmt errs mkds g  s1 g1 ->
        check_stmt errs mkds g1 s2 g2 ->
        check_stmt errs mkds g (S.SSeq s1 s2) g2
    | chk_vardecl (t : E.t) (x : NAME.t) (e : E.e) :
        $ errs ,, mkds ,, g $ |= e \in t  ->
        check_stmt errs mkds g (S.SVarDecl t x e) (NM.bind x t g)
    | chk_assign (t : E.t) (lhs rhs : E.e) :
        $ errs ,, mkds ,, g $ |= lhs \in t ->
        $ errs ,, mkds ,, g $ |= rhs \in t ->
        check_stmt errs mkds g (S.SAssign t lhs rhs) g
    | chk_cond (t : E.t) (guard : E.e) (tru fls : S.s) (g1 g2 : gam) :
        $ errs ,, mkds ,, g $ |= guard \in t ->
        check_stmt errs mkds g tru g1 ->
        check_stmt errs mkds g fls g2 ->
        check_stmt errs mkds g (S.SConditional t guard tru fls) g
    where "'#' ers ',,' mks ',,' g1 '#' '|=' s '=|' g2"
            := (check_stmt ers mks g1 s g2).
End Typecheck.
