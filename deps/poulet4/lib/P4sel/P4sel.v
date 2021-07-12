Set Warnings "-custom-entry-overridden".
Require Import Coq.PArith.BinPosDef Coq.PArith.BinPos
        Coq.ZArith.BinIntDef Coq.ZArith.BinInt Poulet4.P4Arith
        Coq.Classes.EquivDec Coq.Program.Program.
Require Export Poulet4.P4cub.Syntax.P4Field.
Require Coq.Logic.Eqdep_dec.
Require Poulet4.P4cub.Syntax.Syntax.



(** * P4cub AST *)
Module P4sel.
  Module F := Field.
  Module P4cub := Poulet4.P4cub.Syntax.AST.P4cub.
  (** * Expression Grammar *)
  Module Expr.
    
    Section Expressions.
      Variable (tags_t : Type).

      (** Expressions annotated with types,
          unless the type is obvious. *)
      Inductive e : Type :=
      | EBool (b : bool) (i : tags_t)                     (* booleans *)
      | EVar (type : P4cub.Expr.t) (x : string)
             (i : tags_t)                              (* variables *)
                           (* structs and structs *)
      | EExprMember (mem : string)
                    (expr_type : P4cub.Expr.t)
                    (arg : e) (i : tags_t)             (* member-expressions *)
      | EError (err : option string)
               (i : tags_t)                            (* error literals *)
      | EMatchKind (mk : P4cub.Expr.matchkind) (i : tags_t)       (* matchkind literals *)
      .
      (**[]*)

      (** Function call arguments. *)
      Definition args : Type :=
        F.fs string (P4cub.paramarg (P4cub.Expr.t * e) (P4cub.Expr.t * e)).
      (**[]*)

      (** Function call. *)
      Definition arrowE : Type :=
        P4cub.arrow string (P4cub.Expr.t * e) (P4cub.Expr.t * e) (P4cub.Expr.t * e).
      (**[]*)

      (** Constructor arguments. *)
      Inductive constructor_arg : Type :=
      | CAExpr (expr : e) (* plain expression *)
      | CAName (x : string) (* name of parser, control, package, or extern *).
      (**[]*)

      Definition constructor_args : Type := F.fs string constructor_arg.
    End Expressions.

    Arguments EBool {tags_t}.
    Arguments EVar {tags_t}.
    Arguments EExprMember {tags_t}.
    Arguments EError {tags_t}.
    Arguments EMatchKind {tags_t}.
    Arguments CAExpr {_}.
    Arguments CAName {_}.

    
  End Expr.

  (** * Statement Grammar *)
  Module Stmt.
    Module E := Expr.

    Section Statements.
      Variable (tags_t : Type).

     

      Inductive s : Type :=
      | SSkip (i : tags_t)                              (* skip, useful for
                                                           small-step semantics *)
      | SVardecl (type : P4cub.Expr.t)
                 (x : string) (i : tags_t)       (* Variable declaration. *)
      | SAssign (type : P4cub.Expr.t) (lhs rhs : E.e tags_t)
                (i : tags_t)                            (* assignment *)
      | SUop (dst_type : P4cub.Expr.t)
              (op: P4cub.Expr.uop)
              (arg: E.e tags_t)
              (dst: string)
              (i : tags_t)                              (* apply uop *)
      | SBop (dst_type : P4cub.Expr.t)
              (op: P4cub.Expr.bop)
              (le : E.e tags_t)
              (re : E.e tags_t )
              (dst : string)
              (i : tags_t)                                (* apply bop *)
      | SBitAssign (dst_type : P4cub.Expr.t)
                    (dst : string)
                    (width : positive)
                    (val : Z)
                    (i : tags_t)                        (* assign a bit string value to a variable *)
      | SIntAssign (dst_type : P4cub.Expr.t)
                    (dst : string)
                    (width : positive)
                    (val : Z)
                    (i : tags_t)                        (* assign an int value to a variable *)
      | SSlice (n : E.e tags_t )
                (n_type : P4cub.Expr.t)
                (hi lo : positive)
                (dst : string)
                (i : tags_t)                             (* bit slicing *)   
      | SCast (type : P4cub.Expr.t)
              (arg: E.e tags_t)
              (dst: string)
              (i: tags_t)                                 (* casting *)
      | STuple (es : list (E.e tags_t)) 
                (dst : string)
                (i : tags_t)
      | SStruct (fields : F.fs string (P4cub.Expr.t* (E.e tags_t)))
                (dst : string)
                (i : tags_t)
      | SHeader (fields : F.fs string (P4cub.Expr.t * (E.e tags_t)))
                (dst : string)
                (valid : E.e tags_t)
                (i : tags_t)
      | SHeaderStack (fields : F.fs string P4cub.Expr.t)
                      (headers : list (E.e tags_t))
                      (size : positive)
                      (next_index : Z)
                      (dst : string)
                      (i : tags_t)
      | SHeaderStackAccess (stack : E.e tags_t)
                           (index : Z)
                           (dst : string)
                           (i : tags_t)
      | SConditional (guard_type : P4cub.Expr.t)
                     (guard : E.e tags_t)
                     (tru_blk fls_blk : s) (i : tags_t) (* conditionals *)
      | SSeq (s1 s2 : s) (i : tags_t)                   (* sequences *)
      | SBlock (blk : s)                                (* blocks *)
      | SExternMethodCall (e : string) (f : string)
                          (args : E.arrowE tags_t)
                          (i : tags_t)                  (* extern method calls *)
      | SFunCall (f : string)
                 (args : E.arrowE tags_t) (i : tags_t)  (* function call *)
      | SActCall (f : string)
                 (args : E.args tags_t) (i : tags_t)    (* action call *)
      | SReturnVoid (i : tags_t)                        (* void return statement *)
      | SReturnFruit (t : P4cub.Expr.t)
                     (e : E.e tags_t)(i : tags_t)       (* fruitful return statement *)
      | SExit (i : tags_t)                              (* exit statement *)
      | SInvoke (x : string) (i : tags_t)          (* table invocation *)
      | SApply (x : string)
               (args : E.args tags_t) (i : tags_t)      (* control apply statements,
                                                           where [x] is the
                                                           name of an instance *).
    (**[]*)
    End Statements.

    Arguments SSkip {tags_t}.
    Arguments SVardecl {_}.
    Arguments SUop {tags_t}.
    Arguments SBop {tags_t}.
    Arguments SBitAssign {tags_t}.
    Arguments SIntAssign {tags_t}.
    Arguments SSlice {tags_t}.
    Arguments SCast {tags_t}.
    Arguments STuple {tags_t}.
    Arguments SStruct {tags_t}.
    Arguments SHeader {tags_t}.
    Arguments SHeaderStack {tags_t}.
    Arguments SHeaderStackAccess {tags_t}.
    Arguments SAssign {tags_t}.
    Arguments SConditional {tags_t}.
    Arguments SSeq {tags_t}.
    Arguments SBlock {_}.
    Arguments SFunCall {_}.
    Arguments SActCall {_}.
    Arguments SExternMethodCall {_}.
    Arguments SReturnVoid {tags_t}.
    Arguments SReturnFruit {tags_t}.
    Arguments SExit {_}.
    Arguments SApply {_}.
    Arguments SInvoke {_}.
    
    
  End Stmt.

  (** * Parsers *)
  Module Parser.
    Module E := Expr.
    Module S := Stmt.


    Section Parsers.
      Variable (tags_t : Type).

      (** Parser expressions, which evaluate to state names *)
      Inductive e : Type :=
      | PGoto (st : P4cub.Parser.state) (i : tags_t) (* goto state [st] *)
      | PSelect (exp : E.e tags_t) (default : e)
                (cases : F.fs P4cub.Parser.pat e)
                (i : tags_t)        (* select expressions,
                                       where "default" is
                                       the wild card case *).
      (**[]*)

      (** Parser State Blocks. *)
      Inductive state_block : Type :=
      | State (stmt : S.s tags_t) (transition : e).
      (**[]*)
    End Parsers.

    Arguments PGoto {_}.
    Arguments PSelect {_}.
    Arguments State {_}.

    
  End Parser.

  (** * Controls *)
  Module Control.
    Module E := Expr.
    Module S := Stmt.

    Module ControlDecl.
      Section ControlDecls.
        Variable (tags_t : Type).

        (** Table. *)
        Inductive table : Type :=
        | Table (key : list (P4cub.Expr.t * E.e tags_t * P4cub.Expr.matchkind))
                (actions : list string)
                (initialization : S.s tags_t).
        (**[]*)

        (** Declarations that may occur within Controls. *)
        (* TODO, this is a stub. *)
        Inductive d : Type :=
        | CDAction (a : string)
                   (signature : P4cub.Expr.params)
                   (body : S.s tags_t) (i : tags_t) (* action declaration *)
        | CDTable (t : string) (bdy : table)
                  (i : tags_t)                      (* table declaration *)
        | CDSeq (d1 d2 : d) (i : tags_t).
        (**[]*)
      End ControlDecls.

      Arguments Table {_}.
      Arguments CDAction {_}.
      Arguments CDTable {_}.
      Arguments CDSeq {_}.

      
    End ControlDecl.
  End Control.

  (** * Top-Level Declarations *)
  Module TopDecl.
    Module E := Expr.
    Module S := Stmt.
    Module C := Control.ControlDecl.
    Module P := Parser.

    Section TopDeclarations.
      Variable (tags_t : Type).

      (** Top-level declarations. *)
      Inductive d : Type :=
      | TPInstantiate (C : string) (x : string)
                     (cargs : E.constructor_args tags_t)
                     (arg_init: S.s tags_t)
                     (i : tags_t) (* constructor [C] that 
                                     runs [arg_init] first
                                     and then use
                                     constructor [args]
                                     makes instance [x]. *)
      | TPExtern (e : string)
                 (cparams : P4cub.Expr.constructor_params)
                 (methods : F.fs string P4cub.Expr.arrowT)
                 (i : tags_t) (* extern declarations *)
      | TPControl (c : string)
                  (cparams : P4cub.Expr.constructor_params) (* constructor params *)
                  (params : P4cub.Expr.params) (* apply block params *)
                  (body : C.d tags_t) (apply_blk : S.s tags_t) (i : tags_t)
      | TPParser (p : string)
                 (cparams : P4cub.Expr.constructor_params) (* constructor params *)
                 (params : P4cub.Expr.params)           (* invocation params *)
                 (start : P.state_block tags_t) (* start state *)
                 (states : F.fs string (P.state_block tags_t)) (* parser states *)
                 (i : tags_t) (* parser declaration *)
      | TPFunction (f : string) (signature : P4cub.Expr.arrowT) (body : S.s tags_t)
                   (i : tags_t) (* function/method declaration *)
      | TPPackage (p : string)
                  (cparams : P4cub.Expr.constructor_params) (* constructor params *)
                  (i : tags_t) (* package type declaration *)
      | TPSeq (d1 d2 : d) (i : tags_t).
      (**[]*)
    End TopDeclarations.

    Arguments TPInstantiate {_}.
    Arguments TPExtern {_}.
    Arguments TPControl {_}.
    Arguments TPParser {_}.
    Arguments TPFunction {_}.
    Arguments TPPackage {_}.
    Arguments TPSeq {_}.

    
  End TopDecl.

  
End P4sel.
