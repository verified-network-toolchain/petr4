Set Warnings "-custom-entry-overridden".
Require Import Coq.PArith.BinPosDef Coq.PArith.BinPos
        Coq.ZArith.BinIntDef Coq.ZArith.BinInt Poulet4.P4Arith
        Coq.Classes.EquivDec Coq.Program.Program.
Require Export Poulet4.P4cub.Syntax.P4Field.
Require Coq.Logic.Eqdep_dec.

(** Notation entries. *)
Declare Custom Entry p4type.
Declare Custom Entry p4constructortype.
Declare Custom Entry p4uop.
Declare Custom Entry p4bop.
Declare Custom Entry p4matchkind.
Declare Custom Entry p4expr.
Declare Custom Entry p4stmt.
Declare Custom Entry p4prsrstate.
Declare Custom Entry p4selectpattern.
Declare Custom Entry p4prsrexpr.
Declare Custom Entry p4prsrstateblock.
Declare Custom Entry p4ctrldecl.
Declare Custom Entry p4topdecl.

(** * P4cub AST *)
Module P4sel.
  Module F := Field.
  (** Function call parameters/arguments. *)
  Inductive paramarg (A B : Type) : Type :=
  | PAIn (a : A)
  | PAOut (b : B)
  | PAInOut (b : B).

  Arguments PAIn {_} {_}.
  Arguments PAOut {_} {_}.
  Arguments PAInOut {_} {_}.

  Definition paramarg_map {A B C D : Type}
             (f : A -> C) (g : B -> D)
             (pa : paramarg A B) : paramarg C D :=
    match pa with
    | PAIn a => PAIn (f a)
    | PAOut b => PAOut (g b)
    | PAInOut b => PAInOut (g b)
    end.
  (**[]*)

  (** A predicate on a [paramarg]. *)
  Definition pred_paramarg {A B : Type}
             (PA : A -> Prop) (PB : B -> Prop) (pa : paramarg A B) : Prop :=
    match pa with
    | PAIn a => PA a
    | PAOut b | PAInOut b => PB b
    end.
  (**[]*)

  Definition pred_paramarg_same {A : Type} (P : A -> Prop)
    : paramarg A A -> Prop := pred_paramarg P P.
  (**[]*)

  (** Relating [paramarg]s. *)
  Definition rel_paramarg {A1 A2 B1 B2 : Type}
             (RA : A1 -> A2 -> Prop) (RB : B1 -> B2 -> Prop)
             (pa1 : paramarg A1 B1)
             (pa2 : paramarg A2 B2) : Prop :=
    match pa1, pa2 with
    | PAIn a1, PAIn a2       => RA a1 a2
    | PAOut b1, PAOut b2
    | PAInOut b1, PAInOut b2 => RB b1 b2
    | _, _ => False
    end.
  (**[]*)

  Definition rel_paramarg_same {A B : Type} (R : A -> B -> Prop) :
    paramarg A A -> paramarg B B -> Prop :=
    rel_paramarg R R.
  (**[]*)

  (** Function signatures/instantiations. *)
  Inductive arrow (K A B R : Type) : Type :=
    Arrow (pas : F.fs K (paramarg A B)) (returns : option R).
  (**[]*)

  Arguments Arrow {_} {_} {_} {_}.

  (** * Expression Grammar *)
  Module Expr.
    Section P4Types.
      (** Expression types. *)
      Inductive t : Type :=
      | TBool                            (* bool *)
      | TBit (width : positive)          (* unsigned integers *)
      | TInt (width : positive)          (* signed integers *)
      | TError                           (* the error type *)
      | TMatchKind                       (* the matchkind type *)
      | TTuple (types : list t)          (* tuple type *)
      | TStruct (fields : F.fs string t) (* the struct and struct type *)
      | THeader (fields : F.fs string t) (* the header type *)
      | THeaderStack (fields : F.fs string t)
                     (size : positive)   (* header stack type *).
      (**[]*)

      (** Function parameters. *)
      Definition params : Type := F.fs string (paramarg t t).

      (** Function types. *)
      Definition arrowT : Type := arrow string t t t.

      (** Constructor Types. *)
      Inductive ct : Type :=
      | CTType (type : t)                   (* expression types *)
      | CTControl (cparams : F.fs string ct)
                  (parameters : params)     (* control types *)
      | CTParser (cparams : F.fs string ct)
                 (parameters : params)      (* parser types *)
      | CTPackage (cparams : F.fs string ct) (* package types *)
      | CTExtern (cparams : F.fs string ct)
                 (methods : F.fs string arrowT) (* extern types *).
      (**[]*)

      Definition constructor_params : Type := F.fs string ct.
    End P4Types.

    

   

    

    (** Default matchkinds. *)
    Inductive matchkind : Set :=
    | MKExact
    | MKTernary
    | MKLpm.
    (**[]*)

    Instance MatchKindEqDec : EqDec matchkind eq.
    Proof.
      unfold EqDec; unfold equiv, complement.
      intros [] []; try (left; reflexivity);
        try (right; intros H; inversion H).
    Defined.

    
    Section Expressions.
      Variable (tags_t : Type).

      (** Expressions annotated with types,
          unless the type is obvious. *)
      Inductive e : Type :=
      | EBool (b : bool) (i : tags_t)                     (* booleans *)
      | EVar (type : t) (x : string)
             (i : tags_t)                              (* variables *)
                           (* structs and structs *)
      | EExprMember (mem : string)
                    (expr_type : t)
                    (arg : e) (i : tags_t)             (* member-expressions *)
      | EError (err : option string)
               (i : tags_t)                            (* error literals *)
      | EMatchKind (mk : matchkind) (i : tags_t)       (* matchkind literals *)
      .
      (**[]*)

      (** Function call arguments. *)
      Definition args : Type :=
        F.fs string (paramarg (t * e) (t * e)).
      (**[]*)

      (** Function call. *)
      Definition arrowE : Type :=
        arrow string (t * e) (t * e) (t * e).
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

      Inductive uop : Set :=
      | Not        (* boolean negation *)
      | BitNot     (* bitwise negation *)
      | UMinus     (* integer negation *)
      | IsValid    (* check header validity *)
      | SetValid   (* set a header valid *)
      | SetInValid (* set a header invalid *)
      | NextIndex  (* get element at [nextIndex] from a header stack *)
      | Size       (* get a header stack's size *)
      | Push (n : positive) (* "push_front," shift stack right by [n] *)
      | Pop  (n : positive) (* "push_front," shift stack left by [n] *).
      (**[]*)

      (** Binary operations.
          The "Sat" suffix denotes
          saturating arithmetic:
          where there is no overflow. *)
      Inductive bop : Set :=
      | Plus     (* integer addition *)
      | PlusSat  (* saturating addition *)
      | Minus    (* integer subtraction *)
      | MinusSat (* saturating subtraction *)
      | Times    (* multiplication *)
      | Shl      (* bitwise left-shift *)
      | Shr      (* bitwise right-shift *)
      | Le       (* integer less-than *)
      | Ge       (* integer greater-than *)
      | Lt       (* integer less-than or equals *)
      | Gt       (* integer greater-than or equals *)
      | Eq       (* expression equality *)
      | NotEq    (* expression inequality *)
      | BitAnd   (* bitwise and *)
      | BitXor   (* bitwise exclusive-or *)
      | BitOr    (* bitwise or *)
      | PlusPlus (* bit-string concatenation *)
      | And      (* boolean and *)
      | Or       (* boolean or *).
      (**[]*)

      Inductive s : Type :=
      | SSkip (i : tags_t)                              (* skip, useful for
                                                           small-step semantics *)
      | SVardecl (type : E.t)
                 (x : string) (i : tags_t)       (* Variable declaration. *)
      | SAssign (type : E.t) (lhs rhs : E.e tags_t)
                (i : tags_t)                            (* assignment *)
      | SUop (dst_type : E.t)
              (op: uop)
              (arg: E.e tags_t)
              (dst: string)
              (i : tags_t)                              (* apply uop *)
      | SBop (dst_type : E.t)
              (op: bop)
              (le : E.e tags_t)
              (re : E.e tags_t )
              (dst : string)
              (i : tags_t)                                (* apply bop *)
      | SBitAssign (dst_type : E.t)
                    (dst : string)
                    (width : positive)
                    (val : Z)
                    (i : tags_t)                        (* assign a bit string value to a variable *)
      | SIntAssign (dst_type : E.t)
                    (dst : string)
                    (width : positive)
                    (val : Z)
                    (i : tags_t)                        (* assign an int value to a variable *)
      | SSlice (n : E.e tags_t )
                (n_type : E.t)
                (hi lo : positive)
                (dst : string)
                (i : tags_t)                             (* bit slicing *)   
      | SCast (type : E.t)
              (arg: E.e tags_t)
              (dst: E.e tags_t)
              (i: tags_t)                                 (* casting *)
      | STuple (es : list (E.e tags_t)) 
                (dst : E.e tags_t)
                (i : tags_t)
      | SStruct (fields : F.fs string (E.t* (E.e tags_t)))
                (dst : (E.e  tags_t))
                (i : tags_t)
      | SHeader (fields : F.fs string (E.t * (E.e tags_t)))
                (dst : E.e tags_t)
                (valid : E.e tags_t)
                (i : tags_t)
      | SHeaderStack (fields : F.fs string E.t)
                      (headers : list (E.e tags_t))
                      (size : positive)
                      (next_index : Z)
                      (dst : E.e tags_t)
                      (i : tags_t)
      | SHeaderStackAccess (stack : E.e tags_t)
                           (index : Z)
                           (dst : E.e tags_t)
                           (i : tags_t)
      | SConditional (guard_type : E.t)
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
      | SReturnFruit (t : E.t)
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

    Inductive state : Set :=
    | STStart | STAccept | STReject | STName (st : string).
    (**[]*)

    (** Select expression pattern.
        Corresponds to keySet expressions in p4. *)
    Inductive pat : Type :=
    | PATWild
    | PATMask (p1 p2 : pat)
    | PATRange (p1 p2 : pat)
    | PATBit (w : positive) (n : Z)
    | PATInt (w : positive) (n : Z)
    | PATTuple (ps : list pat).
    (**[]*)

    Section Parsers.
      Variable (tags_t : Type).

      (** Parser expressions, which evaluate to state names *)
      Inductive e : Type :=
      | PGoto (st : state) (i : tags_t) (* goto state [st] *)
      | PSelect (exp : E.e tags_t) (default : e)
                (cases : F.fs pat e)
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
        | Table (key : list (E.t * E.e tags_t * E.matchkind))
                (actions : list string).
        (**[]*)

        (** Declarations that may occur within Controls. *)
        (* TODO, this is a stub. *)
        Inductive d : Type :=
        | CDAction (a : string)
                   (signature : E.params)
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
                     (i : tags_t) (* constructor [C]
                                     with constructor [args]
                                     makes instance [x]. *)
      | TPExtern (e : string)
                 (cparams : E.constructor_params)
                 (methods : F.fs string E.arrowT)
                 (i : tags_t) (* extern declarations *)
      | TPControl (c : string)
                  (cparams : E.constructor_params) (* constructor params *)
                  (params : E.params) (* apply block params *)
                  (body : C.d tags_t) (apply_blk : S.s tags_t) (i : tags_t)
      | TPParser (p : string)
                 (cparams : E.constructor_params) (* constructor params *)
                 (params : E.params)           (* invocation params *)
                 (start : P.state_block tags_t) (* start state *)
                 (states : F.fs string (P.state_block tags_t)) (* parser states *)
                 (i : tags_t) (* parser declaration *)
      | TPFunction (f : string) (signature : E.arrowT) (body : S.s tags_t)
                   (i : tags_t) (* function/method declaration *)
      | TPPackage (p : string)
                  (cparams : E.constructor_params) (* constructor params *)
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
