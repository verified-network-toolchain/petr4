Require Import Coq.PArith.BinPosDef Coq.PArith.BinPos
        Coq.ZArith.BinIntDef Coq.ZArith.BinInt
        Coq.Classes.EquivDec Coq.Program.Program.
Require Export Poulet4.P4cub.Syntax.P4Field.
Require Coq.Logic.Eqdep_dec.
Import String.
(** * P4cub AST *)

Module F := Field.

(** Function call parameters/arguments. *)
Variant paramarg (A B : Type) : Type :=
| PAIn (a : A)
| PAOut (b : B)
| PAInOut (b : B)
| PADirLess (a : A).

Arguments PAIn {_} {_}.
Arguments PAOut {_} {_}.
Arguments PAInOut {_} {_}.
Arguments PADirLess {_} {_}.

Definition paramarg_map {A B C D : Type}
           (f : A -> C) (g : B -> D)
           (pa : paramarg A B) : paramarg C D :=
  match pa with
  | PAIn a => PAIn (f a)
  | PAOut b => PAOut (g b)
  | PAInOut b => PAInOut (g b)
  | PADirLess a => PADirLess (f a)
  end.
(**[]*)

(** A predicate on a [paramarg]. *)
Definition pred_paramarg {A B : Type}
           (PA : A -> Prop) (PB : B -> Prop) (pa : paramarg A B) : Prop :=
  match pa with
  | PAIn a | PADirLess a => PA a
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
  | PADirLess a1, PADirLess a2 
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
Record arrow (K A B R : Type) : Type :=
  { paramargs : F.fs K (paramarg A B);
    rtrns : option R }.
(**[]*)

Arguments paramargs {_} {_} {_} {_}.
Arguments rtrns {_} {_} {_} {_}.

(** * Expression Grammar *)
Module Expr.
  Section P4Types.
    (** Expression types. *)
    Inductive t : Type :=
    | TBool                            (* bool *)
    | TBit (width : N)                 (* unsigned integers *)
    | TInt (width : positive)          (* signed integers *)
    | TError                           (* the error type *)
    | TTuple (types : list t)          (* tuple type *)
    | TStruct (fields : F.fs string t) (* the struct and struct type *)
    | THeader (fields : F.fs string t) (* the header type *)
    | THeaderStack (fields : F.fs string t)
                   (size : positive)   (* header stack type *)
    | TVar (type_name : string)        (* type variables *).
    (**[]*)
    
    (** Function parameters. *)
    Definition params : Type := F.fs string (paramarg t t).
    
    (** Function types. *)
    Definition arrowT : Type := arrow string t t t.
    
    (** Constructor Types. *)
    Inductive ct : Type :=
    | CTType (type : t)                   (* expression types *)
    | CTControl (cparams : F.fs string ct)
                (runtime_extern_params : F.fs string string)
                (parameters : params)     (* control types *)
    | CTParser (cparams : F.fs string ct)
               (runtime_extern_params : F.fs string string)
               (parameters : params)      (* parser types *)
    | CTPackage (cparams : F.fs string ct) (* package types *)
    | CTExtern (extern_name : string).
    (**[]*)
    
    Definition constructor_params : Type := F.fs string ct.
  End P4Types.
  
  Variant uop : Set :=
  | Not        (* boolean negation *)
  | BitNot     (* bitwise negation *)
  | UMinus     (* integer negation *)
  | IsValid    (* check header validity *)
  | SetValid   (* set a header valid *)
  | SetInValid (* set a header invalid *)
  | NextIndex  (* get element at [nextIndex] from a header stack *)
  | Size       (* get a header stack's size *).
  (**[]*)
  
  (** Binary operations.
      The "Sat" suffix denotes
      saturating arithmetic:
      where there is no overflow. *)
  Variant bop : Set :=
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
  
  (** Default matchkinds. *)
  Variant matchkind : Set :=
  | MKExact
  | MKTernary
  | MKLpm.
  (**[]*)
  
  Section Expressions.
    Variable (tags_t : Type).

    (* AST parameterized by variable type.
       variable type needs decidable equality (or an order).
       order is faster then membership checking. *)
    
    (** Expressions annotated with types,
        unless the type is obvious. *)
    Inductive e : Type :=
    | EBool (b : bool) (i : tags_t)                     (* booleans *)
    | EBit (width : N) (val : Z) (i : tags_t)        (* unsigned integers *)
    | EInt (width : positive) (val : Z) (i : tags_t) (* signed integers *)
    | EVar (type : t) (x : string) (i : tags_t)      (* variables *)
    | ESlice (arg : e)
             (hi lo : positive) (i : tags_t)         (* bit-slicing *)
    | ECast (type : t) (arg : e) (i : tags_t)        (* explicit casts *)
    | EUop (result_type : t) (op : uop)
           (arg : e) (i : tags_t)                    (* unary operations *)
    | EBop (result_type : t) (op : bop)
           (lhs rhs : e) (i : tags_t)                (* binary operations *)
    | ETuple (es : list e) (i : tags_t)              (* tuples *)
    | EStruct (fields : F.fs string e) (i : tags_t)  (* struct literals *)
    | EHeader (fields : F.fs string e)
              (valid : e) (i : tags_t)               (* header literals *)
    | EExprMember (result_type : t) (mem : string)
                  (arg : e) (i : tags_t)             (* member-expressions *)
    | EError (err : option string) (i : tags_t)      (* error literals *)
    | EHeaderStack (fields : F.fs string t)
                   (headers : list e)                (* header stack literals *)
                   (next_index : Z) (i : tags_t)     (*unique to p4cub *)
    | EHeaderStackAccess (result_hdr_type : F.fs string t)
                         (stk : e)
                         (index : Z) (i : tags_t)    (* header stack indexing *).
    (**[]*)
    
    (** Function call arguments. *)
    Definition args : Type :=
      F.fs string (paramarg e e).
    (**[]*)
    
    (** Function call. *)
    Definition arrowE : Type :=
      arrow string e e e.
    (**[]*)
    
    (** Constructor arguments. *)
    Variant constructor_arg : Type :=
    | CAExpr (expr : e)   (* plain expression *)
    | CAName (x : string) (* name of parser, control, package, or extern *).
    (**[]*)
    
    Definition constructor_args : Type := F.fs string constructor_arg.
  End Expressions.

  Arguments EBool {tags_t}.
  Arguments EBit {_}.
  Arguments EInt {_}.
  Arguments EVar {tags_t}.
  Arguments ESlice {_}.
  Arguments ECast {_}.
  Arguments EUop {tags_t}.
  Arguments EBop {tags_t}.
  Arguments ETuple {_}.
  Arguments EStruct {tags_t}.
  Arguments EHeader {_}.
  Arguments EExprMember {tags_t}.
  Arguments EError {tags_t}.
  Arguments EHeaderStack {_}.
  Arguments EHeaderStackAccess {_}.
  Arguments CAExpr {_}.
  Arguments CAName {_}.
End Expr.

(** Statement Grammar *)
Module Stmt.
  Section Statements.
    Variable (tags_t : Type).

    (** Header Stack Operations. *)
    Variant hsop : Set := HSPush | HSPop.

    Inductive s : Type :=
    | SSkip (i : tags_t)                         (* skip/no-op *)
    | SVardecl (x : string) (expr : Expr.t + Expr.e tags_t)
               (i : tags_t)                      (* variable declaration. *)
    | SAssign (lhs rhs : Expr.e tags_t) (i : tags_t)     (* assignment *)
    | SConditional (guard : Expr.e tags_t)
                   (tru_blk fls_blk : s) (i : tags_t) (* conditionals *)
    | SSeq (s1 s2 : s) (i : tags_t)                   (* sequences *)
    | SBlock (blk : s)                                (* blocks *)
    | SExternMethodCall (extern_name method_name : string)
                        (typ_args : list Expr.t)
                        (args : Expr.arrowE tags_t)
                        (i : tags_t)             (* extern method calls *)
    | SFunCall (f : string)
               (typ_args : list Expr.t)
               (args : Expr.arrowE tags_t) (i : tags_t) (* function call *)
    | SActCall (action_name : string)
               (args : Expr.args tags_t) (i : tags_t) (* action call *)
    | SReturn (e : option (Expr.e tags_t))
              (i : tags_t)                          (* return statement *)
    | SExit (i : tags_t)                            (* exit statement *)
    | SInvoke (table_name : string) (i : tags_t)    (* table invocation *)
    | SApply (instance_name : string)
             (ext_args : F.fs string string)
             (args : Expr.args tags_t)
             (i : tags_t) (* apply statements *)
    | SHeaderStackOp (hdr_stk_name : string) (o : hsop)
                     (n : positive) (i : tags_t)  (* push/pop statements *)
    | SSetValidity (hdr : Expr.e tags_t) (validity : bool)
                   (i : tags_t)               (* set valid or set invalid *).
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
  Arguments SReturn {_}.
  Arguments SExit {_}.
  Arguments SApply {_}.
  Arguments SInvoke {_}.
  Arguments SHeaderStackOp {_}.
  Arguments SSetValidity {_}.
End Stmt.

(** Parsers *)
Module Parser.
  (** Labels for parser-states. *)
  Variant state : Set :=
  | STStart              (* start state *)
  | STAccept             (* accept state *)
  | STReject             (* reject state *)
  | STName (st : string) (* user-defined state *).
  (**[]*)

  (** Select expression pattern.
      Corresponds to keySet expressions in p4. *)
  Inductive pat : Type :=
  | PATWild                             (* wild-card/anything pattern *)
  | PATMask (p1 p2 : pat)               (* mask pattern *)
  | PATRange (p1 p2 : pat)              (* range pattern *)
  | PATBit (width : N) (val : Z)        (* unsigned-int pattern *)
  | PATInt (width : positive) (val : Z) (* signed-int pattern *)
  | PATTuple (ps : list pat).           (* tuple pattern *)
  (**[]*)

  Section Parsers.
    Variable (tags_t : Type).

    (** Parser expressions, which evaluate to state names *)
    Inductive e : Type :=
    | PGoto (st : state) (i : tags_t) (* goto state [st] *)
    | PSelect (discriminee : Expr.e tags_t)
              (default : e) (cases : F.fs pat e)
              (i : tags_t)           (* select expressions,
                                        where "default" is
                                        the catch-all case *).
    (**[]*)

    (** Parser State Blocks. *)
    Record state_block : Type :=
      { stmt : Stmt.s tags_t; trans : e }.
    (**[]*)
  End Parsers.

  Arguments stmt {_}.
  Arguments trans {_}.
  Arguments PGoto {_}.
  Arguments PSelect {_}.
End Parser.

(** Controls *)
Module Control.
  Section ControlDecls.
    Variable (tags_t : Type).
    
    (** Table. *)
    Record table : Type :=
      { table_key : list (Expr.e tags_t * Expr.matchkind); 
        table_actions : list string }.
    (**[]*)
    
    (** Declarations that may occur within Controls. *)
    Inductive d : Type :=
    | CDAction (action_name : string)
               (signature : Expr.params) (body : Stmt.s tags_t)
               (i : tags_t)               (* action declaration *)
    | CDTable (table_name : string)
              (body : table) (i : tags_t) (* table declaration *)
    | CDSeq (d1 d2 : d) (i : tags_t)      (* sequence of declarations *).
    (**[]*)
  End ControlDecls.

  Arguments table_key {_}.
  Arguments table_actions {_}.
  Arguments CDAction {_}.
  Arguments CDTable {_}.
  Arguments CDSeq {_}.
End Control.

(** Top-Level Declarations *)
Module TopDecl.
  Section TopDeclarations.
    Variable (tags_t : Type).

    (** Top-level declarations. *)
    Inductive d : Type :=
    | TPInstantiate (constructor_name instance_name : string)
                    (type_args : list Expr.t)
                    (cargs : Expr.constructor_args tags_t)
                    (i : tags_t) (* instantiations *)
    | TPExtern (extern_name : string)
               (type_params : list string)
               (cparams : Expr.constructor_params)
               (methods : F.fs string (list string * Expr.arrowT))
               (i : tags_t) (* extern declarations *)
    | TPControl (control_name : string)
                (cparams : Expr.constructor_params) (* constructor params *)
                (eparams : F.fs string string)   (* runtime extern params *)
                (params : Expr.params)              (* apply block params *)
                (body : Control.d tags_t) (apply_blk : Stmt.s tags_t)
                (i : tags_t) (* control declarations *)
    | TPParser (parser_name : string)
               (cparams : Expr.constructor_params) (* constructor params *)
               (eparams : F.fs string string)   (* runtime extern params *)
               (params : Expr.params)              (* invocation params *)
               (start : Parser.state_block tags_t)   (* start state *)
               (states : F.fs string (Parser.state_block tags_t)) (* parser states *)
               (i : tags_t)  (* parser declaration *)
    | TPFunction (function_name : string)
                 (type_params : list string)
                 (signature : Expr.arrowT) (body : Stmt.s tags_t)
                 (i : tags_t)(* function/method declaration *)
    | TPSeq (d1 d2 : d) (i : tags_t).
    (**[]*)
  End TopDeclarations.

  Arguments TPInstantiate {_}.
  Arguments TPExtern {_}.
  Arguments TPControl {_}.
  Arguments TPParser {_}.
  Arguments TPFunction {_}.
  Arguments TPSeq {_}.
End TopDecl.
