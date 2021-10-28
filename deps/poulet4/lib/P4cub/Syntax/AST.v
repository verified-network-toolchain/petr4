Require Import Coq.PArith.BinPosDef Coq.PArith.BinPos
        Coq.ZArith.BinIntDef Coq.ZArith.BinInt Poulet4.P4Arith
        Coq.Classes.EquivDec Coq.Program.Program.
Require Export Poulet4.P4cub.Syntax.P4Field.
Require Coq.Logic.Eqdep_dec.

(** * P4cub AST *)

Module F := Field.

(** Function call parameters/arguments. *)
Inductive paramarg (A B : Type) : Type :=
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
  
  Inductive uop : Set :=
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
    | EBit (width : positive) (val : Z) (i : tags_t) (* unsigned integers *)
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
    | EMatchKind (mk : matchkind) (i : tags_t)       (* matchkind literals *)
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
    Inductive constructor_arg : Type :=
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
  Arguments EMatchKind {tags_t}.
  Arguments EHeaderStack {_}.
  Arguments EHeaderStackAccess {_}.
  Arguments CAExpr {_}.
  Arguments CAName {_}.
End Expr.

(** Statement Grammar *)
Module Stmt.
  Module E := Expr.

  Section Statements.
    Variable (tags_t : Type).

    (** Header Stack Operations. *)
    Inductive hsop : Set := HSPush | HSPop.

    Inductive s : Type :=
    | SSkip (i : tags_t)                              (* skip/no-op *)
    | SVardecl (x : string) (expr : either E.t (E.e tags_t))
               (i : tags_t)                           (* variable declaration. *)
    | SAssign (lhs rhs : E.e tags_t) (i : tags_t)     (* assignment *)
    | SConditional (guard : E.e tags_t)
                   (tru_blk fls_blk : s) (i : tags_t) (* conditionals *)
    | SSeq (s1 s2 : s) (i : tags_t)                   (* sequences *)
    | SBlock (blk : s)                                (* blocks *)
    | SExternMethodCall (extern_name method_name : string)
                        (typ_args : list E.t)
                        (args : E.arrowE tags_t)
                        (i : tags_t)                  (* extern method calls *)
    | SFunCall (f : string)
               (typ_args : list E.t)
               (args : E.arrowE tags_t) (i : tags_t)  (* function call *)
    | SActCall (action_name : string)
               (args : E.args tags_t) (i : tags_t)    (* action call *)
    | SReturn (e : option (E.e tags_t))
              (i : tags_t)                            (* return statement *)
    | SExit (i : tags_t)                              (* exit statement *)
    | SInvoke (table_name : string) (i : tags_t)      (* table invocation *)
    | SApply (control_instance_name : string)
             (ext_args : F.fs string string)
             (args : E.args tags_t) (i : tags_t)      (* control apply statements *)
    | SHeaderStackOp (hdr_stk_name : string) (s : hsop)
                     (n : positive) (i : tags_t)      (* push or pop statements *)
    | SSetValidity (hdr : E.e tags_t) (validity : bool)
                   (i : tags_t)                       (* set valid or set invalid *).
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
  Module E := Expr.
  Module S := Stmt.

  (** Labels for parser-states. *)
  Inductive state : Set :=
  | STStart              (* start state *)
  | STAccept             (* accept state *)
  | STReject             (* reject state *)
  | STName (st : string) (* user-defined state *).
  (**[]*)

  (** Select expression pattern.
      Corresponds to keySet expressions in p4. *)
  Inductive pat : Type :=
  | PATWild                             (* wild-card/anything pattern *)
  | PATMask  (p1 p2 : pat)              (* mask pattern *)
  | PATRange (p1 p2 : pat)              (* range pattern *)
  | PATBit (width : positive) (val : Z) (* unsigned-int pattern *)
  | PATInt (width : positive) (val : Z) (* signed-int pattern *)
  | PATTuple (ps : list pat)            (* tuple pattern *).
  (**[]*)

  Section Parsers.
    Variable (tags_t : Type).

    (** Parser expressions, which evaluate to state names *)
    Inductive e : Type :=
    | PGoto (st : state) (i : tags_t) (* goto state [st] *)
    | PSelect (discriminee : E.e tags_t)
              (default : e) (cases : F.fs pat e)
              (i : tags_t)           (* select expressions,
                                        where "default" is
                                        the catch-all case *).
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

(** Controls *)
Module Control.
  Module E := Expr.
  Module S := Stmt.

  Section ControlDecls.
    Variable (tags_t : Type).
    
    (** Table. *)
    Inductive table : Type :=
    | Table (key : list (E.t * E.e tags_t * E.matchkind))
            (actions : list string).
    (**[]*)
    
    (** Declarations that may occur within Controls. *)
    Inductive d : Type :=
    | CDAction (action_name : string)
               (signature : E.params) (body : S.s tags_t)
               (i : tags_t)               (* action declaration *)
    | CDTable (table_name : string)
              (body : table) (i : tags_t) (* table declaration *)
    | CDSeq (d1 d2 : d) (i : tags_t)      (* sequence of declarations *).
    (**[]*)
  End ControlDecls.
  
  Arguments Table {_}.
  Arguments CDAction {_}.
  Arguments CDTable {_}.
  Arguments CDSeq {_}.
End Control.

(** Top-Level Declarations *)
Module TopDecl.
  Module E := Expr.
  Module S := Stmt.
  Module C := Control.
  Module P := Parser.

  Section TopDeclarations.
    Variable (tags_t : Type).

    (** Top-level declarations. *)
    Inductive d : Type :=
    | TPInstantiate (constructor_name instance_name : string)
                    (type_args : list E.t)
                    (cargs : E.constructor_args tags_t)
                    (i : tags_t) (* instantiations *)
    | TPExtern (extern_name : string)
               (type_params : list string)
               (cparams : E.constructor_params)
               (methods : F.fs string (list string * E.arrowT))
               (i : tags_t) (* extern declarations *)
    | TPControl (control_name : string)
                (cparams : E.constructor_params) (* constructor params *)
                (eparams : F.fs string string)   (* runtime extern params *)
                (params : E.params)              (* apply block params *)
                (body : C.d tags_t) (apply_blk : S.s tags_t)
                (i : tags_t) (* control declarations *)
    | TPParser (parser_name : string)
               (cparams : E.constructor_params) (* constructor params *)
               (eparams : F.fs string string)   (* runtime extern params *)
               (params : E.params)              (* invocation params *)
               (start : P.state_block tags_t)   (* start state *)
               (states : F.fs string (P.state_block tags_t)) (* parser states *)
               (i : tags_t)  (* parser declaration *)
    | TPFunction (function_name : string)
                 (type_params : list string)
                 (signature : E.arrowT) (body : S.s tags_t)
                 (i : tags_t)(* function/method declaration *)
    | TPPackage (package_name : string)
                (type_params : list string)
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
