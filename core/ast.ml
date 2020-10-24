module P4Int = Petr4.Types.P4Int

type dir = DIn | DOut | DInOut | DNone

type id = string

type match_kind = MK of id

(** Expressions. *)
module Expr : sig
  (* Expression types. *)
  type t =
    | TInteger
    | TBitstring of int
    | TError
    | TMatchKind
    | TRecord of (id * t) list
    | THeader of (id * t) list
    | TTypeName of id

  (** Unary operations. *)
  type uop =
    | Not
    | BitNot
    | UMinus

  (** Binary operations.
    The "Sat" suffix denotes
    saturating arithmetic:
    where there is no overflow.
  *)
  type bop =
    | Plus
    | PlusSat
    | Minus
    | MinusSat
    | Shl
    | Shr
    | Le
    | Ge
    | Lt
    | Gt
    | Eq
    | NotEq
    | BitAnd
    | BitXor
    | BitOr
    | PlusPlus
    | And
    | Or

  (** Expressions. *)
  type e =
    | Integer of int
    | Bitstring of {
      width : int;
      value : Bigint.t;
    }
    | Var of id
    | Uop of {
      op : uop;
      expr : e
    }
    | Bop of {
      op : bop;
      lhs : e;
      rhs : e;
    }
    | Cast of {
      typ : t;
      expr : e;
    }
    | Record of (id * e) list
    | ExprMember of {
      expr : e;
      mem : id;
    }
    | Error of id
    (* Extern or action calls. *)
    | Call of {
      callee : e;
      args : (dir * e) list; }
end = struct
  type t =
    | TInteger
    | TBitstring of int
    | TError
    | TMatchKind
    | TRecord of (id * t) list
    | THeader of (id * t) list
    | TTypeName of id

    (** Unary operations. *)
    type uop =
      | Not
      | BitNot
      | UMinus

    (** Binary operations.
      The "Sat" suffix denotes
      saturating arithmetic:
      where there is no overflow.
    *)
    type bop =
      | Plus
      | PlusSat
      | Minus
      | MinusSat
      | Shl
      | Shr
      | Le
      | Ge
      | Lt
      | Gt
      | Eq
      | NotEq
      | BitAnd
      | BitXor
      | BitOr
      | PlusPlus
      | And
      | Or

  type e =
    | Integer of int
    | Bitstring of {
      width : int;
      value : Bigint.t; }
    | Var of id
    | Uop of {
      op : uop;
      expr : e; }
    | Bop of {
      op : bop;
      lhs : e;
      rhs : e; }
    | Cast of {
      typ : t;
      expr : e; }
    | Record of (id * e) list
    | ExprMember of {
      expr : e;
      mem : id; }
    | Error of id
    | Call of {
      callee : e;
      args : (dir * e) list; }
end

(** Statements.  *)
module Stmt : sig
  type s =
    | Assign of {
      lhs : Expr.e;
      rhs : Expr.e; }
    | Conditional of {
      guard : Expr.e;
      t : s;
      f : s; }
    | Block of s list
    | Exit
    | Return of Expr.e option
    | VarDecl of {
      typ : Expr.t;
      var : id;
      expr : Expr.e; }
    | MethodCall of {
      callee : Expr.e;
      args : Expr.e list }
end = struct
  type s =
    | Assign of {
      lhs : Expr.e;
      rhs : Expr.e; }
    | Conditional of {
      guard : Expr.e;
      t : s;
      f : s; }
    | Block of s list
    | Exit
    | Return of Expr.e option
    | VarDecl of {
      typ : Expr.t;
      var : id;
      expr : Expr.e; }
    | MethodCall of {
      callee : Expr.e;
      args : Expr.e list }
end

(** Controls  *)
module Control : sig
  (** Control types. *)
  type t = {
    type_params: id list;
    parameters: (dir * Expr.t) list; }

  (** Table definition. *)
  type table = {
    name: id;
    key: (id * match_kind) list;
    actions: id list;
    default_action: id option;
    size: P4Int.t option; }

  (** Action definition. *)
  type action = {
    name: id;
    (* Compilation will perform
      closure-conversion to
      remove partial applications. *)
    params: (dir * Expr.t) list;
    body: Stmt.s list; }

    (** Control declarations. *)
    type c = {
      actions: action list;
      tables: table list;
      apply: Stmt.s list }
end = struct
  (** Control types. *)
  type t = {
    type_params: id list;
    parameters: (dir * Expr.t) list; }

  (** Table definition. *)
  type table = {
    name: id;
    key: (id * match_kind) list;
    actions: id list;
    default_action: id option;
    size: P4Int.t option; }

  (** Action definition. *)
  type action = {
    name: id;
    (* Compilation will perform
      closure-conversion to
      remove partial applications. *)
    params: (dir * Expr.t) list;
    body: Stmt.s list; }

    (** Control declarations. *)
    type c = {
      actions: action list;
      tables: table list;
      apply: Stmt.s list }
end

(** The top-level program. *)
module Program : sig
  (** Variable declaration.  *)
  type var_decl = {
    var : id;
    typ : Expr.t;
    expr :  Expr.e; }

  (* Instantiations. *)
  type instantiation = {
    typ_name : id;
    args : Expr.e list;
    var : id; }

  (** Type declaration. *)
  type typ_decl = {
    typ : Expr.t;
    name : id; }

  (** The program. *)
  type p = {
    variables: var_decl list;
    instantiations: instantiation list;
    errors: id list;
    match_kinds: match_kind list;
    types: typ_decl list;
    externs: unit list (* TODO *);
    controls: Control.c list;
    package: unit (* TODO *); }
end = struct
  (** Variable declaration.  *)
  type var_decl = {
    var : id;
    typ : Expr.t;
    expr :  Expr.e; }

  (* Instantiations. *)
  type instantiation = {
    typ_name : id;
    args : Expr.e list;
    var : id; }

  (** Type declaration. *)
  type typ_decl = {
    typ : Expr.t;
    name : id; }

  (** The program. *)
  type p = {
    variables: var_decl list;
    instantiations: instantiation list;
    errors: id list;
    match_kinds: match_kind list;
    types: typ_decl list;
    externs: unit list (* TODO *);
    controls: Control.c list;
    package: unit (* TODO *); }
end

(**
How to get there?

1) Global substitution of constants and typdefs (optional). Result
    should be a valid P4 program passing our type-checker.
2) Collapse error and matchkind declarations and lift them to the top of the
    program. Result should be a valid P4 program passing our type-checker
    (for convenience only; optional).
3) Inline nested parser/control declarations by lifting parser states from
    sub-parses, inlining apply blocks of sub-controls, and lifting local
    declarations from sub-parsers and sub-controls. Result should be a valid
    P4 program passing our type-checker.
4) For the remaining parsers and controls, lift the local declarations to
    global space. Result should be expressable in our P4 AST, but may not
    pass the type-checker due to restrictions on various kinds of declarations.
    We may be able to run a subset of the type-checker.
5) Inline function calls, and perform closure-conversion
    and lambda lifting for actions.
6) Unroll parsers, expressing them as controls.
7) Translation from P4 into the P4 core language described above. Most of the
    transformations are related to expressing some of P4's more complex data
    types in terms of headers and structs.
8)  Inlining method calls and correctly removing copy-in/copy-out.
Notes :
- Keep externs in the syntax in some simplified form.
- Keep architectures/packages abstract; translation is not target-dependent
- Keep functions & copy-in/copy out; could remove function calls and
  copy-in/copy-out, but it would be rather non-trivial. Idea: introduce
  e-seq and lower.
*)
