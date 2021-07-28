open AST0
open BinNums
open Datatypes
open EquivDec
open EquivUtil

module P :
 sig
  module F :
   sig
    type ('k, 'v) f = 'k * 'v

    type ('k, 'v) fs = ('k, 'v) f list

    val key : ('a1, 'a2) f -> 'a1

    val value : ('a1, 'a2) f -> 'a2

    val keys : ('a1, 'a2) fs -> 'a1 list

    val values : ('a1, 'a2) fs -> 'a2 list

    val filter : ('a2 -> bool) -> ('a1, 'a2) fs -> ('a1, 'a2) fs

    val map : ('a2 -> 'a3) -> ('a1, 'a2) fs -> ('a1, 'a3) fs

    val fold : ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1, 'a2) fs -> 'a3 -> 'a3

    val find_value : ('a1 -> bool) -> ('a1, 'a2) fs -> 'a2 option

    val get : 'a1 coq_EqDec -> 'a1 -> ('a1, 'a2) fs -> 'a2 option

    val get_index_rec :
      'a1 coq_EqDec -> 'a1 -> ('a1, 'a2) fs -> nat -> nat option

    val get_index : 'a1 coq_EqDec -> 'a1 -> ('a1, 'a2) fs -> nat option

    val update : 'a1 coq_EqDec -> 'a1 -> 'a2 -> ('a1, 'a2) fs -> ('a1, 'a2) fs

    val eqb_f :
      'a1 coq_EqDec -> ('a2 -> 'a2 -> bool) -> ('a1, 'a2) f -> ('a1, 'a2) f
      -> bool

    val eqb_fs :
      'a1 coq_EqDec -> ('a2 -> 'a2 -> bool) -> ('a1, 'a2) fs -> ('a1, 'a2) fs
      -> bool

    module RelfEquiv :
     sig
     end

    module FieldTactics :
     sig
     end
   end

  type ('a, 'b) paramarg = ('a, 'b) P4cub.paramarg =
  | PAIn of 'a
  | PAOut of 'b
  | PAInOut of 'b

  val paramarg_rect :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) paramarg -> 'a3

  val paramarg_rec :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) paramarg -> 'a3

  val paramarg_map :
    ('a1 -> 'a3) -> ('a2 -> 'a4) -> ('a1, 'a2) paramarg -> ('a3, 'a4) paramarg

  type ('k, 'a, 'b, 'r) arrow = ('k, 'a, 'b, 'r) P4cub.arrow =
  | Arrow of ('k, ('a, 'b) paramarg) F.fs * 'r option

  val arrow_rect :
    (('a1, ('a2, 'a3) paramarg) F.fs -> 'a4 option -> 'a5) -> ('a1, 'a2, 'a3,
    'a4) arrow -> 'a5

  val arrow_rec :
    (('a1, ('a2, 'a3) paramarg) F.fs -> 'a4 option -> 'a5) -> ('a1, 'a2, 'a3,
    'a4) arrow -> 'a5

  module Expr :
   sig
    type t = P4cub.Expr.t =
    | TBool
    | TBit of positive
    | TInt of positive
    | TError
    | TMatchKind
    | TTuple of t list
    | TStruct of (string, t) F.fs
    | THeader of (string, t) F.fs
    | THeaderStack of (string, t) F.fs * positive

    val t_rect :
      'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> 'a1 -> 'a1 -> (t list
      -> 'a1) -> ((string, t) F.fs -> 'a1) -> ((string, t) F.fs -> 'a1) ->
      ((string, t) F.fs -> positive -> 'a1) -> t -> 'a1

    val t_rec :
      'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> 'a1 -> 'a1 -> (t list
      -> 'a1) -> ((string, t) F.fs -> 'a1) -> ((string, t) F.fs -> 'a1) ->
      ((string, t) F.fs -> positive -> 'a1) -> t -> 'a1

    type params = (string, (t, t) paramarg) F.fs

    type arrowT = (string, t, t, t) arrow

    type ct = P4cub.Expr.ct =
    | CTType of t
    | CTControl of (string, ct) F.fs * params
    | CTParser of (string, ct) F.fs * params
    | CTPackage of (string, ct) F.fs
    | CTExtern of (string, ct) F.fs * (string, arrowT) F.fs

    val ct_rect :
      (t -> 'a1) -> ((string, ct) F.fs -> params -> 'a1) -> ((string, ct)
      F.fs -> params -> 'a1) -> ((string, ct) F.fs -> 'a1) -> ((string, ct)
      F.fs -> (string, arrowT) F.fs -> 'a1) -> ct -> 'a1

    val ct_rec :
      (t -> 'a1) -> ((string, ct) F.fs -> params -> 'a1) -> ((string, ct)
      F.fs -> params -> 'a1) -> ((string, ct) F.fs -> 'a1) -> ((string, ct)
      F.fs -> (string, arrowT) F.fs -> 'a1) -> ct -> 'a1

    type constructor_params = (string, ct) F.fs

    module TypeNotations :
     sig
     end

    type uop = P4cub.Expr.uop =
    | Not
    | BitNot
    | UMinus
    | IsValid
    | SetValid
    | SetInValid
    | NextIndex
    | Size
    | Push of positive
    | Pop of positive

    val uop_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (positive ->
      'a1) -> (positive -> 'a1) -> uop -> 'a1

    val uop_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (positive ->
      'a1) -> (positive -> 'a1) -> uop -> 'a1

    module UopNotations :
     sig
     end

    type bop = P4cub.Expr.bop =
    | Plus
    | PlusSat
    | Minus
    | MinusSat
    | Times
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

    val bop_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> bop ->
      'a1

    val bop_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> bop ->
      'a1

    module BopNotations :
     sig
     end

    type matchkind = P4cub.Expr.matchkind =
    | MKExact
    | MKTernary
    | MKLpm

    val matchkind_rect : 'a1 -> 'a1 -> 'a1 -> matchkind -> 'a1

    val matchkind_rec : 'a1 -> 'a1 -> 'a1 -> matchkind -> 'a1

    val coq_MatchKindEqDec : matchkind coq_EqDec

    module MatchkindNotations :
     sig
     end

    type 'tags_t e = 'tags_t P4cub.Expr.e =
    | EBool of bool * 'tags_t
    | EBit of positive * coq_Z * 'tags_t
    | EInt of positive * coq_Z * 'tags_t
    | EVar of t * string * 'tags_t
    | ESlice of 'tags_t e * t * positive * positive * 'tags_t
    | ECast of t * 'tags_t e * 'tags_t
    | EUop of uop * t * 'tags_t e * 'tags_t
    | EBop of bop * t * t * 'tags_t e * 'tags_t e * 'tags_t
    | ETuple of 'tags_t e list * 'tags_t
    | EStruct of (string, t * 'tags_t e) F.fs * 'tags_t
    | EHeader of (string, t * 'tags_t e) F.fs * 'tags_t e * 'tags_t
    | EExprMember of string * t * 'tags_t e * 'tags_t
    | EError of string option * 'tags_t
    | EMatchKind of matchkind * 'tags_t
    | EHeaderStack of (string, t) F.fs * 'tags_t e list * positive * 
       coq_Z * 'tags_t
    | EHeaderStackAccess of 'tags_t e * coq_Z * 'tags_t

    val e_rect :
      (bool -> 'a1 -> 'a2) -> (positive -> coq_Z -> 'a1 -> 'a2) -> (positive
      -> coq_Z -> 'a1 -> 'a2) -> (t -> string -> 'a1 -> 'a2) -> ('a1 e -> 'a2
      -> t -> positive -> positive -> 'a1 -> 'a2) -> (t -> 'a1 e -> 'a2 ->
      'a1 -> 'a2) -> (uop -> t -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (bop -> t ->
      t -> 'a1 e -> 'a2 -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> ('a1 e list -> 'a1
      -> 'a2) -> ((string, t * 'a1 e) F.fs -> 'a1 -> 'a2) -> ((string,
      t * 'a1 e) F.fs -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (string -> t -> 'a1 e
      -> 'a2 -> 'a1 -> 'a2) -> (string option -> 'a1 -> 'a2) -> (matchkind ->
      'a1 -> 'a2) -> ((string, t) F.fs -> 'a1 e list -> positive -> coq_Z ->
      'a1 -> 'a2) -> ('a1 e -> 'a2 -> coq_Z -> 'a1 -> 'a2) -> 'a1 e -> 'a2

    val e_rec :
      (bool -> 'a1 -> 'a2) -> (positive -> coq_Z -> 'a1 -> 'a2) -> (positive
      -> coq_Z -> 'a1 -> 'a2) -> (t -> string -> 'a1 -> 'a2) -> ('a1 e -> 'a2
      -> t -> positive -> positive -> 'a1 -> 'a2) -> (t -> 'a1 e -> 'a2 ->
      'a1 -> 'a2) -> (uop -> t -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (bop -> t ->
      t -> 'a1 e -> 'a2 -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> ('a1 e list -> 'a1
      -> 'a2) -> ((string, t * 'a1 e) F.fs -> 'a1 -> 'a2) -> ((string,
      t * 'a1 e) F.fs -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (string -> t -> 'a1 e
      -> 'a2 -> 'a1 -> 'a2) -> (string option -> 'a1 -> 'a2) -> (matchkind ->
      'a1 -> 'a2) -> ((string, t) F.fs -> 'a1 e list -> positive -> coq_Z ->
      'a1 -> 'a2) -> ('a1 e -> 'a2 -> coq_Z -> 'a1 -> 'a2) -> 'a1 e -> 'a2

    type 'tags_t args = (string, (t * 'tags_t e, t * 'tags_t e) paramarg) F.fs

    type 'tags_t arrowE =
      (string, t * 'tags_t e, t * 'tags_t e, t * 'tags_t e) arrow

    type 'tags_t constructor_arg = 'tags_t P4cub.Expr.constructor_arg =
    | CAExpr of 'tags_t e
    | CAName of string

    val constructor_arg_rect :
      ('a1 e -> 'a2) -> (string -> 'a2) -> 'a1 constructor_arg -> 'a2

    val constructor_arg_rec :
      ('a1 e -> 'a2) -> (string -> 'a2) -> 'a1 constructor_arg -> 'a2

    type 'tags_t constructor_args = (string, 'tags_t constructor_arg) F.fs

    module ExprNotations :
     sig
     end
   end

  module Stmt :
   sig
    module E :
     sig
      type t = P4cub.Expr.t =
      | TBool
      | TBit of positive
      | TInt of positive
      | TError
      | TMatchKind
      | TTuple of t list
      | TStruct of (string, t) F.fs
      | THeader of (string, t) F.fs
      | THeaderStack of (string, t) F.fs * positive

      val t_rect :
        'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> 'a1 -> 'a1 -> (t
        list -> 'a1) -> ((string, t) F.fs -> 'a1) -> ((string, t) F.fs ->
        'a1) -> ((string, t) F.fs -> positive -> 'a1) -> t -> 'a1

      val t_rec :
        'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> 'a1 -> 'a1 -> (t
        list -> 'a1) -> ((string, t) F.fs -> 'a1) -> ((string, t) F.fs ->
        'a1) -> ((string, t) F.fs -> positive -> 'a1) -> t -> 'a1

      type params = (string, (t, t) paramarg) F.fs

      type arrowT = (string, t, t, t) arrow

      type ct = P4cub.Expr.ct =
      | CTType of t
      | CTControl of (string, ct) F.fs * params
      | CTParser of (string, ct) F.fs * params
      | CTPackage of (string, ct) F.fs
      | CTExtern of (string, ct) F.fs * (string, arrowT) F.fs

      val ct_rect :
        (t -> 'a1) -> ((string, ct) F.fs -> params -> 'a1) -> ((string, ct)
        F.fs -> params -> 'a1) -> ((string, ct) F.fs -> 'a1) -> ((string, ct)
        F.fs -> (string, arrowT) F.fs -> 'a1) -> ct -> 'a1

      val ct_rec :
        (t -> 'a1) -> ((string, ct) F.fs -> params -> 'a1) -> ((string, ct)
        F.fs -> params -> 'a1) -> ((string, ct) F.fs -> 'a1) -> ((string, ct)
        F.fs -> (string, arrowT) F.fs -> 'a1) -> ct -> 'a1

      type constructor_params = (string, ct) F.fs

      module TypeNotations :
       sig
       end

      type uop = P4cub.Expr.uop =
      | Not
      | BitNot
      | UMinus
      | IsValid
      | SetValid
      | SetInValid
      | NextIndex
      | Size
      | Push of positive
      | Pop of positive

      val uop_rect :
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (positive ->
        'a1) -> (positive -> 'a1) -> uop -> 'a1

      val uop_rec :
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (positive ->
        'a1) -> (positive -> 'a1) -> uop -> 'a1

      module UopNotations :
       sig
       end

      type bop = P4cub.Expr.bop =
      | Plus
      | PlusSat
      | Minus
      | MinusSat
      | Times
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

      val bop_rect :
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> bop ->
        'a1

      val bop_rec :
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> bop ->
        'a1

      module BopNotations :
       sig
       end

      type matchkind = P4cub.Expr.matchkind =
      | MKExact
      | MKTernary
      | MKLpm

      val matchkind_rect : 'a1 -> 'a1 -> 'a1 -> matchkind -> 'a1

      val matchkind_rec : 'a1 -> 'a1 -> 'a1 -> matchkind -> 'a1

      val coq_MatchKindEqDec : matchkind coq_EqDec

      module MatchkindNotations :
       sig
       end

      type 'tags_t e = 'tags_t P4cub.Expr.e =
      | EBool of bool * 'tags_t
      | EBit of positive * coq_Z * 'tags_t
      | EInt of positive * coq_Z * 'tags_t
      | EVar of t * string * 'tags_t
      | ESlice of 'tags_t e * t * positive * positive * 'tags_t
      | ECast of t * 'tags_t e * 'tags_t
      | EUop of uop * t * 'tags_t e * 'tags_t
      | EBop of bop * t * t * 'tags_t e * 'tags_t e * 'tags_t
      | ETuple of 'tags_t e list * 'tags_t
      | EStruct of (string, t * 'tags_t e) F.fs * 'tags_t
      | EHeader of (string, t * 'tags_t e) F.fs * 'tags_t e * 'tags_t
      | EExprMember of string * t * 'tags_t e * 'tags_t
      | EError of string option * 'tags_t
      | EMatchKind of matchkind * 'tags_t
      | EHeaderStack of (string, t) F.fs * 'tags_t e list * positive * 
         coq_Z * 'tags_t
      | EHeaderStackAccess of 'tags_t e * coq_Z * 'tags_t

      val e_rect :
        (bool -> 'a1 -> 'a2) -> (positive -> coq_Z -> 'a1 -> 'a2) ->
        (positive -> coq_Z -> 'a1 -> 'a2) -> (t -> string -> 'a1 -> 'a2) ->
        ('a1 e -> 'a2 -> t -> positive -> positive -> 'a1 -> 'a2) -> (t ->
        'a1 e -> 'a2 -> 'a1 -> 'a2) -> (uop -> t -> 'a1 e -> 'a2 -> 'a1 ->
        'a2) -> (bop -> t -> t -> 'a1 e -> 'a2 -> 'a1 e -> 'a2 -> 'a1 -> 'a2)
        -> ('a1 e list -> 'a1 -> 'a2) -> ((string, t * 'a1 e) F.fs -> 'a1 ->
        'a2) -> ((string, t * 'a1 e) F.fs -> 'a1 e -> 'a2 -> 'a1 -> 'a2) ->
        (string -> t -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (string option -> 'a1
        -> 'a2) -> (matchkind -> 'a1 -> 'a2) -> ((string, t) F.fs -> 'a1 e
        list -> positive -> coq_Z -> 'a1 -> 'a2) -> ('a1 e -> 'a2 -> coq_Z ->
        'a1 -> 'a2) -> 'a1 e -> 'a2

      val e_rec :
        (bool -> 'a1 -> 'a2) -> (positive -> coq_Z -> 'a1 -> 'a2) ->
        (positive -> coq_Z -> 'a1 -> 'a2) -> (t -> string -> 'a1 -> 'a2) ->
        ('a1 e -> 'a2 -> t -> positive -> positive -> 'a1 -> 'a2) -> (t ->
        'a1 e -> 'a2 -> 'a1 -> 'a2) -> (uop -> t -> 'a1 e -> 'a2 -> 'a1 ->
        'a2) -> (bop -> t -> t -> 'a1 e -> 'a2 -> 'a1 e -> 'a2 -> 'a1 -> 'a2)
        -> ('a1 e list -> 'a1 -> 'a2) -> ((string, t * 'a1 e) F.fs -> 'a1 ->
        'a2) -> ((string, t * 'a1 e) F.fs -> 'a1 e -> 'a2 -> 'a1 -> 'a2) ->
        (string -> t -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (string option -> 'a1
        -> 'a2) -> (matchkind -> 'a1 -> 'a2) -> ((string, t) F.fs -> 'a1 e
        list -> positive -> coq_Z -> 'a1 -> 'a2) -> ('a1 e -> 'a2 -> coq_Z ->
        'a1 -> 'a2) -> 'a1 e -> 'a2

      type 'tags_t args =
        (string, (t * 'tags_t e, t * 'tags_t e) paramarg) F.fs

      type 'tags_t arrowE =
        (string, t * 'tags_t e, t * 'tags_t e, t * 'tags_t e) arrow

      type 'tags_t constructor_arg = 'tags_t P4cub.Expr.constructor_arg =
      | CAExpr of 'tags_t e
      | CAName of string

      val constructor_arg_rect :
        ('a1 e -> 'a2) -> (string -> 'a2) -> 'a1 constructor_arg -> 'a2

      val constructor_arg_rec :
        ('a1 e -> 'a2) -> (string -> 'a2) -> 'a1 constructor_arg -> 'a2

      type 'tags_t constructor_args = (string, 'tags_t constructor_arg) F.fs

      module ExprNotations :
       sig
       end
     end

    type 'tags_t s = 'tags_t P4cub.Stmt.s =
    | SSkip of 'tags_t
    | SVardecl of E.t * string * 'tags_t
    | SAssign of E.t * 'tags_t E.e * 'tags_t E.e * 'tags_t
    | SConditional of E.t * 'tags_t E.e * 'tags_t s * 'tags_t s * 'tags_t
    | SSeq of 'tags_t s * 'tags_t s * 'tags_t
    | SBlock of 'tags_t s
    | SExternMethodCall of string * string * 'tags_t E.arrowE * 'tags_t
    | SFunCall of string * 'tags_t E.arrowE * 'tags_t
    | SActCall of string * 'tags_t E.args * 'tags_t
    | SReturnVoid of 'tags_t
    | SReturnFruit of E.t * 'tags_t E.e * 'tags_t
    | SExit of 'tags_t
    | SInvoke of string * 'tags_t
    | SApply of string * 'tags_t E.args * 'tags_t

    val s_rect :
      ('a1 -> 'a2) -> (E.t -> string -> 'a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1
      E.e -> 'a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1 s -> 'a2 -> 'a1 s -> 'a2
      -> 'a1 -> 'a2) -> ('a1 s -> 'a2 -> 'a1 s -> 'a2 -> 'a1 -> 'a2) -> ('a1
      s -> 'a2 -> 'a2) -> (string -> string -> 'a1 E.arrowE -> 'a1 -> 'a2) ->
      (string -> 'a1 E.arrowE -> 'a1 -> 'a2) -> (string -> 'a1 E.args -> 'a1
      -> 'a2) -> ('a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1 -> 'a2) -> ('a1 ->
      'a2) -> (string -> 'a1 -> 'a2) -> (string -> 'a1 E.args -> 'a1 -> 'a2)
      -> 'a1 s -> 'a2

    val s_rec :
      ('a1 -> 'a2) -> (E.t -> string -> 'a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1
      E.e -> 'a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1 s -> 'a2 -> 'a1 s -> 'a2
      -> 'a1 -> 'a2) -> ('a1 s -> 'a2 -> 'a1 s -> 'a2 -> 'a1 -> 'a2) -> ('a1
      s -> 'a2 -> 'a2) -> (string -> string -> 'a1 E.arrowE -> 'a1 -> 'a2) ->
      (string -> 'a1 E.arrowE -> 'a1 -> 'a2) -> (string -> 'a1 E.args -> 'a1
      -> 'a2) -> ('a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1 -> 'a2) -> ('a1 ->
      'a2) -> (string -> 'a1 -> 'a2) -> (string -> 'a1 E.args -> 'a1 -> 'a2)
      -> 'a1 s -> 'a2

    module StmtNotations :
     sig
     end
   end

  module Parser :
   sig
    module E :
     sig
      type t = P4cub.Expr.t =
      | TBool
      | TBit of positive
      | TInt of positive
      | TError
      | TMatchKind
      | TTuple of t list
      | TStruct of (string, t) F.fs
      | THeader of (string, t) F.fs
      | THeaderStack of (string, t) F.fs * positive

      val t_rect :
        'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> 'a1 -> 'a1 -> (t
        list -> 'a1) -> ((string, t) F.fs -> 'a1) -> ((string, t) F.fs ->
        'a1) -> ((string, t) F.fs -> positive -> 'a1) -> t -> 'a1

      val t_rec :
        'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> 'a1 -> 'a1 -> (t
        list -> 'a1) -> ((string, t) F.fs -> 'a1) -> ((string, t) F.fs ->
        'a1) -> ((string, t) F.fs -> positive -> 'a1) -> t -> 'a1

      type params = (string, (t, t) paramarg) F.fs

      type arrowT = (string, t, t, t) arrow

      type ct = P4cub.Expr.ct =
      | CTType of t
      | CTControl of (string, ct) F.fs * params
      | CTParser of (string, ct) F.fs * params
      | CTPackage of (string, ct) F.fs
      | CTExtern of (string, ct) F.fs * (string, arrowT) F.fs

      val ct_rect :
        (t -> 'a1) -> ((string, ct) F.fs -> params -> 'a1) -> ((string, ct)
        F.fs -> params -> 'a1) -> ((string, ct) F.fs -> 'a1) -> ((string, ct)
        F.fs -> (string, arrowT) F.fs -> 'a1) -> ct -> 'a1

      val ct_rec :
        (t -> 'a1) -> ((string, ct) F.fs -> params -> 'a1) -> ((string, ct)
        F.fs -> params -> 'a1) -> ((string, ct) F.fs -> 'a1) -> ((string, ct)
        F.fs -> (string, arrowT) F.fs -> 'a1) -> ct -> 'a1

      type constructor_params = (string, ct) F.fs

      module TypeNotations :
       sig
       end

      type uop = P4cub.Expr.uop =
      | Not
      | BitNot
      | UMinus
      | IsValid
      | SetValid
      | SetInValid
      | NextIndex
      | Size
      | Push of positive
      | Pop of positive

      val uop_rect :
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (positive ->
        'a1) -> (positive -> 'a1) -> uop -> 'a1

      val uop_rec :
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (positive ->
        'a1) -> (positive -> 'a1) -> uop -> 'a1

      module UopNotations :
       sig
       end

      type bop = P4cub.Expr.bop =
      | Plus
      | PlusSat
      | Minus
      | MinusSat
      | Times
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

      val bop_rect :
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> bop ->
        'a1

      val bop_rec :
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> bop ->
        'a1

      module BopNotations :
       sig
       end

      type matchkind = P4cub.Expr.matchkind =
      | MKExact
      | MKTernary
      | MKLpm

      val matchkind_rect : 'a1 -> 'a1 -> 'a1 -> matchkind -> 'a1

      val matchkind_rec : 'a1 -> 'a1 -> 'a1 -> matchkind -> 'a1

      val coq_MatchKindEqDec : matchkind coq_EqDec

      module MatchkindNotations :
       sig
       end

      type 'tags_t e = 'tags_t P4cub.Expr.e =
      | EBool of bool * 'tags_t
      | EBit of positive * coq_Z * 'tags_t
      | EInt of positive * coq_Z * 'tags_t
      | EVar of t * string * 'tags_t
      | ESlice of 'tags_t e * t * positive * positive * 'tags_t
      | ECast of t * 'tags_t e * 'tags_t
      | EUop of uop * t * 'tags_t e * 'tags_t
      | EBop of bop * t * t * 'tags_t e * 'tags_t e * 'tags_t
      | ETuple of 'tags_t e list * 'tags_t
      | EStruct of (string, t * 'tags_t e) F.fs * 'tags_t
      | EHeader of (string, t * 'tags_t e) F.fs * 'tags_t e * 'tags_t
      | EExprMember of string * t * 'tags_t e * 'tags_t
      | EError of string option * 'tags_t
      | EMatchKind of matchkind * 'tags_t
      | EHeaderStack of (string, t) F.fs * 'tags_t e list * positive * 
         coq_Z * 'tags_t
      | EHeaderStackAccess of 'tags_t e * coq_Z * 'tags_t

      val e_rect :
        (bool -> 'a1 -> 'a2) -> (positive -> coq_Z -> 'a1 -> 'a2) ->
        (positive -> coq_Z -> 'a1 -> 'a2) -> (t -> string -> 'a1 -> 'a2) ->
        ('a1 e -> 'a2 -> t -> positive -> positive -> 'a1 -> 'a2) -> (t ->
        'a1 e -> 'a2 -> 'a1 -> 'a2) -> (uop -> t -> 'a1 e -> 'a2 -> 'a1 ->
        'a2) -> (bop -> t -> t -> 'a1 e -> 'a2 -> 'a1 e -> 'a2 -> 'a1 -> 'a2)
        -> ('a1 e list -> 'a1 -> 'a2) -> ((string, t * 'a1 e) F.fs -> 'a1 ->
        'a2) -> ((string, t * 'a1 e) F.fs -> 'a1 e -> 'a2 -> 'a1 -> 'a2) ->
        (string -> t -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (string option -> 'a1
        -> 'a2) -> (matchkind -> 'a1 -> 'a2) -> ((string, t) F.fs -> 'a1 e
        list -> positive -> coq_Z -> 'a1 -> 'a2) -> ('a1 e -> 'a2 -> coq_Z ->
        'a1 -> 'a2) -> 'a1 e -> 'a2

      val e_rec :
        (bool -> 'a1 -> 'a2) -> (positive -> coq_Z -> 'a1 -> 'a2) ->
        (positive -> coq_Z -> 'a1 -> 'a2) -> (t -> string -> 'a1 -> 'a2) ->
        ('a1 e -> 'a2 -> t -> positive -> positive -> 'a1 -> 'a2) -> (t ->
        'a1 e -> 'a2 -> 'a1 -> 'a2) -> (uop -> t -> 'a1 e -> 'a2 -> 'a1 ->
        'a2) -> (bop -> t -> t -> 'a1 e -> 'a2 -> 'a1 e -> 'a2 -> 'a1 -> 'a2)
        -> ('a1 e list -> 'a1 -> 'a2) -> ((string, t * 'a1 e) F.fs -> 'a1 ->
        'a2) -> ((string, t * 'a1 e) F.fs -> 'a1 e -> 'a2 -> 'a1 -> 'a2) ->
        (string -> t -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (string option -> 'a1
        -> 'a2) -> (matchkind -> 'a1 -> 'a2) -> ((string, t) F.fs -> 'a1 e
        list -> positive -> coq_Z -> 'a1 -> 'a2) -> ('a1 e -> 'a2 -> coq_Z ->
        'a1 -> 'a2) -> 'a1 e -> 'a2

      type 'tags_t args =
        (string, (t * 'tags_t e, t * 'tags_t e) paramarg) F.fs

      type 'tags_t arrowE =
        (string, t * 'tags_t e, t * 'tags_t e, t * 'tags_t e) arrow

      type 'tags_t constructor_arg = 'tags_t P4cub.Expr.constructor_arg =
      | CAExpr of 'tags_t e
      | CAName of string

      val constructor_arg_rect :
        ('a1 e -> 'a2) -> (string -> 'a2) -> 'a1 constructor_arg -> 'a2

      val constructor_arg_rec :
        ('a1 e -> 'a2) -> (string -> 'a2) -> 'a1 constructor_arg -> 'a2

      type 'tags_t constructor_args = (string, 'tags_t constructor_arg) F.fs

      module ExprNotations :
       sig
       end
     end

    module S :
     sig
      module E :
       sig
        type t = P4cub.Expr.t =
        | TBool
        | TBit of positive
        | TInt of positive
        | TError
        | TMatchKind
        | TTuple of t list
        | TStruct of (string, t) F.fs
        | THeader of (string, t) F.fs
        | THeaderStack of (string, t) F.fs * positive

        val t_rect :
          'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> 'a1 -> 'a1 -> (t
          list -> 'a1) -> ((string, t) F.fs -> 'a1) -> ((string, t) F.fs ->
          'a1) -> ((string, t) F.fs -> positive -> 'a1) -> t -> 'a1

        val t_rec :
          'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> 'a1 -> 'a1 -> (t
          list -> 'a1) -> ((string, t) F.fs -> 'a1) -> ((string, t) F.fs ->
          'a1) -> ((string, t) F.fs -> positive -> 'a1) -> t -> 'a1

        type params = (string, (t, t) paramarg) F.fs

        type arrowT = (string, t, t, t) arrow

        type ct = P4cub.Expr.ct =
        | CTType of t
        | CTControl of (string, ct) F.fs * params
        | CTParser of (string, ct) F.fs * params
        | CTPackage of (string, ct) F.fs
        | CTExtern of (string, ct) F.fs * (string, arrowT) F.fs

        val ct_rect :
          (t -> 'a1) -> ((string, ct) F.fs -> params -> 'a1) -> ((string, ct)
          F.fs -> params -> 'a1) -> ((string, ct) F.fs -> 'a1) -> ((string,
          ct) F.fs -> (string, arrowT) F.fs -> 'a1) -> ct -> 'a1

        val ct_rec :
          (t -> 'a1) -> ((string, ct) F.fs -> params -> 'a1) -> ((string, ct)
          F.fs -> params -> 'a1) -> ((string, ct) F.fs -> 'a1) -> ((string,
          ct) F.fs -> (string, arrowT) F.fs -> 'a1) -> ct -> 'a1

        type constructor_params = (string, ct) F.fs

        module TypeNotations :
         sig
         end

        type uop = P4cub.Expr.uop =
        | Not
        | BitNot
        | UMinus
        | IsValid
        | SetValid
        | SetInValid
        | NextIndex
        | Size
        | Push of positive
        | Pop of positive

        val uop_rect :
          'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (positive
          -> 'a1) -> (positive -> 'a1) -> uop -> 'a1

        val uop_rec :
          'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (positive
          -> 'a1) -> (positive -> 'a1) -> uop -> 'a1

        module UopNotations :
         sig
         end

        type bop = P4cub.Expr.bop =
        | Plus
        | PlusSat
        | Minus
        | MinusSat
        | Times
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

        val bop_rect :
          'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
          -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
          bop -> 'a1

        val bop_rec :
          'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
          -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
          bop -> 'a1

        module BopNotations :
         sig
         end

        type matchkind = P4cub.Expr.matchkind =
        | MKExact
        | MKTernary
        | MKLpm

        val matchkind_rect : 'a1 -> 'a1 -> 'a1 -> matchkind -> 'a1

        val matchkind_rec : 'a1 -> 'a1 -> 'a1 -> matchkind -> 'a1

        val coq_MatchKindEqDec : matchkind coq_EqDec

        module MatchkindNotations :
         sig
         end

        type 'tags_t e = 'tags_t P4cub.Expr.e =
        | EBool of bool * 'tags_t
        | EBit of positive * coq_Z * 'tags_t
        | EInt of positive * coq_Z * 'tags_t
        | EVar of t * string * 'tags_t
        | ESlice of 'tags_t e * t * positive * positive * 'tags_t
        | ECast of t * 'tags_t e * 'tags_t
        | EUop of uop * t * 'tags_t e * 'tags_t
        | EBop of bop * t * t * 'tags_t e * 'tags_t e * 'tags_t
        | ETuple of 'tags_t e list * 'tags_t
        | EStruct of (string, t * 'tags_t e) F.fs * 'tags_t
        | EHeader of (string, t * 'tags_t e) F.fs * 'tags_t e * 'tags_t
        | EExprMember of string * t * 'tags_t e * 'tags_t
        | EError of string option * 'tags_t
        | EMatchKind of matchkind * 'tags_t
        | EHeaderStack of (string, t) F.fs * 'tags_t e list * positive
           * coq_Z * 'tags_t
        | EHeaderStackAccess of 'tags_t e * coq_Z * 'tags_t

        val e_rect :
          (bool -> 'a1 -> 'a2) -> (positive -> coq_Z -> 'a1 -> 'a2) ->
          (positive -> coq_Z -> 'a1 -> 'a2) -> (t -> string -> 'a1 -> 'a2) ->
          ('a1 e -> 'a2 -> t -> positive -> positive -> 'a1 -> 'a2) -> (t ->
          'a1 e -> 'a2 -> 'a1 -> 'a2) -> (uop -> t -> 'a1 e -> 'a2 -> 'a1 ->
          'a2) -> (bop -> t -> t -> 'a1 e -> 'a2 -> 'a1 e -> 'a2 -> 'a1 ->
          'a2) -> ('a1 e list -> 'a1 -> 'a2) -> ((string, t * 'a1 e) F.fs ->
          'a1 -> 'a2) -> ((string, t * 'a1 e) F.fs -> 'a1 e -> 'a2 -> 'a1 ->
          'a2) -> (string -> t -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (string
          option -> 'a1 -> 'a2) -> (matchkind -> 'a1 -> 'a2) -> ((string, t)
          F.fs -> 'a1 e list -> positive -> coq_Z -> 'a1 -> 'a2) -> ('a1 e ->
          'a2 -> coq_Z -> 'a1 -> 'a2) -> 'a1 e -> 'a2

        val e_rec :
          (bool -> 'a1 -> 'a2) -> (positive -> coq_Z -> 'a1 -> 'a2) ->
          (positive -> coq_Z -> 'a1 -> 'a2) -> (t -> string -> 'a1 -> 'a2) ->
          ('a1 e -> 'a2 -> t -> positive -> positive -> 'a1 -> 'a2) -> (t ->
          'a1 e -> 'a2 -> 'a1 -> 'a2) -> (uop -> t -> 'a1 e -> 'a2 -> 'a1 ->
          'a2) -> (bop -> t -> t -> 'a1 e -> 'a2 -> 'a1 e -> 'a2 -> 'a1 ->
          'a2) -> ('a1 e list -> 'a1 -> 'a2) -> ((string, t * 'a1 e) F.fs ->
          'a1 -> 'a2) -> ((string, t * 'a1 e) F.fs -> 'a1 e -> 'a2 -> 'a1 ->
          'a2) -> (string -> t -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (string
          option -> 'a1 -> 'a2) -> (matchkind -> 'a1 -> 'a2) -> ((string, t)
          F.fs -> 'a1 e list -> positive -> coq_Z -> 'a1 -> 'a2) -> ('a1 e ->
          'a2 -> coq_Z -> 'a1 -> 'a2) -> 'a1 e -> 'a2

        type 'tags_t args =
          (string, (t * 'tags_t e, t * 'tags_t e) paramarg) F.fs

        type 'tags_t arrowE =
          (string, t * 'tags_t e, t * 'tags_t e, t * 'tags_t e) arrow

        type 'tags_t constructor_arg = 'tags_t P4cub.Expr.constructor_arg =
        | CAExpr of 'tags_t e
        | CAName of string

        val constructor_arg_rect :
          ('a1 e -> 'a2) -> (string -> 'a2) -> 'a1 constructor_arg -> 'a2

        val constructor_arg_rec :
          ('a1 e -> 'a2) -> (string -> 'a2) -> 'a1 constructor_arg -> 'a2

        type 'tags_t constructor_args = (string, 'tags_t constructor_arg) F.fs

        module ExprNotations :
         sig
         end
       end

      type 'tags_t s = 'tags_t P4cub.Stmt.s =
      | SSkip of 'tags_t
      | SVardecl of E.t * string * 'tags_t
      | SAssign of E.t * 'tags_t E.e * 'tags_t E.e * 'tags_t
      | SConditional of E.t * 'tags_t E.e * 'tags_t s * 'tags_t s * 'tags_t
      | SSeq of 'tags_t s * 'tags_t s * 'tags_t
      | SBlock of 'tags_t s
      | SExternMethodCall of string * string * 'tags_t E.arrowE * 'tags_t
      | SFunCall of string * 'tags_t E.arrowE * 'tags_t
      | SActCall of string * 'tags_t E.args * 'tags_t
      | SReturnVoid of 'tags_t
      | SReturnFruit of E.t * 'tags_t E.e * 'tags_t
      | SExit of 'tags_t
      | SInvoke of string * 'tags_t
      | SApply of string * 'tags_t E.args * 'tags_t

      val s_rect :
        ('a1 -> 'a2) -> (E.t -> string -> 'a1 -> 'a2) -> (E.t -> 'a1 E.e ->
        'a1 E.e -> 'a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1 s -> 'a2 -> 'a1 s ->
        'a2 -> 'a1 -> 'a2) -> ('a1 s -> 'a2 -> 'a1 s -> 'a2 -> 'a1 -> 'a2) ->
        ('a1 s -> 'a2 -> 'a2) -> (string -> string -> 'a1 E.arrowE -> 'a1 ->
        'a2) -> (string -> 'a1 E.arrowE -> 'a1 -> 'a2) -> (string -> 'a1
        E.args -> 'a1 -> 'a2) -> ('a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1 ->
        'a2) -> ('a1 -> 'a2) -> (string -> 'a1 -> 'a2) -> (string -> 'a1
        E.args -> 'a1 -> 'a2) -> 'a1 s -> 'a2

      val s_rec :
        ('a1 -> 'a2) -> (E.t -> string -> 'a1 -> 'a2) -> (E.t -> 'a1 E.e ->
        'a1 E.e -> 'a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1 s -> 'a2 -> 'a1 s ->
        'a2 -> 'a1 -> 'a2) -> ('a1 s -> 'a2 -> 'a1 s -> 'a2 -> 'a1 -> 'a2) ->
        ('a1 s -> 'a2 -> 'a2) -> (string -> string -> 'a1 E.arrowE -> 'a1 ->
        'a2) -> (string -> 'a1 E.arrowE -> 'a1 -> 'a2) -> (string -> 'a1
        E.args -> 'a1 -> 'a2) -> ('a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1 ->
        'a2) -> ('a1 -> 'a2) -> (string -> 'a1 -> 'a2) -> (string -> 'a1
        E.args -> 'a1 -> 'a2) -> 'a1 s -> 'a2

      module StmtNotations :
       sig
       end
     end

    type state = P4cub.Parser.state =
    | STStart
    | STAccept
    | STReject
    | STName of string

    val state_rect : 'a1 -> 'a1 -> 'a1 -> (string -> 'a1) -> state -> 'a1

    val state_rec : 'a1 -> 'a1 -> 'a1 -> (string -> 'a1) -> state -> 'a1

    type pat = P4cub.Parser.pat =
    | PATWild
    | PATMask of pat * pat
    | PATRange of pat * pat
    | PATBit of positive * coq_Z
    | PATInt of positive * coq_Z
    | PATTuple of pat list

    val pat_rect :
      'a1 -> (pat -> 'a1 -> pat -> 'a1 -> 'a1) -> (pat -> 'a1 -> pat -> 'a1
      -> 'a1) -> (positive -> coq_Z -> 'a1) -> (positive -> coq_Z -> 'a1) ->
      (pat list -> 'a1) -> pat -> 'a1

    val pat_rec :
      'a1 -> (pat -> 'a1 -> pat -> 'a1 -> 'a1) -> (pat -> 'a1 -> pat -> 'a1
      -> 'a1) -> (positive -> coq_Z -> 'a1) -> (positive -> coq_Z -> 'a1) ->
      (pat list -> 'a1) -> pat -> 'a1

    type 'tags_t e = 'tags_t P4cub.Parser.e =
    | PGoto of state * 'tags_t
    | PSelect of 'tags_t E.e * 'tags_t e * (pat, 'tags_t e) F.fs * 'tags_t

    val e_rect :
      (state -> 'a1 -> 'a2) -> ('a1 E.e -> 'a1 e -> 'a2 -> (pat, 'a1 e) F.fs
      -> 'a1 -> 'a2) -> 'a1 e -> 'a2

    val e_rec :
      (state -> 'a1 -> 'a2) -> ('a1 E.e -> 'a1 e -> 'a2 -> (pat, 'a1 e) F.fs
      -> 'a1 -> 'a2) -> 'a1 e -> 'a2

    type 'tags_t state_block = 'tags_t P4cub.Parser.state_block =
    | State of 'tags_t S.s * 'tags_t e

    val state_block_rect : ('a1 S.s -> 'a1 e -> 'a2) -> 'a1 state_block -> 'a2

    val state_block_rec : ('a1 S.s -> 'a1 e -> 'a2) -> 'a1 state_block -> 'a2

    module ParserNotations :
     sig
     end
   end

  module Control :
   sig
    module E :
     sig
      type t = P4cub.Expr.t =
      | TBool
      | TBit of positive
      | TInt of positive
      | TError
      | TMatchKind
      | TTuple of t list
      | TStruct of (string, t) F.fs
      | THeader of (string, t) F.fs
      | THeaderStack of (string, t) F.fs * positive

      val t_rect :
        'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> 'a1 -> 'a1 -> (t
        list -> 'a1) -> ((string, t) F.fs -> 'a1) -> ((string, t) F.fs ->
        'a1) -> ((string, t) F.fs -> positive -> 'a1) -> t -> 'a1

      val t_rec :
        'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> 'a1 -> 'a1 -> (t
        list -> 'a1) -> ((string, t) F.fs -> 'a1) -> ((string, t) F.fs ->
        'a1) -> ((string, t) F.fs -> positive -> 'a1) -> t -> 'a1

      type params = (string, (t, t) paramarg) F.fs

      type arrowT = (string, t, t, t) arrow

      type ct = P4cub.Expr.ct =
      | CTType of t
      | CTControl of (string, ct) F.fs * params
      | CTParser of (string, ct) F.fs * params
      | CTPackage of (string, ct) F.fs
      | CTExtern of (string, ct) F.fs * (string, arrowT) F.fs

      val ct_rect :
        (t -> 'a1) -> ((string, ct) F.fs -> params -> 'a1) -> ((string, ct)
        F.fs -> params -> 'a1) -> ((string, ct) F.fs -> 'a1) -> ((string, ct)
        F.fs -> (string, arrowT) F.fs -> 'a1) -> ct -> 'a1

      val ct_rec :
        (t -> 'a1) -> ((string, ct) F.fs -> params -> 'a1) -> ((string, ct)
        F.fs -> params -> 'a1) -> ((string, ct) F.fs -> 'a1) -> ((string, ct)
        F.fs -> (string, arrowT) F.fs -> 'a1) -> ct -> 'a1

      type constructor_params = (string, ct) F.fs

      module TypeNotations :
       sig
       end

      type uop = P4cub.Expr.uop =
      | Not
      | BitNot
      | UMinus
      | IsValid
      | SetValid
      | SetInValid
      | NextIndex
      | Size
      | Push of positive
      | Pop of positive

      val uop_rect :
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (positive ->
        'a1) -> (positive -> 'a1) -> uop -> 'a1

      val uop_rec :
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (positive ->
        'a1) -> (positive -> 'a1) -> uop -> 'a1

      module UopNotations :
       sig
       end

      type bop = P4cub.Expr.bop =
      | Plus
      | PlusSat
      | Minus
      | MinusSat
      | Times
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

      val bop_rect :
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> bop ->
        'a1

      val bop_rec :
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> bop ->
        'a1

      module BopNotations :
       sig
       end

      type matchkind = P4cub.Expr.matchkind =
      | MKExact
      | MKTernary
      | MKLpm

      val matchkind_rect : 'a1 -> 'a1 -> 'a1 -> matchkind -> 'a1

      val matchkind_rec : 'a1 -> 'a1 -> 'a1 -> matchkind -> 'a1

      val coq_MatchKindEqDec : matchkind coq_EqDec

      module MatchkindNotations :
       sig
       end

      type 'tags_t e = 'tags_t P4cub.Expr.e =
      | EBool of bool * 'tags_t
      | EBit of positive * coq_Z * 'tags_t
      | EInt of positive * coq_Z * 'tags_t
      | EVar of t * string * 'tags_t
      | ESlice of 'tags_t e * t * positive * positive * 'tags_t
      | ECast of t * 'tags_t e * 'tags_t
      | EUop of uop * t * 'tags_t e * 'tags_t
      | EBop of bop * t * t * 'tags_t e * 'tags_t e * 'tags_t
      | ETuple of 'tags_t e list * 'tags_t
      | EStruct of (string, t * 'tags_t e) F.fs * 'tags_t
      | EHeader of (string, t * 'tags_t e) F.fs * 'tags_t e * 'tags_t
      | EExprMember of string * t * 'tags_t e * 'tags_t
      | EError of string option * 'tags_t
      | EMatchKind of matchkind * 'tags_t
      | EHeaderStack of (string, t) F.fs * 'tags_t e list * positive * 
         coq_Z * 'tags_t
      | EHeaderStackAccess of 'tags_t e * coq_Z * 'tags_t

      val e_rect :
        (bool -> 'a1 -> 'a2) -> (positive -> coq_Z -> 'a1 -> 'a2) ->
        (positive -> coq_Z -> 'a1 -> 'a2) -> (t -> string -> 'a1 -> 'a2) ->
        ('a1 e -> 'a2 -> t -> positive -> positive -> 'a1 -> 'a2) -> (t ->
        'a1 e -> 'a2 -> 'a1 -> 'a2) -> (uop -> t -> 'a1 e -> 'a2 -> 'a1 ->
        'a2) -> (bop -> t -> t -> 'a1 e -> 'a2 -> 'a1 e -> 'a2 -> 'a1 -> 'a2)
        -> ('a1 e list -> 'a1 -> 'a2) -> ((string, t * 'a1 e) F.fs -> 'a1 ->
        'a2) -> ((string, t * 'a1 e) F.fs -> 'a1 e -> 'a2 -> 'a1 -> 'a2) ->
        (string -> t -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (string option -> 'a1
        -> 'a2) -> (matchkind -> 'a1 -> 'a2) -> ((string, t) F.fs -> 'a1 e
        list -> positive -> coq_Z -> 'a1 -> 'a2) -> ('a1 e -> 'a2 -> coq_Z ->
        'a1 -> 'a2) -> 'a1 e -> 'a2

      val e_rec :
        (bool -> 'a1 -> 'a2) -> (positive -> coq_Z -> 'a1 -> 'a2) ->
        (positive -> coq_Z -> 'a1 -> 'a2) -> (t -> string -> 'a1 -> 'a2) ->
        ('a1 e -> 'a2 -> t -> positive -> positive -> 'a1 -> 'a2) -> (t ->
        'a1 e -> 'a2 -> 'a1 -> 'a2) -> (uop -> t -> 'a1 e -> 'a2 -> 'a1 ->
        'a2) -> (bop -> t -> t -> 'a1 e -> 'a2 -> 'a1 e -> 'a2 -> 'a1 -> 'a2)
        -> ('a1 e list -> 'a1 -> 'a2) -> ((string, t * 'a1 e) F.fs -> 'a1 ->
        'a2) -> ((string, t * 'a1 e) F.fs -> 'a1 e -> 'a2 -> 'a1 -> 'a2) ->
        (string -> t -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (string option -> 'a1
        -> 'a2) -> (matchkind -> 'a1 -> 'a2) -> ((string, t) F.fs -> 'a1 e
        list -> positive -> coq_Z -> 'a1 -> 'a2) -> ('a1 e -> 'a2 -> coq_Z ->
        'a1 -> 'a2) -> 'a1 e -> 'a2

      type 'tags_t args =
        (string, (t * 'tags_t e, t * 'tags_t e) paramarg) F.fs

      type 'tags_t arrowE =
        (string, t * 'tags_t e, t * 'tags_t e, t * 'tags_t e) arrow

      type 'tags_t constructor_arg = 'tags_t P4cub.Expr.constructor_arg =
      | CAExpr of 'tags_t e
      | CAName of string

      val constructor_arg_rect :
        ('a1 e -> 'a2) -> (string -> 'a2) -> 'a1 constructor_arg -> 'a2

      val constructor_arg_rec :
        ('a1 e -> 'a2) -> (string -> 'a2) -> 'a1 constructor_arg -> 'a2

      type 'tags_t constructor_args = (string, 'tags_t constructor_arg) F.fs

      module ExprNotations :
       sig
       end
     end

    module S :
     sig
      module E :
       sig
        type t = P4cub.Expr.t =
        | TBool
        | TBit of positive
        | TInt of positive
        | TError
        | TMatchKind
        | TTuple of t list
        | TStruct of (string, t) F.fs
        | THeader of (string, t) F.fs
        | THeaderStack of (string, t) F.fs * positive

        val t_rect :
          'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> 'a1 -> 'a1 -> (t
          list -> 'a1) -> ((string, t) F.fs -> 'a1) -> ((string, t) F.fs ->
          'a1) -> ((string, t) F.fs -> positive -> 'a1) -> t -> 'a1

        val t_rec :
          'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> 'a1 -> 'a1 -> (t
          list -> 'a1) -> ((string, t) F.fs -> 'a1) -> ((string, t) F.fs ->
          'a1) -> ((string, t) F.fs -> positive -> 'a1) -> t -> 'a1

        type params = (string, (t, t) paramarg) F.fs

        type arrowT = (string, t, t, t) arrow

        type ct = P4cub.Expr.ct =
        | CTType of t
        | CTControl of (string, ct) F.fs * params
        | CTParser of (string, ct) F.fs * params
        | CTPackage of (string, ct) F.fs
        | CTExtern of (string, ct) F.fs * (string, arrowT) F.fs

        val ct_rect :
          (t -> 'a1) -> ((string, ct) F.fs -> params -> 'a1) -> ((string, ct)
          F.fs -> params -> 'a1) -> ((string, ct) F.fs -> 'a1) -> ((string,
          ct) F.fs -> (string, arrowT) F.fs -> 'a1) -> ct -> 'a1

        val ct_rec :
          (t -> 'a1) -> ((string, ct) F.fs -> params -> 'a1) -> ((string, ct)
          F.fs -> params -> 'a1) -> ((string, ct) F.fs -> 'a1) -> ((string,
          ct) F.fs -> (string, arrowT) F.fs -> 'a1) -> ct -> 'a1

        type constructor_params = (string, ct) F.fs

        module TypeNotations :
         sig
         end

        type uop = P4cub.Expr.uop =
        | Not
        | BitNot
        | UMinus
        | IsValid
        | SetValid
        | SetInValid
        | NextIndex
        | Size
        | Push of positive
        | Pop of positive

        val uop_rect :
          'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (positive
          -> 'a1) -> (positive -> 'a1) -> uop -> 'a1

        val uop_rec :
          'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (positive
          -> 'a1) -> (positive -> 'a1) -> uop -> 'a1

        module UopNotations :
         sig
         end

        type bop = P4cub.Expr.bop =
        | Plus
        | PlusSat
        | Minus
        | MinusSat
        | Times
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

        val bop_rect :
          'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
          -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
          bop -> 'a1

        val bop_rec :
          'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
          -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
          bop -> 'a1

        module BopNotations :
         sig
         end

        type matchkind = P4cub.Expr.matchkind =
        | MKExact
        | MKTernary
        | MKLpm

        val matchkind_rect : 'a1 -> 'a1 -> 'a1 -> matchkind -> 'a1

        val matchkind_rec : 'a1 -> 'a1 -> 'a1 -> matchkind -> 'a1

        val coq_MatchKindEqDec : matchkind coq_EqDec

        module MatchkindNotations :
         sig
         end

        type 'tags_t e = 'tags_t P4cub.Expr.e =
        | EBool of bool * 'tags_t
        | EBit of positive * coq_Z * 'tags_t
        | EInt of positive * coq_Z * 'tags_t
        | EVar of t * string * 'tags_t
        | ESlice of 'tags_t e * t * positive * positive * 'tags_t
        | ECast of t * 'tags_t e * 'tags_t
        | EUop of uop * t * 'tags_t e * 'tags_t
        | EBop of bop * t * t * 'tags_t e * 'tags_t e * 'tags_t
        | ETuple of 'tags_t e list * 'tags_t
        | EStruct of (string, t * 'tags_t e) F.fs * 'tags_t
        | EHeader of (string, t * 'tags_t e) F.fs * 'tags_t e * 'tags_t
        | EExprMember of string * t * 'tags_t e * 'tags_t
        | EError of string option * 'tags_t
        | EMatchKind of matchkind * 'tags_t
        | EHeaderStack of (string, t) F.fs * 'tags_t e list * positive
           * coq_Z * 'tags_t
        | EHeaderStackAccess of 'tags_t e * coq_Z * 'tags_t

        val e_rect :
          (bool -> 'a1 -> 'a2) -> (positive -> coq_Z -> 'a1 -> 'a2) ->
          (positive -> coq_Z -> 'a1 -> 'a2) -> (t -> string -> 'a1 -> 'a2) ->
          ('a1 e -> 'a2 -> t -> positive -> positive -> 'a1 -> 'a2) -> (t ->
          'a1 e -> 'a2 -> 'a1 -> 'a2) -> (uop -> t -> 'a1 e -> 'a2 -> 'a1 ->
          'a2) -> (bop -> t -> t -> 'a1 e -> 'a2 -> 'a1 e -> 'a2 -> 'a1 ->
          'a2) -> ('a1 e list -> 'a1 -> 'a2) -> ((string, t * 'a1 e) F.fs ->
          'a1 -> 'a2) -> ((string, t * 'a1 e) F.fs -> 'a1 e -> 'a2 -> 'a1 ->
          'a2) -> (string -> t -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (string
          option -> 'a1 -> 'a2) -> (matchkind -> 'a1 -> 'a2) -> ((string, t)
          F.fs -> 'a1 e list -> positive -> coq_Z -> 'a1 -> 'a2) -> ('a1 e ->
          'a2 -> coq_Z -> 'a1 -> 'a2) -> 'a1 e -> 'a2

        val e_rec :
          (bool -> 'a1 -> 'a2) -> (positive -> coq_Z -> 'a1 -> 'a2) ->
          (positive -> coq_Z -> 'a1 -> 'a2) -> (t -> string -> 'a1 -> 'a2) ->
          ('a1 e -> 'a2 -> t -> positive -> positive -> 'a1 -> 'a2) -> (t ->
          'a1 e -> 'a2 -> 'a1 -> 'a2) -> (uop -> t -> 'a1 e -> 'a2 -> 'a1 ->
          'a2) -> (bop -> t -> t -> 'a1 e -> 'a2 -> 'a1 e -> 'a2 -> 'a1 ->
          'a2) -> ('a1 e list -> 'a1 -> 'a2) -> ((string, t * 'a1 e) F.fs ->
          'a1 -> 'a2) -> ((string, t * 'a1 e) F.fs -> 'a1 e -> 'a2 -> 'a1 ->
          'a2) -> (string -> t -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (string
          option -> 'a1 -> 'a2) -> (matchkind -> 'a1 -> 'a2) -> ((string, t)
          F.fs -> 'a1 e list -> positive -> coq_Z -> 'a1 -> 'a2) -> ('a1 e ->
          'a2 -> coq_Z -> 'a1 -> 'a2) -> 'a1 e -> 'a2

        type 'tags_t args =
          (string, (t * 'tags_t e, t * 'tags_t e) paramarg) F.fs

        type 'tags_t arrowE =
          (string, t * 'tags_t e, t * 'tags_t e, t * 'tags_t e) arrow

        type 'tags_t constructor_arg = 'tags_t P4cub.Expr.constructor_arg =
        | CAExpr of 'tags_t e
        | CAName of string

        val constructor_arg_rect :
          ('a1 e -> 'a2) -> (string -> 'a2) -> 'a1 constructor_arg -> 'a2

        val constructor_arg_rec :
          ('a1 e -> 'a2) -> (string -> 'a2) -> 'a1 constructor_arg -> 'a2

        type 'tags_t constructor_args = (string, 'tags_t constructor_arg) F.fs

        module ExprNotations :
         sig
         end
       end

      type 'tags_t s = 'tags_t P4cub.Stmt.s =
      | SSkip of 'tags_t
      | SVardecl of E.t * string * 'tags_t
      | SAssign of E.t * 'tags_t E.e * 'tags_t E.e * 'tags_t
      | SConditional of E.t * 'tags_t E.e * 'tags_t s * 'tags_t s * 'tags_t
      | SSeq of 'tags_t s * 'tags_t s * 'tags_t
      | SBlock of 'tags_t s
      | SExternMethodCall of string * string * 'tags_t E.arrowE * 'tags_t
      | SFunCall of string * 'tags_t E.arrowE * 'tags_t
      | SActCall of string * 'tags_t E.args * 'tags_t
      | SReturnVoid of 'tags_t
      | SReturnFruit of E.t * 'tags_t E.e * 'tags_t
      | SExit of 'tags_t
      | SInvoke of string * 'tags_t
      | SApply of string * 'tags_t E.args * 'tags_t

      val s_rect :
        ('a1 -> 'a2) -> (E.t -> string -> 'a1 -> 'a2) -> (E.t -> 'a1 E.e ->
        'a1 E.e -> 'a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1 s -> 'a2 -> 'a1 s ->
        'a2 -> 'a1 -> 'a2) -> ('a1 s -> 'a2 -> 'a1 s -> 'a2 -> 'a1 -> 'a2) ->
        ('a1 s -> 'a2 -> 'a2) -> (string -> string -> 'a1 E.arrowE -> 'a1 ->
        'a2) -> (string -> 'a1 E.arrowE -> 'a1 -> 'a2) -> (string -> 'a1
        E.args -> 'a1 -> 'a2) -> ('a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1 ->
        'a2) -> ('a1 -> 'a2) -> (string -> 'a1 -> 'a2) -> (string -> 'a1
        E.args -> 'a1 -> 'a2) -> 'a1 s -> 'a2

      val s_rec :
        ('a1 -> 'a2) -> (E.t -> string -> 'a1 -> 'a2) -> (E.t -> 'a1 E.e ->
        'a1 E.e -> 'a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1 s -> 'a2 -> 'a1 s ->
        'a2 -> 'a1 -> 'a2) -> ('a1 s -> 'a2 -> 'a1 s -> 'a2 -> 'a1 -> 'a2) ->
        ('a1 s -> 'a2 -> 'a2) -> (string -> string -> 'a1 E.arrowE -> 'a1 ->
        'a2) -> (string -> 'a1 E.arrowE -> 'a1 -> 'a2) -> (string -> 'a1
        E.args -> 'a1 -> 'a2) -> ('a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1 ->
        'a2) -> ('a1 -> 'a2) -> (string -> 'a1 -> 'a2) -> (string -> 'a1
        E.args -> 'a1 -> 'a2) -> 'a1 s -> 'a2

      module StmtNotations :
       sig
       end
     end

    module ControlDecl :
     sig
      type 'tags_t table = 'tags_t P4cub.Control.ControlDecl.table =
      | Table of ((E.t * 'tags_t E.e) * E.matchkind) list * string list

      val table_rect :
        (((E.t * 'a1 E.e) * E.matchkind) list -> string list -> 'a2) -> 'a1
        table -> 'a2

      val table_rec :
        (((E.t * 'a1 E.e) * E.matchkind) list -> string list -> 'a2) -> 'a1
        table -> 'a2

      type 'tags_t d = 'tags_t P4cub.Control.ControlDecl.d =
      | CDAction of string * E.params * 'tags_t S.s * 'tags_t
      | CDTable of string * 'tags_t table * 'tags_t
      | CDSeq of 'tags_t d * 'tags_t d * 'tags_t

      val d_rect :
        (string -> E.params -> 'a1 S.s -> 'a1 -> 'a2) -> (string -> 'a1 table
        -> 'a1 -> 'a2) -> ('a1 d -> 'a2 -> 'a1 d -> 'a2 -> 'a1 -> 'a2) -> 'a1
        d -> 'a2

      val d_rec :
        (string -> E.params -> 'a1 S.s -> 'a1 -> 'a2) -> (string -> 'a1 table
        -> 'a1 -> 'a2) -> ('a1 d -> 'a2 -> 'a1 d -> 'a2 -> 'a1 -> 'a2) -> 'a1
        d -> 'a2

      module ControlDeclNotations :
       sig
       end
     end
   end

  module TopDecl :
   sig
    module E :
     sig
      type t = P4cub.Expr.t =
      | TBool
      | TBit of positive
      | TInt of positive
      | TError
      | TMatchKind
      | TTuple of t list
      | TStruct of (string, t) F.fs
      | THeader of (string, t) F.fs
      | THeaderStack of (string, t) F.fs * positive

      val t_rect :
        'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> 'a1 -> 'a1 -> (t
        list -> 'a1) -> ((string, t) F.fs -> 'a1) -> ((string, t) F.fs ->
        'a1) -> ((string, t) F.fs -> positive -> 'a1) -> t -> 'a1

      val t_rec :
        'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> 'a1 -> 'a1 -> (t
        list -> 'a1) -> ((string, t) F.fs -> 'a1) -> ((string, t) F.fs ->
        'a1) -> ((string, t) F.fs -> positive -> 'a1) -> t -> 'a1

      type params = (string, (t, t) paramarg) F.fs

      type arrowT = (string, t, t, t) arrow

      type ct = P4cub.Expr.ct =
      | CTType of t
      | CTControl of (string, ct) F.fs * params
      | CTParser of (string, ct) F.fs * params
      | CTPackage of (string, ct) F.fs
      | CTExtern of (string, ct) F.fs * (string, arrowT) F.fs

      val ct_rect :
        (t -> 'a1) -> ((string, ct) F.fs -> params -> 'a1) -> ((string, ct)
        F.fs -> params -> 'a1) -> ((string, ct) F.fs -> 'a1) -> ((string, ct)
        F.fs -> (string, arrowT) F.fs -> 'a1) -> ct -> 'a1

      val ct_rec :
        (t -> 'a1) -> ((string, ct) F.fs -> params -> 'a1) -> ((string, ct)
        F.fs -> params -> 'a1) -> ((string, ct) F.fs -> 'a1) -> ((string, ct)
        F.fs -> (string, arrowT) F.fs -> 'a1) -> ct -> 'a1

      type constructor_params = (string, ct) F.fs

      module TypeNotations :
       sig
       end

      type uop = P4cub.Expr.uop =
      | Not
      | BitNot
      | UMinus
      | IsValid
      | SetValid
      | SetInValid
      | NextIndex
      | Size
      | Push of positive
      | Pop of positive

      val uop_rect :
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (positive ->
        'a1) -> (positive -> 'a1) -> uop -> 'a1

      val uop_rec :
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (positive ->
        'a1) -> (positive -> 'a1) -> uop -> 'a1

      module UopNotations :
       sig
       end

      type bop = P4cub.Expr.bop =
      | Plus
      | PlusSat
      | Minus
      | MinusSat
      | Times
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

      val bop_rect :
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> bop ->
        'a1

      val bop_rec :
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> bop ->
        'a1

      module BopNotations :
       sig
       end

      type matchkind = P4cub.Expr.matchkind =
      | MKExact
      | MKTernary
      | MKLpm

      val matchkind_rect : 'a1 -> 'a1 -> 'a1 -> matchkind -> 'a1

      val matchkind_rec : 'a1 -> 'a1 -> 'a1 -> matchkind -> 'a1

      val coq_MatchKindEqDec : matchkind coq_EqDec

      module MatchkindNotations :
       sig
       end

      type 'tags_t e = 'tags_t P4cub.Expr.e =
      | EBool of bool * 'tags_t
      | EBit of positive * coq_Z * 'tags_t
      | EInt of positive * coq_Z * 'tags_t
      | EVar of t * string * 'tags_t
      | ESlice of 'tags_t e * t * positive * positive * 'tags_t
      | ECast of t * 'tags_t e * 'tags_t
      | EUop of uop * t * 'tags_t e * 'tags_t
      | EBop of bop * t * t * 'tags_t e * 'tags_t e * 'tags_t
      | ETuple of 'tags_t e list * 'tags_t
      | EStruct of (string, t * 'tags_t e) F.fs * 'tags_t
      | EHeader of (string, t * 'tags_t e) F.fs * 'tags_t e * 'tags_t
      | EExprMember of string * t * 'tags_t e * 'tags_t
      | EError of string option * 'tags_t
      | EMatchKind of matchkind * 'tags_t
      | EHeaderStack of (string, t) F.fs * 'tags_t e list * positive * 
         coq_Z * 'tags_t
      | EHeaderStackAccess of 'tags_t e * coq_Z * 'tags_t

      val e_rect :
        (bool -> 'a1 -> 'a2) -> (positive -> coq_Z -> 'a1 -> 'a2) ->
        (positive -> coq_Z -> 'a1 -> 'a2) -> (t -> string -> 'a1 -> 'a2) ->
        ('a1 e -> 'a2 -> t -> positive -> positive -> 'a1 -> 'a2) -> (t ->
        'a1 e -> 'a2 -> 'a1 -> 'a2) -> (uop -> t -> 'a1 e -> 'a2 -> 'a1 ->
        'a2) -> (bop -> t -> t -> 'a1 e -> 'a2 -> 'a1 e -> 'a2 -> 'a1 -> 'a2)
        -> ('a1 e list -> 'a1 -> 'a2) -> ((string, t * 'a1 e) F.fs -> 'a1 ->
        'a2) -> ((string, t * 'a1 e) F.fs -> 'a1 e -> 'a2 -> 'a1 -> 'a2) ->
        (string -> t -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (string option -> 'a1
        -> 'a2) -> (matchkind -> 'a1 -> 'a2) -> ((string, t) F.fs -> 'a1 e
        list -> positive -> coq_Z -> 'a1 -> 'a2) -> ('a1 e -> 'a2 -> coq_Z ->
        'a1 -> 'a2) -> 'a1 e -> 'a2

      val e_rec :
        (bool -> 'a1 -> 'a2) -> (positive -> coq_Z -> 'a1 -> 'a2) ->
        (positive -> coq_Z -> 'a1 -> 'a2) -> (t -> string -> 'a1 -> 'a2) ->
        ('a1 e -> 'a2 -> t -> positive -> positive -> 'a1 -> 'a2) -> (t ->
        'a1 e -> 'a2 -> 'a1 -> 'a2) -> (uop -> t -> 'a1 e -> 'a2 -> 'a1 ->
        'a2) -> (bop -> t -> t -> 'a1 e -> 'a2 -> 'a1 e -> 'a2 -> 'a1 -> 'a2)
        -> ('a1 e list -> 'a1 -> 'a2) -> ((string, t * 'a1 e) F.fs -> 'a1 ->
        'a2) -> ((string, t * 'a1 e) F.fs -> 'a1 e -> 'a2 -> 'a1 -> 'a2) ->
        (string -> t -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (string option -> 'a1
        -> 'a2) -> (matchkind -> 'a1 -> 'a2) -> ((string, t) F.fs -> 'a1 e
        list -> positive -> coq_Z -> 'a1 -> 'a2) -> ('a1 e -> 'a2 -> coq_Z ->
        'a1 -> 'a2) -> 'a1 e -> 'a2

      type 'tags_t args =
        (string, (t * 'tags_t e, t * 'tags_t e) paramarg) F.fs

      type 'tags_t arrowE =
        (string, t * 'tags_t e, t * 'tags_t e, t * 'tags_t e) arrow

      type 'tags_t constructor_arg = 'tags_t P4cub.Expr.constructor_arg =
      | CAExpr of 'tags_t e
      | CAName of string

      val constructor_arg_rect :
        ('a1 e -> 'a2) -> (string -> 'a2) -> 'a1 constructor_arg -> 'a2

      val constructor_arg_rec :
        ('a1 e -> 'a2) -> (string -> 'a2) -> 'a1 constructor_arg -> 'a2

      type 'tags_t constructor_args = (string, 'tags_t constructor_arg) F.fs

      module ExprNotations :
       sig
       end
     end

    module S :
     sig
      module E :
       sig
        type t = P4cub.Expr.t =
        | TBool
        | TBit of positive
        | TInt of positive
        | TError
        | TMatchKind
        | TTuple of t list
        | TStruct of (string, t) F.fs
        | THeader of (string, t) F.fs
        | THeaderStack of (string, t) F.fs * positive

        val t_rect :
          'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> 'a1 -> 'a1 -> (t
          list -> 'a1) -> ((string, t) F.fs -> 'a1) -> ((string, t) F.fs ->
          'a1) -> ((string, t) F.fs -> positive -> 'a1) -> t -> 'a1

        val t_rec :
          'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> 'a1 -> 'a1 -> (t
          list -> 'a1) -> ((string, t) F.fs -> 'a1) -> ((string, t) F.fs ->
          'a1) -> ((string, t) F.fs -> positive -> 'a1) -> t -> 'a1

        type params = (string, (t, t) paramarg) F.fs

        type arrowT = (string, t, t, t) arrow

        type ct = P4cub.Expr.ct =
        | CTType of t
        | CTControl of (string, ct) F.fs * params
        | CTParser of (string, ct) F.fs * params
        | CTPackage of (string, ct) F.fs
        | CTExtern of (string, ct) F.fs * (string, arrowT) F.fs

        val ct_rect :
          (t -> 'a1) -> ((string, ct) F.fs -> params -> 'a1) -> ((string, ct)
          F.fs -> params -> 'a1) -> ((string, ct) F.fs -> 'a1) -> ((string,
          ct) F.fs -> (string, arrowT) F.fs -> 'a1) -> ct -> 'a1

        val ct_rec :
          (t -> 'a1) -> ((string, ct) F.fs -> params -> 'a1) -> ((string, ct)
          F.fs -> params -> 'a1) -> ((string, ct) F.fs -> 'a1) -> ((string,
          ct) F.fs -> (string, arrowT) F.fs -> 'a1) -> ct -> 'a1

        type constructor_params = (string, ct) F.fs

        module TypeNotations :
         sig
         end

        type uop = P4cub.Expr.uop =
        | Not
        | BitNot
        | UMinus
        | IsValid
        | SetValid
        | SetInValid
        | NextIndex
        | Size
        | Push of positive
        | Pop of positive

        val uop_rect :
          'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (positive
          -> 'a1) -> (positive -> 'a1) -> uop -> 'a1

        val uop_rec :
          'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (positive
          -> 'a1) -> (positive -> 'a1) -> uop -> 'a1

        module UopNotations :
         sig
         end

        type bop = P4cub.Expr.bop =
        | Plus
        | PlusSat
        | Minus
        | MinusSat
        | Times
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

        val bop_rect :
          'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
          -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
          bop -> 'a1

        val bop_rec :
          'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
          -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
          bop -> 'a1

        module BopNotations :
         sig
         end

        type matchkind = P4cub.Expr.matchkind =
        | MKExact
        | MKTernary
        | MKLpm

        val matchkind_rect : 'a1 -> 'a1 -> 'a1 -> matchkind -> 'a1

        val matchkind_rec : 'a1 -> 'a1 -> 'a1 -> matchkind -> 'a1

        val coq_MatchKindEqDec : matchkind coq_EqDec

        module MatchkindNotations :
         sig
         end

        type 'tags_t e = 'tags_t P4cub.Expr.e =
        | EBool of bool * 'tags_t
        | EBit of positive * coq_Z * 'tags_t
        | EInt of positive * coq_Z * 'tags_t
        | EVar of t * string * 'tags_t
        | ESlice of 'tags_t e * t * positive * positive * 'tags_t
        | ECast of t * 'tags_t e * 'tags_t
        | EUop of uop * t * 'tags_t e * 'tags_t
        | EBop of bop * t * t * 'tags_t e * 'tags_t e * 'tags_t
        | ETuple of 'tags_t e list * 'tags_t
        | EStruct of (string, t * 'tags_t e) F.fs * 'tags_t
        | EHeader of (string, t * 'tags_t e) F.fs * 'tags_t e * 'tags_t
        | EExprMember of string * t * 'tags_t e * 'tags_t
        | EError of string option * 'tags_t
        | EMatchKind of matchkind * 'tags_t
        | EHeaderStack of (string, t) F.fs * 'tags_t e list * positive
           * coq_Z * 'tags_t
        | EHeaderStackAccess of 'tags_t e * coq_Z * 'tags_t

        val e_rect :
          (bool -> 'a1 -> 'a2) -> (positive -> coq_Z -> 'a1 -> 'a2) ->
          (positive -> coq_Z -> 'a1 -> 'a2) -> (t -> string -> 'a1 -> 'a2) ->
          ('a1 e -> 'a2 -> t -> positive -> positive -> 'a1 -> 'a2) -> (t ->
          'a1 e -> 'a2 -> 'a1 -> 'a2) -> (uop -> t -> 'a1 e -> 'a2 -> 'a1 ->
          'a2) -> (bop -> t -> t -> 'a1 e -> 'a2 -> 'a1 e -> 'a2 -> 'a1 ->
          'a2) -> ('a1 e list -> 'a1 -> 'a2) -> ((string, t * 'a1 e) F.fs ->
          'a1 -> 'a2) -> ((string, t * 'a1 e) F.fs -> 'a1 e -> 'a2 -> 'a1 ->
          'a2) -> (string -> t -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (string
          option -> 'a1 -> 'a2) -> (matchkind -> 'a1 -> 'a2) -> ((string, t)
          F.fs -> 'a1 e list -> positive -> coq_Z -> 'a1 -> 'a2) -> ('a1 e ->
          'a2 -> coq_Z -> 'a1 -> 'a2) -> 'a1 e -> 'a2

        val e_rec :
          (bool -> 'a1 -> 'a2) -> (positive -> coq_Z -> 'a1 -> 'a2) ->
          (positive -> coq_Z -> 'a1 -> 'a2) -> (t -> string -> 'a1 -> 'a2) ->
          ('a1 e -> 'a2 -> t -> positive -> positive -> 'a1 -> 'a2) -> (t ->
          'a1 e -> 'a2 -> 'a1 -> 'a2) -> (uop -> t -> 'a1 e -> 'a2 -> 'a1 ->
          'a2) -> (bop -> t -> t -> 'a1 e -> 'a2 -> 'a1 e -> 'a2 -> 'a1 ->
          'a2) -> ('a1 e list -> 'a1 -> 'a2) -> ((string, t * 'a1 e) F.fs ->
          'a1 -> 'a2) -> ((string, t * 'a1 e) F.fs -> 'a1 e -> 'a2 -> 'a1 ->
          'a2) -> (string -> t -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (string
          option -> 'a1 -> 'a2) -> (matchkind -> 'a1 -> 'a2) -> ((string, t)
          F.fs -> 'a1 e list -> positive -> coq_Z -> 'a1 -> 'a2) -> ('a1 e ->
          'a2 -> coq_Z -> 'a1 -> 'a2) -> 'a1 e -> 'a2

        type 'tags_t args =
          (string, (t * 'tags_t e, t * 'tags_t e) paramarg) F.fs

        type 'tags_t arrowE =
          (string, t * 'tags_t e, t * 'tags_t e, t * 'tags_t e) arrow

        type 'tags_t constructor_arg = 'tags_t P4cub.Expr.constructor_arg =
        | CAExpr of 'tags_t e
        | CAName of string

        val constructor_arg_rect :
          ('a1 e -> 'a2) -> (string -> 'a2) -> 'a1 constructor_arg -> 'a2

        val constructor_arg_rec :
          ('a1 e -> 'a2) -> (string -> 'a2) -> 'a1 constructor_arg -> 'a2

        type 'tags_t constructor_args = (string, 'tags_t constructor_arg) F.fs

        module ExprNotations :
         sig
         end
       end

      type 'tags_t s = 'tags_t P4cub.Stmt.s =
      | SSkip of 'tags_t
      | SVardecl of E.t * string * 'tags_t
      | SAssign of E.t * 'tags_t E.e * 'tags_t E.e * 'tags_t
      | SConditional of E.t * 'tags_t E.e * 'tags_t s * 'tags_t s * 'tags_t
      | SSeq of 'tags_t s * 'tags_t s * 'tags_t
      | SBlock of 'tags_t s
      | SExternMethodCall of string * string * 'tags_t E.arrowE * 'tags_t
      | SFunCall of string * 'tags_t E.arrowE * 'tags_t
      | SActCall of string * 'tags_t E.args * 'tags_t
      | SReturnVoid of 'tags_t
      | SReturnFruit of E.t * 'tags_t E.e * 'tags_t
      | SExit of 'tags_t
      | SInvoke of string * 'tags_t
      | SApply of string * 'tags_t E.args * 'tags_t

      val s_rect :
        ('a1 -> 'a2) -> (E.t -> string -> 'a1 -> 'a2) -> (E.t -> 'a1 E.e ->
        'a1 E.e -> 'a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1 s -> 'a2 -> 'a1 s ->
        'a2 -> 'a1 -> 'a2) -> ('a1 s -> 'a2 -> 'a1 s -> 'a2 -> 'a1 -> 'a2) ->
        ('a1 s -> 'a2 -> 'a2) -> (string -> string -> 'a1 E.arrowE -> 'a1 ->
        'a2) -> (string -> 'a1 E.arrowE -> 'a1 -> 'a2) -> (string -> 'a1
        E.args -> 'a1 -> 'a2) -> ('a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1 ->
        'a2) -> ('a1 -> 'a2) -> (string -> 'a1 -> 'a2) -> (string -> 'a1
        E.args -> 'a1 -> 'a2) -> 'a1 s -> 'a2

      val s_rec :
        ('a1 -> 'a2) -> (E.t -> string -> 'a1 -> 'a2) -> (E.t -> 'a1 E.e ->
        'a1 E.e -> 'a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1 s -> 'a2 -> 'a1 s ->
        'a2 -> 'a1 -> 'a2) -> ('a1 s -> 'a2 -> 'a1 s -> 'a2 -> 'a1 -> 'a2) ->
        ('a1 s -> 'a2 -> 'a2) -> (string -> string -> 'a1 E.arrowE -> 'a1 ->
        'a2) -> (string -> 'a1 E.arrowE -> 'a1 -> 'a2) -> (string -> 'a1
        E.args -> 'a1 -> 'a2) -> ('a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1 ->
        'a2) -> ('a1 -> 'a2) -> (string -> 'a1 -> 'a2) -> (string -> 'a1
        E.args -> 'a1 -> 'a2) -> 'a1 s -> 'a2

      module StmtNotations :
       sig
       end
     end

    module C :
     sig
      type 'tags_t table = 'tags_t P4cub.Control.ControlDecl.table =
      | Table of ((Control.E.t * 'tags_t Control.E.e) * Control.E.matchkind)
                 list * string list

      val table_rect :
        (((Control.E.t * 'a1 Control.E.e) * Control.E.matchkind) list ->
        string list -> 'a2) -> 'a1 table -> 'a2

      val table_rec :
        (((Control.E.t * 'a1 Control.E.e) * Control.E.matchkind) list ->
        string list -> 'a2) -> 'a1 table -> 'a2

      type 'tags_t d = 'tags_t P4cub.Control.ControlDecl.d =
      | CDAction of string * Control.E.params * 'tags_t Control.S.s * 'tags_t
      | CDTable of string * 'tags_t table * 'tags_t
      | CDSeq of 'tags_t d * 'tags_t d * 'tags_t

      val d_rect :
        (string -> Control.E.params -> 'a1 Control.S.s -> 'a1 -> 'a2) ->
        (string -> 'a1 table -> 'a1 -> 'a2) -> ('a1 d -> 'a2 -> 'a1 d -> 'a2
        -> 'a1 -> 'a2) -> 'a1 d -> 'a2

      val d_rec :
        (string -> Control.E.params -> 'a1 Control.S.s -> 'a1 -> 'a2) ->
        (string -> 'a1 table -> 'a1 -> 'a2) -> ('a1 d -> 'a2 -> 'a1 d -> 'a2
        -> 'a1 -> 'a2) -> 'a1 d -> 'a2

      module ControlDeclNotations :
       sig
       end
     end

    module P :
     sig
      module E :
       sig
        type t = P4cub.Expr.t =
        | TBool
        | TBit of positive
        | TInt of positive
        | TError
        | TMatchKind
        | TTuple of t list
        | TStruct of (string, t) F.fs
        | THeader of (string, t) F.fs
        | THeaderStack of (string, t) F.fs * positive

        val t_rect :
          'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> 'a1 -> 'a1 -> (t
          list -> 'a1) -> ((string, t) F.fs -> 'a1) -> ((string, t) F.fs ->
          'a1) -> ((string, t) F.fs -> positive -> 'a1) -> t -> 'a1

        val t_rec :
          'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> 'a1 -> 'a1 -> (t
          list -> 'a1) -> ((string, t) F.fs -> 'a1) -> ((string, t) F.fs ->
          'a1) -> ((string, t) F.fs -> positive -> 'a1) -> t -> 'a1

        type params = (string, (t, t) paramarg) F.fs

        type arrowT = (string, t, t, t) arrow

        type ct = P4cub.Expr.ct =
        | CTType of t
        | CTControl of (string, ct) F.fs * params
        | CTParser of (string, ct) F.fs * params
        | CTPackage of (string, ct) F.fs
        | CTExtern of (string, ct) F.fs * (string, arrowT) F.fs

        val ct_rect :
          (t -> 'a1) -> ((string, ct) F.fs -> params -> 'a1) -> ((string, ct)
          F.fs -> params -> 'a1) -> ((string, ct) F.fs -> 'a1) -> ((string,
          ct) F.fs -> (string, arrowT) F.fs -> 'a1) -> ct -> 'a1

        val ct_rec :
          (t -> 'a1) -> ((string, ct) F.fs -> params -> 'a1) -> ((string, ct)
          F.fs -> params -> 'a1) -> ((string, ct) F.fs -> 'a1) -> ((string,
          ct) F.fs -> (string, arrowT) F.fs -> 'a1) -> ct -> 'a1

        type constructor_params = (string, ct) F.fs

        module TypeNotations :
         sig
         end

        type uop = P4cub.Expr.uop =
        | Not
        | BitNot
        | UMinus
        | IsValid
        | SetValid
        | SetInValid
        | NextIndex
        | Size
        | Push of positive
        | Pop of positive

        val uop_rect :
          'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (positive
          -> 'a1) -> (positive -> 'a1) -> uop -> 'a1

        val uop_rec :
          'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (positive
          -> 'a1) -> (positive -> 'a1) -> uop -> 'a1

        module UopNotations :
         sig
         end

        type bop = P4cub.Expr.bop =
        | Plus
        | PlusSat
        | Minus
        | MinusSat
        | Times
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

        val bop_rect :
          'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
          -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
          bop -> 'a1

        val bop_rec :
          'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
          -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
          bop -> 'a1

        module BopNotations :
         sig
         end

        type matchkind = P4cub.Expr.matchkind =
        | MKExact
        | MKTernary
        | MKLpm

        val matchkind_rect : 'a1 -> 'a1 -> 'a1 -> matchkind -> 'a1

        val matchkind_rec : 'a1 -> 'a1 -> 'a1 -> matchkind -> 'a1

        val coq_MatchKindEqDec : matchkind coq_EqDec

        module MatchkindNotations :
         sig
         end

        type 'tags_t e = 'tags_t P4cub.Expr.e =
        | EBool of bool * 'tags_t
        | EBit of positive * coq_Z * 'tags_t
        | EInt of positive * coq_Z * 'tags_t
        | EVar of t * string * 'tags_t
        | ESlice of 'tags_t e * t * positive * positive * 'tags_t
        | ECast of t * 'tags_t e * 'tags_t
        | EUop of uop * t * 'tags_t e * 'tags_t
        | EBop of bop * t * t * 'tags_t e * 'tags_t e * 'tags_t
        | ETuple of 'tags_t e list * 'tags_t
        | EStruct of (string, t * 'tags_t e) F.fs * 'tags_t
        | EHeader of (string, t * 'tags_t e) F.fs * 'tags_t e * 'tags_t
        | EExprMember of string * t * 'tags_t e * 'tags_t
        | EError of string option * 'tags_t
        | EMatchKind of matchkind * 'tags_t
        | EHeaderStack of (string, t) F.fs * 'tags_t e list * positive
           * coq_Z * 'tags_t
        | EHeaderStackAccess of 'tags_t e * coq_Z * 'tags_t

        val e_rect :
          (bool -> 'a1 -> 'a2) -> (positive -> coq_Z -> 'a1 -> 'a2) ->
          (positive -> coq_Z -> 'a1 -> 'a2) -> (t -> string -> 'a1 -> 'a2) ->
          ('a1 e -> 'a2 -> t -> positive -> positive -> 'a1 -> 'a2) -> (t ->
          'a1 e -> 'a2 -> 'a1 -> 'a2) -> (uop -> t -> 'a1 e -> 'a2 -> 'a1 ->
          'a2) -> (bop -> t -> t -> 'a1 e -> 'a2 -> 'a1 e -> 'a2 -> 'a1 ->
          'a2) -> ('a1 e list -> 'a1 -> 'a2) -> ((string, t * 'a1 e) F.fs ->
          'a1 -> 'a2) -> ((string, t * 'a1 e) F.fs -> 'a1 e -> 'a2 -> 'a1 ->
          'a2) -> (string -> t -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (string
          option -> 'a1 -> 'a2) -> (matchkind -> 'a1 -> 'a2) -> ((string, t)
          F.fs -> 'a1 e list -> positive -> coq_Z -> 'a1 -> 'a2) -> ('a1 e ->
          'a2 -> coq_Z -> 'a1 -> 'a2) -> 'a1 e -> 'a2

        val e_rec :
          (bool -> 'a1 -> 'a2) -> (positive -> coq_Z -> 'a1 -> 'a2) ->
          (positive -> coq_Z -> 'a1 -> 'a2) -> (t -> string -> 'a1 -> 'a2) ->
          ('a1 e -> 'a2 -> t -> positive -> positive -> 'a1 -> 'a2) -> (t ->
          'a1 e -> 'a2 -> 'a1 -> 'a2) -> (uop -> t -> 'a1 e -> 'a2 -> 'a1 ->
          'a2) -> (bop -> t -> t -> 'a1 e -> 'a2 -> 'a1 e -> 'a2 -> 'a1 ->
          'a2) -> ('a1 e list -> 'a1 -> 'a2) -> ((string, t * 'a1 e) F.fs ->
          'a1 -> 'a2) -> ((string, t * 'a1 e) F.fs -> 'a1 e -> 'a2 -> 'a1 ->
          'a2) -> (string -> t -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (string
          option -> 'a1 -> 'a2) -> (matchkind -> 'a1 -> 'a2) -> ((string, t)
          F.fs -> 'a1 e list -> positive -> coq_Z -> 'a1 -> 'a2) -> ('a1 e ->
          'a2 -> coq_Z -> 'a1 -> 'a2) -> 'a1 e -> 'a2

        type 'tags_t args =
          (string, (t * 'tags_t e, t * 'tags_t e) paramarg) F.fs

        type 'tags_t arrowE =
          (string, t * 'tags_t e, t * 'tags_t e, t * 'tags_t e) arrow

        type 'tags_t constructor_arg = 'tags_t P4cub.Expr.constructor_arg =
        | CAExpr of 'tags_t e
        | CAName of string

        val constructor_arg_rect :
          ('a1 e -> 'a2) -> (string -> 'a2) -> 'a1 constructor_arg -> 'a2

        val constructor_arg_rec :
          ('a1 e -> 'a2) -> (string -> 'a2) -> 'a1 constructor_arg -> 'a2

        type 'tags_t constructor_args = (string, 'tags_t constructor_arg) F.fs

        module ExprNotations :
         sig
         end
       end

      module S :
       sig
        module E :
         sig
          type t = P4cub.Expr.t =
          | TBool
          | TBit of positive
          | TInt of positive
          | TError
          | TMatchKind
          | TTuple of t list
          | TStruct of (string, t) F.fs
          | THeader of (string, t) F.fs
          | THeaderStack of (string, t) F.fs * positive

          val t_rect :
            'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> 'a1 -> 'a1 -> (t
            list -> 'a1) -> ((string, t) F.fs -> 'a1) -> ((string, t) F.fs ->
            'a1) -> ((string, t) F.fs -> positive -> 'a1) -> t -> 'a1

          val t_rec :
            'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> 'a1 -> 'a1 -> (t
            list -> 'a1) -> ((string, t) F.fs -> 'a1) -> ((string, t) F.fs ->
            'a1) -> ((string, t) F.fs -> positive -> 'a1) -> t -> 'a1

          type params = (string, (t, t) paramarg) F.fs

          type arrowT = (string, t, t, t) arrow

          type ct = P4cub.Expr.ct =
          | CTType of t
          | CTControl of (string, ct) F.fs * params
          | CTParser of (string, ct) F.fs * params
          | CTPackage of (string, ct) F.fs
          | CTExtern of (string, ct) F.fs * (string, arrowT) F.fs

          val ct_rect :
            (t -> 'a1) -> ((string, ct) F.fs -> params -> 'a1) -> ((string,
            ct) F.fs -> params -> 'a1) -> ((string, ct) F.fs -> 'a1) ->
            ((string, ct) F.fs -> (string, arrowT) F.fs -> 'a1) -> ct -> 'a1

          val ct_rec :
            (t -> 'a1) -> ((string, ct) F.fs -> params -> 'a1) -> ((string,
            ct) F.fs -> params -> 'a1) -> ((string, ct) F.fs -> 'a1) ->
            ((string, ct) F.fs -> (string, arrowT) F.fs -> 'a1) -> ct -> 'a1

          type constructor_params = (string, ct) F.fs

          module TypeNotations :
           sig
           end

          type uop = P4cub.Expr.uop =
          | Not
          | BitNot
          | UMinus
          | IsValid
          | SetValid
          | SetInValid
          | NextIndex
          | Size
          | Push of positive
          | Pop of positive

          val uop_rect :
            'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (positive
            -> 'a1) -> (positive -> 'a1) -> uop -> 'a1

          val uop_rec :
            'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (positive
            -> 'a1) -> (positive -> 'a1) -> uop -> 'a1

          module UopNotations :
           sig
           end

          type bop = P4cub.Expr.bop =
          | Plus
          | PlusSat
          | Minus
          | MinusSat
          | Times
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

          val bop_rect :
            'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
            'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
            'a1 -> bop -> 'a1

          val bop_rec :
            'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
            'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
            'a1 -> bop -> 'a1

          module BopNotations :
           sig
           end

          type matchkind = P4cub.Expr.matchkind =
          | MKExact
          | MKTernary
          | MKLpm

          val matchkind_rect : 'a1 -> 'a1 -> 'a1 -> matchkind -> 'a1

          val matchkind_rec : 'a1 -> 'a1 -> 'a1 -> matchkind -> 'a1

          val coq_MatchKindEqDec : matchkind coq_EqDec

          module MatchkindNotations :
           sig
           end

          type 'tags_t e = 'tags_t P4cub.Expr.e =
          | EBool of bool * 'tags_t
          | EBit of positive * coq_Z * 'tags_t
          | EInt of positive * coq_Z * 'tags_t
          | EVar of t * string * 'tags_t
          | ESlice of 'tags_t e * t * positive * positive * 'tags_t
          | ECast of t * 'tags_t e * 'tags_t
          | EUop of uop * t * 'tags_t e * 'tags_t
          | EBop of bop * t * t * 'tags_t e * 'tags_t e * 'tags_t
          | ETuple of 'tags_t e list * 'tags_t
          | EStruct of (string, t * 'tags_t e) F.fs * 'tags_t
          | EHeader of (string, t * 'tags_t e) F.fs * 'tags_t e * 'tags_t
          | EExprMember of string * t * 'tags_t e * 'tags_t
          | EError of string option * 'tags_t
          | EMatchKind of matchkind * 'tags_t
          | EHeaderStack of (string, t) F.fs * 'tags_t e list * positive
             * coq_Z * 'tags_t
          | EHeaderStackAccess of 'tags_t e * coq_Z * 'tags_t

          val e_rect :
            (bool -> 'a1 -> 'a2) -> (positive -> coq_Z -> 'a1 -> 'a2) ->
            (positive -> coq_Z -> 'a1 -> 'a2) -> (t -> string -> 'a1 -> 'a2)
            -> ('a1 e -> 'a2 -> t -> positive -> positive -> 'a1 -> 'a2) ->
            (t -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (uop -> t -> 'a1 e -> 'a2 ->
            'a1 -> 'a2) -> (bop -> t -> t -> 'a1 e -> 'a2 -> 'a1 e -> 'a2 ->
            'a1 -> 'a2) -> ('a1 e list -> 'a1 -> 'a2) -> ((string, t * 'a1 e)
            F.fs -> 'a1 -> 'a2) -> ((string, t * 'a1 e) F.fs -> 'a1 e -> 'a2
            -> 'a1 -> 'a2) -> (string -> t -> 'a1 e -> 'a2 -> 'a1 -> 'a2) ->
            (string option -> 'a1 -> 'a2) -> (matchkind -> 'a1 -> 'a2) ->
            ((string, t) F.fs -> 'a1 e list -> positive -> coq_Z -> 'a1 ->
            'a2) -> ('a1 e -> 'a2 -> coq_Z -> 'a1 -> 'a2) -> 'a1 e -> 'a2

          val e_rec :
            (bool -> 'a1 -> 'a2) -> (positive -> coq_Z -> 'a1 -> 'a2) ->
            (positive -> coq_Z -> 'a1 -> 'a2) -> (t -> string -> 'a1 -> 'a2)
            -> ('a1 e -> 'a2 -> t -> positive -> positive -> 'a1 -> 'a2) ->
            (t -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (uop -> t -> 'a1 e -> 'a2 ->
            'a1 -> 'a2) -> (bop -> t -> t -> 'a1 e -> 'a2 -> 'a1 e -> 'a2 ->
            'a1 -> 'a2) -> ('a1 e list -> 'a1 -> 'a2) -> ((string, t * 'a1 e)
            F.fs -> 'a1 -> 'a2) -> ((string, t * 'a1 e) F.fs -> 'a1 e -> 'a2
            -> 'a1 -> 'a2) -> (string -> t -> 'a1 e -> 'a2 -> 'a1 -> 'a2) ->
            (string option -> 'a1 -> 'a2) -> (matchkind -> 'a1 -> 'a2) ->
            ((string, t) F.fs -> 'a1 e list -> positive -> coq_Z -> 'a1 ->
            'a2) -> ('a1 e -> 'a2 -> coq_Z -> 'a1 -> 'a2) -> 'a1 e -> 'a2

          type 'tags_t args =
            (string, (t * 'tags_t e, t * 'tags_t e) paramarg) F.fs

          type 'tags_t arrowE =
            (string, t * 'tags_t e, t * 'tags_t e, t * 'tags_t e) arrow

          type 'tags_t constructor_arg = 'tags_t P4cub.Expr.constructor_arg =
          | CAExpr of 'tags_t e
          | CAName of string

          val constructor_arg_rect :
            ('a1 e -> 'a2) -> (string -> 'a2) -> 'a1 constructor_arg -> 'a2

          val constructor_arg_rec :
            ('a1 e -> 'a2) -> (string -> 'a2) -> 'a1 constructor_arg -> 'a2

          type 'tags_t constructor_args =
            (string, 'tags_t constructor_arg) F.fs

          module ExprNotations :
           sig
           end
         end

        type 'tags_t s = 'tags_t P4cub.Stmt.s =
        | SSkip of 'tags_t
        | SVardecl of E.t * string * 'tags_t
        | SAssign of E.t * 'tags_t E.e * 'tags_t E.e * 'tags_t
        | SConditional of E.t * 'tags_t E.e * 'tags_t s * 'tags_t s * 'tags_t
        | SSeq of 'tags_t s * 'tags_t s * 'tags_t
        | SBlock of 'tags_t s
        | SExternMethodCall of string * string * 'tags_t E.arrowE * 'tags_t
        | SFunCall of string * 'tags_t E.arrowE * 'tags_t
        | SActCall of string * 'tags_t E.args * 'tags_t
        | SReturnVoid of 'tags_t
        | SReturnFruit of E.t * 'tags_t E.e * 'tags_t
        | SExit of 'tags_t
        | SInvoke of string * 'tags_t
        | SApply of string * 'tags_t E.args * 'tags_t

        val s_rect :
          ('a1 -> 'a2) -> (E.t -> string -> 'a1 -> 'a2) -> (E.t -> 'a1 E.e ->
          'a1 E.e -> 'a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1 s -> 'a2 -> 'a1 s
          -> 'a2 -> 'a1 -> 'a2) -> ('a1 s -> 'a2 -> 'a1 s -> 'a2 -> 'a1 ->
          'a2) -> ('a1 s -> 'a2 -> 'a2) -> (string -> string -> 'a1 E.arrowE
          -> 'a1 -> 'a2) -> (string -> 'a1 E.arrowE -> 'a1 -> 'a2) -> (string
          -> 'a1 E.args -> 'a1 -> 'a2) -> ('a1 -> 'a2) -> (E.t -> 'a1 E.e ->
          'a1 -> 'a2) -> ('a1 -> 'a2) -> (string -> 'a1 -> 'a2) -> (string ->
          'a1 E.args -> 'a1 -> 'a2) -> 'a1 s -> 'a2

        val s_rec :
          ('a1 -> 'a2) -> (E.t -> string -> 'a1 -> 'a2) -> (E.t -> 'a1 E.e ->
          'a1 E.e -> 'a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1 s -> 'a2 -> 'a1 s
          -> 'a2 -> 'a1 -> 'a2) -> ('a1 s -> 'a2 -> 'a1 s -> 'a2 -> 'a1 ->
          'a2) -> ('a1 s -> 'a2 -> 'a2) -> (string -> string -> 'a1 E.arrowE
          -> 'a1 -> 'a2) -> (string -> 'a1 E.arrowE -> 'a1 -> 'a2) -> (string
          -> 'a1 E.args -> 'a1 -> 'a2) -> ('a1 -> 'a2) -> (E.t -> 'a1 E.e ->
          'a1 -> 'a2) -> ('a1 -> 'a2) -> (string -> 'a1 -> 'a2) -> (string ->
          'a1 E.args -> 'a1 -> 'a2) -> 'a1 s -> 'a2

        module StmtNotations :
         sig
         end
       end

      type state = P4cub.Parser.state =
      | STStart
      | STAccept
      | STReject
      | STName of string

      val state_rect : 'a1 -> 'a1 -> 'a1 -> (string -> 'a1) -> state -> 'a1

      val state_rec : 'a1 -> 'a1 -> 'a1 -> (string -> 'a1) -> state -> 'a1

      type pat = P4cub.Parser.pat =
      | PATWild
      | PATMask of pat * pat
      | PATRange of pat * pat
      | PATBit of positive * coq_Z
      | PATInt of positive * coq_Z
      | PATTuple of pat list

      val pat_rect :
        'a1 -> (pat -> 'a1 -> pat -> 'a1 -> 'a1) -> (pat -> 'a1 -> pat -> 'a1
        -> 'a1) -> (positive -> coq_Z -> 'a1) -> (positive -> coq_Z -> 'a1)
        -> (pat list -> 'a1) -> pat -> 'a1

      val pat_rec :
        'a1 -> (pat -> 'a1 -> pat -> 'a1 -> 'a1) -> (pat -> 'a1 -> pat -> 'a1
        -> 'a1) -> (positive -> coq_Z -> 'a1) -> (positive -> coq_Z -> 'a1)
        -> (pat list -> 'a1) -> pat -> 'a1

      type 'tags_t e = 'tags_t P4cub.Parser.e =
      | PGoto of state * 'tags_t
      | PSelect of 'tags_t E.e * 'tags_t e * (pat, 'tags_t e) F.fs * 'tags_t

      val e_rect :
        (state -> 'a1 -> 'a2) -> ('a1 E.e -> 'a1 e -> 'a2 -> (pat, 'a1 e)
        F.fs -> 'a1 -> 'a2) -> 'a1 e -> 'a2

      val e_rec :
        (state -> 'a1 -> 'a2) -> ('a1 E.e -> 'a1 e -> 'a2 -> (pat, 'a1 e)
        F.fs -> 'a1 -> 'a2) -> 'a1 e -> 'a2

      type 'tags_t state_block = 'tags_t P4cub.Parser.state_block =
      | State of 'tags_t S.s * 'tags_t e

      val state_block_rect :
        ('a1 S.s -> 'a1 e -> 'a2) -> 'a1 state_block -> 'a2

      val state_block_rec :
        ('a1 S.s -> 'a1 e -> 'a2) -> 'a1 state_block -> 'a2

      module ParserNotations :
       sig
       end
     end

    type 'tags_t d = 'tags_t P4cub.TopDecl.d =
    | TPInstantiate of string * string * 'tags_t E.constructor_args * 'tags_t
    | TPExtern of string * E.constructor_params * (string, E.arrowT) F.fs
       * 'tags_t
    | TPControl of string * E.constructor_params * E.params * 'tags_t C.d
       * 'tags_t S.s * 'tags_t
    | TPParser of string * E.constructor_params * E.params
       * 'tags_t P.state_block * (string, 'tags_t P.state_block) F.fs
       * 'tags_t
    | TPFunction of string * E.arrowT * 'tags_t S.s * 'tags_t
    | TPPackage of string * E.constructor_params * 'tags_t
    | TPSeq of 'tags_t d * 'tags_t d * 'tags_t

    val d_rect :
      (string -> string -> 'a1 E.constructor_args -> 'a1 -> 'a2) -> (string
      -> E.constructor_params -> (string, E.arrowT) F.fs -> 'a1 -> 'a2) ->
      (string -> E.constructor_params -> E.params -> 'a1 C.d -> 'a1 S.s ->
      'a1 -> 'a2) -> (string -> E.constructor_params -> E.params -> 'a1
      P.state_block -> (string, 'a1 P.state_block) F.fs -> 'a1 -> 'a2) ->
      (string -> E.arrowT -> 'a1 S.s -> 'a1 -> 'a2) -> (string ->
      E.constructor_params -> 'a1 -> 'a2) -> ('a1 d -> 'a2 -> 'a1 d -> 'a2 ->
      'a1 -> 'a2) -> 'a1 d -> 'a2

    val d_rec :
      (string -> string -> 'a1 E.constructor_args -> 'a1 -> 'a2) -> (string
      -> E.constructor_params -> (string, E.arrowT) F.fs -> 'a1 -> 'a2) ->
      (string -> E.constructor_params -> E.params -> 'a1 C.d -> 'a1 S.s ->
      'a1 -> 'a2) -> (string -> E.constructor_params -> E.params -> 'a1
      P.state_block -> (string, 'a1 P.state_block) F.fs -> 'a1 -> 'a2) ->
      (string -> E.arrowT -> 'a1 S.s -> 'a1 -> 'a2) -> (string ->
      E.constructor_params -> 'a1 -> 'a2) -> ('a1 d -> 'a2 -> 'a1 d -> 'a2 ->
      'a1 -> 'a2) -> 'a1 d -> 'a2

    module TopDeclNotations :
     sig
     end
   end

  module P4cubNotations :
   sig
   end
 end
module Coq__1 : module type of struct include P end

module E :
 sig
  type t = P4cub.Expr.t =
  | TBool
  | TBit of positive
  | TInt of positive
  | TError
  | TMatchKind
  | TTuple of t list
  | TStruct of (string, t) P.F.fs
  | THeader of (string, t) P.F.fs
  | THeaderStack of (string, t) P.F.fs * positive

  val t_rect :
    'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> 'a1 -> 'a1 -> (t list ->
    'a1) -> ((string, t) P.F.fs -> 'a1) -> ((string, t) P.F.fs -> 'a1) ->
    ((string, t) P.F.fs -> positive -> 'a1) -> t -> 'a1

  val t_rec :
    'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> 'a1 -> 'a1 -> (t list ->
    'a1) -> ((string, t) P.F.fs -> 'a1) -> ((string, t) P.F.fs -> 'a1) ->
    ((string, t) P.F.fs -> positive -> 'a1) -> t -> 'a1

  type params = (string, (t, t) P.paramarg) P.F.fs

  type arrowT = (string, t, t, t) P.arrow

  type ct = P4cub.Expr.ct =
  | CTType of t
  | CTControl of (string, ct) P.F.fs * params
  | CTParser of (string, ct) P.F.fs * params
  | CTPackage of (string, ct) P.F.fs
  | CTExtern of (string, ct) P.F.fs * (string, arrowT) P.F.fs

  val ct_rect :
    (t -> 'a1) -> ((string, ct) P.F.fs -> params -> 'a1) -> ((string, ct)
    P.F.fs -> params -> 'a1) -> ((string, ct) P.F.fs -> 'a1) -> ((string, ct)
    P.F.fs -> (string, arrowT) P.F.fs -> 'a1) -> ct -> 'a1

  val ct_rec :
    (t -> 'a1) -> ((string, ct) P.F.fs -> params -> 'a1) -> ((string, ct)
    P.F.fs -> params -> 'a1) -> ((string, ct) P.F.fs -> 'a1) -> ((string, ct)
    P.F.fs -> (string, arrowT) P.F.fs -> 'a1) -> ct -> 'a1

  type constructor_params = (string, ct) P.F.fs

  module TypeNotations :
   sig
   end

  type uop = P4cub.Expr.uop =
  | Not
  | BitNot
  | UMinus
  | IsValid
  | SetValid
  | SetInValid
  | NextIndex
  | Size
  | Push of positive
  | Pop of positive

  val uop_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (positive -> 'a1)
    -> (positive -> 'a1) -> uop -> 'a1

  val uop_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (positive -> 'a1)
    -> (positive -> 'a1) -> uop -> 'a1

  module UopNotations :
   sig
   end

  type bop = P4cub.Expr.bop =
  | Plus
  | PlusSat
  | Minus
  | MinusSat
  | Times
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

  val bop_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> bop -> 'a1

  val bop_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> bop -> 'a1

  module BopNotations :
   sig
   end

  type matchkind = P4cub.Expr.matchkind =
  | MKExact
  | MKTernary
  | MKLpm

  val matchkind_rect : 'a1 -> 'a1 -> 'a1 -> matchkind -> 'a1

  val matchkind_rec : 'a1 -> 'a1 -> 'a1 -> matchkind -> 'a1

  val coq_MatchKindEqDec : matchkind coq_EqDec

  module MatchkindNotations :
   sig
   end

  type 'tags_t e = 'tags_t P4cub.Expr.e =
  | EBool of bool * 'tags_t
  | EBit of positive * coq_Z * 'tags_t
  | EInt of positive * coq_Z * 'tags_t
  | EVar of t * string * 'tags_t
  | ESlice of 'tags_t e * t * positive * positive * 'tags_t
  | ECast of t * 'tags_t e * 'tags_t
  | EUop of uop * t * 'tags_t e * 'tags_t
  | EBop of bop * t * t * 'tags_t e * 'tags_t e * 'tags_t
  | ETuple of 'tags_t e list * 'tags_t
  | EStruct of (string, t * 'tags_t e) P.F.fs * 'tags_t
  | EHeader of (string, t * 'tags_t e) P.F.fs * 'tags_t e * 'tags_t
  | EExprMember of string * t * 'tags_t e * 'tags_t
  | EError of string option * 'tags_t
  | EMatchKind of matchkind * 'tags_t
  | EHeaderStack of (string, t) P.F.fs * 'tags_t e list * positive * 
     coq_Z * 'tags_t
  | EHeaderStackAccess of 'tags_t e * coq_Z * 'tags_t

  val e_rect :
    (bool -> 'a1 -> 'a2) -> (positive -> coq_Z -> 'a1 -> 'a2) -> (positive ->
    coq_Z -> 'a1 -> 'a2) -> (t -> string -> 'a1 -> 'a2) -> ('a1 e -> 'a2 -> t
    -> positive -> positive -> 'a1 -> 'a2) -> (t -> 'a1 e -> 'a2 -> 'a1 ->
    'a2) -> (uop -> t -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (bop -> t -> t -> 'a1
    e -> 'a2 -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> ('a1 e list -> 'a1 -> 'a2) ->
    ((string, t * 'a1 e) P.F.fs -> 'a1 -> 'a2) -> ((string, t * 'a1 e) P.F.fs
    -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (string -> t -> 'a1 e -> 'a2 -> 'a1 ->
    'a2) -> (string option -> 'a1 -> 'a2) -> (matchkind -> 'a1 -> 'a2) ->
    ((string, t) P.F.fs -> 'a1 e list -> positive -> coq_Z -> 'a1 -> 'a2) ->
    ('a1 e -> 'a2 -> coq_Z -> 'a1 -> 'a2) -> 'a1 e -> 'a2

  val e_rec :
    (bool -> 'a1 -> 'a2) -> (positive -> coq_Z -> 'a1 -> 'a2) -> (positive ->
    coq_Z -> 'a1 -> 'a2) -> (t -> string -> 'a1 -> 'a2) -> ('a1 e -> 'a2 -> t
    -> positive -> positive -> 'a1 -> 'a2) -> (t -> 'a1 e -> 'a2 -> 'a1 ->
    'a2) -> (uop -> t -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (bop -> t -> t -> 'a1
    e -> 'a2 -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> ('a1 e list -> 'a1 -> 'a2) ->
    ((string, t * 'a1 e) P.F.fs -> 'a1 -> 'a2) -> ((string, t * 'a1 e) P.F.fs
    -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (string -> t -> 'a1 e -> 'a2 -> 'a1 ->
    'a2) -> (string option -> 'a1 -> 'a2) -> (matchkind -> 'a1 -> 'a2) ->
    ((string, t) P.F.fs -> 'a1 e list -> positive -> coq_Z -> 'a1 -> 'a2) ->
    ('a1 e -> 'a2 -> coq_Z -> 'a1 -> 'a2) -> 'a1 e -> 'a2

  type 'tags_t args =
    (string, (t * 'tags_t e, t * 'tags_t e) P.paramarg) P.F.fs

  type 'tags_t arrowE =
    (string, t * 'tags_t e, t * 'tags_t e, t * 'tags_t e) P.arrow

  type 'tags_t constructor_arg = 'tags_t P4cub.Expr.constructor_arg =
  | CAExpr of 'tags_t e
  | CAName of string

  val constructor_arg_rect :
    ('a1 e -> 'a2) -> (string -> 'a2) -> 'a1 constructor_arg -> 'a2

  val constructor_arg_rec :
    ('a1 e -> 'a2) -> (string -> 'a2) -> 'a1 constructor_arg -> 'a2

  type 'tags_t constructor_args = (string, 'tags_t constructor_arg) P.F.fs

  module ExprNotations :
   sig
   end
 end

module PA :
 sig
  module E :
   sig
    type t = P4cub.Expr.t =
    | TBool
    | TBit of positive
    | TInt of positive
    | TError
    | TMatchKind
    | TTuple of t list
    | TStruct of (string, t) P.F.fs
    | THeader of (string, t) P.F.fs
    | THeaderStack of (string, t) P.F.fs * positive

    val t_rect :
      'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> 'a1 -> 'a1 -> (t list
      -> 'a1) -> ((string, t) P.F.fs -> 'a1) -> ((string, t) P.F.fs -> 'a1)
      -> ((string, t) P.F.fs -> positive -> 'a1) -> t -> 'a1

    val t_rec :
      'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> 'a1 -> 'a1 -> (t list
      -> 'a1) -> ((string, t) P.F.fs -> 'a1) -> ((string, t) P.F.fs -> 'a1)
      -> ((string, t) P.F.fs -> positive -> 'a1) -> t -> 'a1

    type params = (string, (t, t) P.paramarg) P.F.fs

    type arrowT = (string, t, t, t) P.arrow

    type ct = P4cub.Expr.ct =
    | CTType of t
    | CTControl of (string, ct) P.F.fs * params
    | CTParser of (string, ct) P.F.fs * params
    | CTPackage of (string, ct) P.F.fs
    | CTExtern of (string, ct) P.F.fs * (string, arrowT) P.F.fs

    val ct_rect :
      (t -> 'a1) -> ((string, ct) P.F.fs -> params -> 'a1) -> ((string, ct)
      P.F.fs -> params -> 'a1) -> ((string, ct) P.F.fs -> 'a1) -> ((string,
      ct) P.F.fs -> (string, arrowT) P.F.fs -> 'a1) -> ct -> 'a1

    val ct_rec :
      (t -> 'a1) -> ((string, ct) P.F.fs -> params -> 'a1) -> ((string, ct)
      P.F.fs -> params -> 'a1) -> ((string, ct) P.F.fs -> 'a1) -> ((string,
      ct) P.F.fs -> (string, arrowT) P.F.fs -> 'a1) -> ct -> 'a1

    type constructor_params = (string, ct) P.F.fs

    module TypeNotations :
     sig
     end

    type uop = P4cub.Expr.uop =
    | Not
    | BitNot
    | UMinus
    | IsValid
    | SetValid
    | SetInValid
    | NextIndex
    | Size
    | Push of positive
    | Pop of positive

    val uop_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (positive ->
      'a1) -> (positive -> 'a1) -> uop -> 'a1

    val uop_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (positive ->
      'a1) -> (positive -> 'a1) -> uop -> 'a1

    module UopNotations :
     sig
     end

    type bop = P4cub.Expr.bop =
    | Plus
    | PlusSat
    | Minus
    | MinusSat
    | Times
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

    val bop_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> bop ->
      'a1

    val bop_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> bop ->
      'a1

    module BopNotations :
     sig
     end

    type matchkind = P4cub.Expr.matchkind =
    | MKExact
    | MKTernary
    | MKLpm

    val matchkind_rect : 'a1 -> 'a1 -> 'a1 -> matchkind -> 'a1

    val matchkind_rec : 'a1 -> 'a1 -> 'a1 -> matchkind -> 'a1

    val coq_MatchKindEqDec : matchkind coq_EqDec

    module MatchkindNotations :
     sig
     end

    type 'tags_t e = 'tags_t P4cub.Expr.e =
    | EBool of bool * 'tags_t
    | EBit of positive * coq_Z * 'tags_t
    | EInt of positive * coq_Z * 'tags_t
    | EVar of t * string * 'tags_t
    | ESlice of 'tags_t e * t * positive * positive * 'tags_t
    | ECast of t * 'tags_t e * 'tags_t
    | EUop of uop * t * 'tags_t e * 'tags_t
    | EBop of bop * t * t * 'tags_t e * 'tags_t e * 'tags_t
    | ETuple of 'tags_t e list * 'tags_t
    | EStruct of (string, t * 'tags_t e) P.F.fs * 'tags_t
    | EHeader of (string, t * 'tags_t e) P.F.fs * 'tags_t e * 'tags_t
    | EExprMember of string * t * 'tags_t e * 'tags_t
    | EError of string option * 'tags_t
    | EMatchKind of matchkind * 'tags_t
    | EHeaderStack of (string, t) P.F.fs * 'tags_t e list * positive * 
       coq_Z * 'tags_t
    | EHeaderStackAccess of 'tags_t e * coq_Z * 'tags_t

    val e_rect :
      (bool -> 'a1 -> 'a2) -> (positive -> coq_Z -> 'a1 -> 'a2) -> (positive
      -> coq_Z -> 'a1 -> 'a2) -> (t -> string -> 'a1 -> 'a2) -> ('a1 e -> 'a2
      -> t -> positive -> positive -> 'a1 -> 'a2) -> (t -> 'a1 e -> 'a2 ->
      'a1 -> 'a2) -> (uop -> t -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (bop -> t ->
      t -> 'a1 e -> 'a2 -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> ('a1 e list -> 'a1
      -> 'a2) -> ((string, t * 'a1 e) P.F.fs -> 'a1 -> 'a2) -> ((string,
      t * 'a1 e) P.F.fs -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (string -> t -> 'a1
      e -> 'a2 -> 'a1 -> 'a2) -> (string option -> 'a1 -> 'a2) -> (matchkind
      -> 'a1 -> 'a2) -> ((string, t) P.F.fs -> 'a1 e list -> positive ->
      coq_Z -> 'a1 -> 'a2) -> ('a1 e -> 'a2 -> coq_Z -> 'a1 -> 'a2) -> 'a1 e
      -> 'a2

    val e_rec :
      (bool -> 'a1 -> 'a2) -> (positive -> coq_Z -> 'a1 -> 'a2) -> (positive
      -> coq_Z -> 'a1 -> 'a2) -> (t -> string -> 'a1 -> 'a2) -> ('a1 e -> 'a2
      -> t -> positive -> positive -> 'a1 -> 'a2) -> (t -> 'a1 e -> 'a2 ->
      'a1 -> 'a2) -> (uop -> t -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (bop -> t ->
      t -> 'a1 e -> 'a2 -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> ('a1 e list -> 'a1
      -> 'a2) -> ((string, t * 'a1 e) P.F.fs -> 'a1 -> 'a2) -> ((string,
      t * 'a1 e) P.F.fs -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (string -> t -> 'a1
      e -> 'a2 -> 'a1 -> 'a2) -> (string option -> 'a1 -> 'a2) -> (matchkind
      -> 'a1 -> 'a2) -> ((string, t) P.F.fs -> 'a1 e list -> positive ->
      coq_Z -> 'a1 -> 'a2) -> ('a1 e -> 'a2 -> coq_Z -> 'a1 -> 'a2) -> 'a1 e
      -> 'a2

    type 'tags_t args =
      (string, (t * 'tags_t e, t * 'tags_t e) P.paramarg) P.F.fs

    type 'tags_t arrowE =
      (string, t * 'tags_t e, t * 'tags_t e, t * 'tags_t e) P.arrow

    type 'tags_t constructor_arg = 'tags_t P4cub.Expr.constructor_arg =
    | CAExpr of 'tags_t e
    | CAName of string

    val constructor_arg_rect :
      ('a1 e -> 'a2) -> (string -> 'a2) -> 'a1 constructor_arg -> 'a2

    val constructor_arg_rec :
      ('a1 e -> 'a2) -> (string -> 'a2) -> 'a1 constructor_arg -> 'a2

    type 'tags_t constructor_args = (string, 'tags_t constructor_arg) P.F.fs

    module ExprNotations :
     sig
     end
   end

  module S :
   sig
    module E :
     sig
      type t = P4cub.Expr.t =
      | TBool
      | TBit of positive
      | TInt of positive
      | TError
      | TMatchKind
      | TTuple of t list
      | TStruct of (string, t) P.F.fs
      | THeader of (string, t) P.F.fs
      | THeaderStack of (string, t) P.F.fs * positive

      val t_rect :
        'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> 'a1 -> 'a1 -> (t
        list -> 'a1) -> ((string, t) P.F.fs -> 'a1) -> ((string, t) P.F.fs ->
        'a1) -> ((string, t) P.F.fs -> positive -> 'a1) -> t -> 'a1

      val t_rec :
        'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> 'a1 -> 'a1 -> (t
        list -> 'a1) -> ((string, t) P.F.fs -> 'a1) -> ((string, t) P.F.fs ->
        'a1) -> ((string, t) P.F.fs -> positive -> 'a1) -> t -> 'a1

      type params = (string, (t, t) P.paramarg) P.F.fs

      type arrowT = (string, t, t, t) P.arrow

      type ct = P4cub.Expr.ct =
      | CTType of t
      | CTControl of (string, ct) P.F.fs * params
      | CTParser of (string, ct) P.F.fs * params
      | CTPackage of (string, ct) P.F.fs
      | CTExtern of (string, ct) P.F.fs * (string, arrowT) P.F.fs

      val ct_rect :
        (t -> 'a1) -> ((string, ct) P.F.fs -> params -> 'a1) -> ((string, ct)
        P.F.fs -> params -> 'a1) -> ((string, ct) P.F.fs -> 'a1) -> ((string,
        ct) P.F.fs -> (string, arrowT) P.F.fs -> 'a1) -> ct -> 'a1

      val ct_rec :
        (t -> 'a1) -> ((string, ct) P.F.fs -> params -> 'a1) -> ((string, ct)
        P.F.fs -> params -> 'a1) -> ((string, ct) P.F.fs -> 'a1) -> ((string,
        ct) P.F.fs -> (string, arrowT) P.F.fs -> 'a1) -> ct -> 'a1

      type constructor_params = (string, ct) P.F.fs

      module TypeNotations :
       sig
       end

      type uop = P4cub.Expr.uop =
      | Not
      | BitNot
      | UMinus
      | IsValid
      | SetValid
      | SetInValid
      | NextIndex
      | Size
      | Push of positive
      | Pop of positive

      val uop_rect :
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (positive ->
        'a1) -> (positive -> 'a1) -> uop -> 'a1

      val uop_rec :
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (positive ->
        'a1) -> (positive -> 'a1) -> uop -> 'a1

      module UopNotations :
       sig
       end

      type bop = P4cub.Expr.bop =
      | Plus
      | PlusSat
      | Minus
      | MinusSat
      | Times
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

      val bop_rect :
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> bop ->
        'a1

      val bop_rec :
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> bop ->
        'a1

      module BopNotations :
       sig
       end

      type matchkind = P4cub.Expr.matchkind =
      | MKExact
      | MKTernary
      | MKLpm

      val matchkind_rect : 'a1 -> 'a1 -> 'a1 -> matchkind -> 'a1

      val matchkind_rec : 'a1 -> 'a1 -> 'a1 -> matchkind -> 'a1

      val coq_MatchKindEqDec : matchkind coq_EqDec

      module MatchkindNotations :
       sig
       end

      type 'tags_t e = 'tags_t P4cub.Expr.e =
      | EBool of bool * 'tags_t
      | EBit of positive * coq_Z * 'tags_t
      | EInt of positive * coq_Z * 'tags_t
      | EVar of t * string * 'tags_t
      | ESlice of 'tags_t e * t * positive * positive * 'tags_t
      | ECast of t * 'tags_t e * 'tags_t
      | EUop of uop * t * 'tags_t e * 'tags_t
      | EBop of bop * t * t * 'tags_t e * 'tags_t e * 'tags_t
      | ETuple of 'tags_t e list * 'tags_t
      | EStruct of (string, t * 'tags_t e) P.F.fs * 'tags_t
      | EHeader of (string, t * 'tags_t e) P.F.fs * 'tags_t e * 'tags_t
      | EExprMember of string * t * 'tags_t e * 'tags_t
      | EError of string option * 'tags_t
      | EMatchKind of matchkind * 'tags_t
      | EHeaderStack of (string, t) P.F.fs * 'tags_t e list * positive
         * coq_Z * 'tags_t
      | EHeaderStackAccess of 'tags_t e * coq_Z * 'tags_t

      val e_rect :
        (bool -> 'a1 -> 'a2) -> (positive -> coq_Z -> 'a1 -> 'a2) ->
        (positive -> coq_Z -> 'a1 -> 'a2) -> (t -> string -> 'a1 -> 'a2) ->
        ('a1 e -> 'a2 -> t -> positive -> positive -> 'a1 -> 'a2) -> (t ->
        'a1 e -> 'a2 -> 'a1 -> 'a2) -> (uop -> t -> 'a1 e -> 'a2 -> 'a1 ->
        'a2) -> (bop -> t -> t -> 'a1 e -> 'a2 -> 'a1 e -> 'a2 -> 'a1 -> 'a2)
        -> ('a1 e list -> 'a1 -> 'a2) -> ((string, t * 'a1 e) P.F.fs -> 'a1
        -> 'a2) -> ((string, t * 'a1 e) P.F.fs -> 'a1 e -> 'a2 -> 'a1 -> 'a2)
        -> (string -> t -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (string option ->
        'a1 -> 'a2) -> (matchkind -> 'a1 -> 'a2) -> ((string, t) P.F.fs ->
        'a1 e list -> positive -> coq_Z -> 'a1 -> 'a2) -> ('a1 e -> 'a2 ->
        coq_Z -> 'a1 -> 'a2) -> 'a1 e -> 'a2

      val e_rec :
        (bool -> 'a1 -> 'a2) -> (positive -> coq_Z -> 'a1 -> 'a2) ->
        (positive -> coq_Z -> 'a1 -> 'a2) -> (t -> string -> 'a1 -> 'a2) ->
        ('a1 e -> 'a2 -> t -> positive -> positive -> 'a1 -> 'a2) -> (t ->
        'a1 e -> 'a2 -> 'a1 -> 'a2) -> (uop -> t -> 'a1 e -> 'a2 -> 'a1 ->
        'a2) -> (bop -> t -> t -> 'a1 e -> 'a2 -> 'a1 e -> 'a2 -> 'a1 -> 'a2)
        -> ('a1 e list -> 'a1 -> 'a2) -> ((string, t * 'a1 e) P.F.fs -> 'a1
        -> 'a2) -> ((string, t * 'a1 e) P.F.fs -> 'a1 e -> 'a2 -> 'a1 -> 'a2)
        -> (string -> t -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (string option ->
        'a1 -> 'a2) -> (matchkind -> 'a1 -> 'a2) -> ((string, t) P.F.fs ->
        'a1 e list -> positive -> coq_Z -> 'a1 -> 'a2) -> ('a1 e -> 'a2 ->
        coq_Z -> 'a1 -> 'a2) -> 'a1 e -> 'a2

      type 'tags_t args =
        (string, (t * 'tags_t e, t * 'tags_t e) P.paramarg) P.F.fs

      type 'tags_t arrowE =
        (string, t * 'tags_t e, t * 'tags_t e, t * 'tags_t e) P.arrow

      type 'tags_t constructor_arg = 'tags_t P4cub.Expr.constructor_arg =
      | CAExpr of 'tags_t e
      | CAName of string

      val constructor_arg_rect :
        ('a1 e -> 'a2) -> (string -> 'a2) -> 'a1 constructor_arg -> 'a2

      val constructor_arg_rec :
        ('a1 e -> 'a2) -> (string -> 'a2) -> 'a1 constructor_arg -> 'a2

      type 'tags_t constructor_args = (string, 'tags_t constructor_arg) P.F.fs

      module ExprNotations :
       sig
       end
     end

    type 'tags_t s = 'tags_t P4cub.Stmt.s =
    | SSkip of 'tags_t
    | SVardecl of E.t * string * 'tags_t
    | SAssign of E.t * 'tags_t E.e * 'tags_t E.e * 'tags_t
    | SConditional of E.t * 'tags_t E.e * 'tags_t s * 'tags_t s * 'tags_t
    | SSeq of 'tags_t s * 'tags_t s * 'tags_t
    | SBlock of 'tags_t s
    | SExternMethodCall of string * string * 'tags_t E.arrowE * 'tags_t
    | SFunCall of string * 'tags_t E.arrowE * 'tags_t
    | SActCall of string * 'tags_t E.args * 'tags_t
    | SReturnVoid of 'tags_t
    | SReturnFruit of E.t * 'tags_t E.e * 'tags_t
    | SExit of 'tags_t
    | SInvoke of string * 'tags_t
    | SApply of string * 'tags_t E.args * 'tags_t

    val s_rect :
      ('a1 -> 'a2) -> (E.t -> string -> 'a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1
      E.e -> 'a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1 s -> 'a2 -> 'a1 s -> 'a2
      -> 'a1 -> 'a2) -> ('a1 s -> 'a2 -> 'a1 s -> 'a2 -> 'a1 -> 'a2) -> ('a1
      s -> 'a2 -> 'a2) -> (string -> string -> 'a1 E.arrowE -> 'a1 -> 'a2) ->
      (string -> 'a1 E.arrowE -> 'a1 -> 'a2) -> (string -> 'a1 E.args -> 'a1
      -> 'a2) -> ('a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1 -> 'a2) -> ('a1 ->
      'a2) -> (string -> 'a1 -> 'a2) -> (string -> 'a1 E.args -> 'a1 -> 'a2)
      -> 'a1 s -> 'a2

    val s_rec :
      ('a1 -> 'a2) -> (E.t -> string -> 'a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1
      E.e -> 'a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1 s -> 'a2 -> 'a1 s -> 'a2
      -> 'a1 -> 'a2) -> ('a1 s -> 'a2 -> 'a1 s -> 'a2 -> 'a1 -> 'a2) -> ('a1
      s -> 'a2 -> 'a2) -> (string -> string -> 'a1 E.arrowE -> 'a1 -> 'a2) ->
      (string -> 'a1 E.arrowE -> 'a1 -> 'a2) -> (string -> 'a1 E.args -> 'a1
      -> 'a2) -> ('a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1 -> 'a2) -> ('a1 ->
      'a2) -> (string -> 'a1 -> 'a2) -> (string -> 'a1 E.args -> 'a1 -> 'a2)
      -> 'a1 s -> 'a2

    module StmtNotations :
     sig
     end
   end

  type state = P4cub.Parser.state =
  | STStart
  | STAccept
  | STReject
  | STName of string

  val state_rect : 'a1 -> 'a1 -> 'a1 -> (string -> 'a1) -> state -> 'a1

  val state_rec : 'a1 -> 'a1 -> 'a1 -> (string -> 'a1) -> state -> 'a1

  type pat = P4cub.Parser.pat =
  | PATWild
  | PATMask of pat * pat
  | PATRange of pat * pat
  | PATBit of positive * coq_Z
  | PATInt of positive * coq_Z
  | PATTuple of pat list

  val pat_rect :
    'a1 -> (pat -> 'a1 -> pat -> 'a1 -> 'a1) -> (pat -> 'a1 -> pat -> 'a1 ->
    'a1) -> (positive -> coq_Z -> 'a1) -> (positive -> coq_Z -> 'a1) -> (pat
    list -> 'a1) -> pat -> 'a1

  val pat_rec :
    'a1 -> (pat -> 'a1 -> pat -> 'a1 -> 'a1) -> (pat -> 'a1 -> pat -> 'a1 ->
    'a1) -> (positive -> coq_Z -> 'a1) -> (positive -> coq_Z -> 'a1) -> (pat
    list -> 'a1) -> pat -> 'a1

  type 'tags_t e = 'tags_t P4cub.Parser.e =
  | PGoto of state * 'tags_t
  | PSelect of 'tags_t E.e * 'tags_t e * (pat, 'tags_t e) P.F.fs * 'tags_t

  val e_rect :
    (state -> 'a1 -> 'a2) -> ('a1 E.e -> 'a1 e -> 'a2 -> (pat, 'a1 e) P.F.fs
    -> 'a1 -> 'a2) -> 'a1 e -> 'a2

  val e_rec :
    (state -> 'a1 -> 'a2) -> ('a1 E.e -> 'a1 e -> 'a2 -> (pat, 'a1 e) P.F.fs
    -> 'a1 -> 'a2) -> 'a1 e -> 'a2

  type 'tags_t state_block = 'tags_t P4cub.Parser.state_block =
  | State of 'tags_t S.s * 'tags_t e

  val state_block_rect : ('a1 S.s -> 'a1 e -> 'a2) -> 'a1 state_block -> 'a2

  val state_block_rec : ('a1 S.s -> 'a1 e -> 'a2) -> 'a1 state_block -> 'a2

  module ParserNotations :
   sig
   end
 end

module CT :
 sig
  module E :
   sig
    type t = P4cub.Expr.t =
    | TBool
    | TBit of positive
    | TInt of positive
    | TError
    | TMatchKind
    | TTuple of t list
    | TStruct of (string, t) P.F.fs
    | THeader of (string, t) P.F.fs
    | THeaderStack of (string, t) P.F.fs * positive

    val t_rect :
      'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> 'a1 -> 'a1 -> (t list
      -> 'a1) -> ((string, t) P.F.fs -> 'a1) -> ((string, t) P.F.fs -> 'a1)
      -> ((string, t) P.F.fs -> positive -> 'a1) -> t -> 'a1

    val t_rec :
      'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> 'a1 -> 'a1 -> (t list
      -> 'a1) -> ((string, t) P.F.fs -> 'a1) -> ((string, t) P.F.fs -> 'a1)
      -> ((string, t) P.F.fs -> positive -> 'a1) -> t -> 'a1

    type params = (string, (t, t) P.paramarg) P.F.fs

    type arrowT = (string, t, t, t) P.arrow

    type ct = P4cub.Expr.ct =
    | CTType of t
    | CTControl of (string, ct) P.F.fs * params
    | CTParser of (string, ct) P.F.fs * params
    | CTPackage of (string, ct) P.F.fs
    | CTExtern of (string, ct) P.F.fs * (string, arrowT) P.F.fs

    val ct_rect :
      (t -> 'a1) -> ((string, ct) P.F.fs -> params -> 'a1) -> ((string, ct)
      P.F.fs -> params -> 'a1) -> ((string, ct) P.F.fs -> 'a1) -> ((string,
      ct) P.F.fs -> (string, arrowT) P.F.fs -> 'a1) -> ct -> 'a1

    val ct_rec :
      (t -> 'a1) -> ((string, ct) P.F.fs -> params -> 'a1) -> ((string, ct)
      P.F.fs -> params -> 'a1) -> ((string, ct) P.F.fs -> 'a1) -> ((string,
      ct) P.F.fs -> (string, arrowT) P.F.fs -> 'a1) -> ct -> 'a1

    type constructor_params = (string, ct) P.F.fs

    module TypeNotations :
     sig
     end

    type uop = P4cub.Expr.uop =
    | Not
    | BitNot
    | UMinus
    | IsValid
    | SetValid
    | SetInValid
    | NextIndex
    | Size
    | Push of positive
    | Pop of positive

    val uop_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (positive ->
      'a1) -> (positive -> 'a1) -> uop -> 'a1

    val uop_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (positive ->
      'a1) -> (positive -> 'a1) -> uop -> 'a1

    module UopNotations :
     sig
     end

    type bop = P4cub.Expr.bop =
    | Plus
    | PlusSat
    | Minus
    | MinusSat
    | Times
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

    val bop_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> bop ->
      'a1

    val bop_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> bop ->
      'a1

    module BopNotations :
     sig
     end

    type matchkind = P4cub.Expr.matchkind =
    | MKExact
    | MKTernary
    | MKLpm

    val matchkind_rect : 'a1 -> 'a1 -> 'a1 -> matchkind -> 'a1

    val matchkind_rec : 'a1 -> 'a1 -> 'a1 -> matchkind -> 'a1

    val coq_MatchKindEqDec : matchkind coq_EqDec

    module MatchkindNotations :
     sig
     end

    type 'tags_t e = 'tags_t P4cub.Expr.e =
    | EBool of bool * 'tags_t
    | EBit of positive * coq_Z * 'tags_t
    | EInt of positive * coq_Z * 'tags_t
    | EVar of t * string * 'tags_t
    | ESlice of 'tags_t e * t * positive * positive * 'tags_t
    | ECast of t * 'tags_t e * 'tags_t
    | EUop of uop * t * 'tags_t e * 'tags_t
    | EBop of bop * t * t * 'tags_t e * 'tags_t e * 'tags_t
    | ETuple of 'tags_t e list * 'tags_t
    | EStruct of (string, t * 'tags_t e) P.F.fs * 'tags_t
    | EHeader of (string, t * 'tags_t e) P.F.fs * 'tags_t e * 'tags_t
    | EExprMember of string * t * 'tags_t e * 'tags_t
    | EError of string option * 'tags_t
    | EMatchKind of matchkind * 'tags_t
    | EHeaderStack of (string, t) P.F.fs * 'tags_t e list * positive * 
       coq_Z * 'tags_t
    | EHeaderStackAccess of 'tags_t e * coq_Z * 'tags_t

    val e_rect :
      (bool -> 'a1 -> 'a2) -> (positive -> coq_Z -> 'a1 -> 'a2) -> (positive
      -> coq_Z -> 'a1 -> 'a2) -> (t -> string -> 'a1 -> 'a2) -> ('a1 e -> 'a2
      -> t -> positive -> positive -> 'a1 -> 'a2) -> (t -> 'a1 e -> 'a2 ->
      'a1 -> 'a2) -> (uop -> t -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (bop -> t ->
      t -> 'a1 e -> 'a2 -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> ('a1 e list -> 'a1
      -> 'a2) -> ((string, t * 'a1 e) P.F.fs -> 'a1 -> 'a2) -> ((string,
      t * 'a1 e) P.F.fs -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (string -> t -> 'a1
      e -> 'a2 -> 'a1 -> 'a2) -> (string option -> 'a1 -> 'a2) -> (matchkind
      -> 'a1 -> 'a2) -> ((string, t) P.F.fs -> 'a1 e list -> positive ->
      coq_Z -> 'a1 -> 'a2) -> ('a1 e -> 'a2 -> coq_Z -> 'a1 -> 'a2) -> 'a1 e
      -> 'a2

    val e_rec :
      (bool -> 'a1 -> 'a2) -> (positive -> coq_Z -> 'a1 -> 'a2) -> (positive
      -> coq_Z -> 'a1 -> 'a2) -> (t -> string -> 'a1 -> 'a2) -> ('a1 e -> 'a2
      -> t -> positive -> positive -> 'a1 -> 'a2) -> (t -> 'a1 e -> 'a2 ->
      'a1 -> 'a2) -> (uop -> t -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (bop -> t ->
      t -> 'a1 e -> 'a2 -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> ('a1 e list -> 'a1
      -> 'a2) -> ((string, t * 'a1 e) P.F.fs -> 'a1 -> 'a2) -> ((string,
      t * 'a1 e) P.F.fs -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (string -> t -> 'a1
      e -> 'a2 -> 'a1 -> 'a2) -> (string option -> 'a1 -> 'a2) -> (matchkind
      -> 'a1 -> 'a2) -> ((string, t) P.F.fs -> 'a1 e list -> positive ->
      coq_Z -> 'a1 -> 'a2) -> ('a1 e -> 'a2 -> coq_Z -> 'a1 -> 'a2) -> 'a1 e
      -> 'a2

    type 'tags_t args =
      (string, (t * 'tags_t e, t * 'tags_t e) P.paramarg) P.F.fs

    type 'tags_t arrowE =
      (string, t * 'tags_t e, t * 'tags_t e, t * 'tags_t e) P.arrow

    type 'tags_t constructor_arg = 'tags_t P4cub.Expr.constructor_arg =
    | CAExpr of 'tags_t e
    | CAName of string

    val constructor_arg_rect :
      ('a1 e -> 'a2) -> (string -> 'a2) -> 'a1 constructor_arg -> 'a2

    val constructor_arg_rec :
      ('a1 e -> 'a2) -> (string -> 'a2) -> 'a1 constructor_arg -> 'a2

    type 'tags_t constructor_args = (string, 'tags_t constructor_arg) P.F.fs

    module ExprNotations :
     sig
     end
   end

  module S :
   sig
    module E :
     sig
      type t = P4cub.Expr.t =
      | TBool
      | TBit of positive
      | TInt of positive
      | TError
      | TMatchKind
      | TTuple of t list
      | TStruct of (string, t) P.F.fs
      | THeader of (string, t) P.F.fs
      | THeaderStack of (string, t) P.F.fs * positive

      val t_rect :
        'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> 'a1 -> 'a1 -> (t
        list -> 'a1) -> ((string, t) P.F.fs -> 'a1) -> ((string, t) P.F.fs ->
        'a1) -> ((string, t) P.F.fs -> positive -> 'a1) -> t -> 'a1

      val t_rec :
        'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> 'a1 -> 'a1 -> (t
        list -> 'a1) -> ((string, t) P.F.fs -> 'a1) -> ((string, t) P.F.fs ->
        'a1) -> ((string, t) P.F.fs -> positive -> 'a1) -> t -> 'a1

      type params = (string, (t, t) P.paramarg) P.F.fs

      type arrowT = (string, t, t, t) P.arrow

      type ct = P4cub.Expr.ct =
      | CTType of t
      | CTControl of (string, ct) P.F.fs * params
      | CTParser of (string, ct) P.F.fs * params
      | CTPackage of (string, ct) P.F.fs
      | CTExtern of (string, ct) P.F.fs * (string, arrowT) P.F.fs

      val ct_rect :
        (t -> 'a1) -> ((string, ct) P.F.fs -> params -> 'a1) -> ((string, ct)
        P.F.fs -> params -> 'a1) -> ((string, ct) P.F.fs -> 'a1) -> ((string,
        ct) P.F.fs -> (string, arrowT) P.F.fs -> 'a1) -> ct -> 'a1

      val ct_rec :
        (t -> 'a1) -> ((string, ct) P.F.fs -> params -> 'a1) -> ((string, ct)
        P.F.fs -> params -> 'a1) -> ((string, ct) P.F.fs -> 'a1) -> ((string,
        ct) P.F.fs -> (string, arrowT) P.F.fs -> 'a1) -> ct -> 'a1

      type constructor_params = (string, ct) P.F.fs

      module TypeNotations :
       sig
       end

      type uop = P4cub.Expr.uop =
      | Not
      | BitNot
      | UMinus
      | IsValid
      | SetValid
      | SetInValid
      | NextIndex
      | Size
      | Push of positive
      | Pop of positive

      val uop_rect :
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (positive ->
        'a1) -> (positive -> 'a1) -> uop -> 'a1

      val uop_rec :
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (positive ->
        'a1) -> (positive -> 'a1) -> uop -> 'a1

      module UopNotations :
       sig
       end

      type bop = P4cub.Expr.bop =
      | Plus
      | PlusSat
      | Minus
      | MinusSat
      | Times
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

      val bop_rect :
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> bop ->
        'a1

      val bop_rec :
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> bop ->
        'a1

      module BopNotations :
       sig
       end

      type matchkind = P4cub.Expr.matchkind =
      | MKExact
      | MKTernary
      | MKLpm

      val matchkind_rect : 'a1 -> 'a1 -> 'a1 -> matchkind -> 'a1

      val matchkind_rec : 'a1 -> 'a1 -> 'a1 -> matchkind -> 'a1

      val coq_MatchKindEqDec : matchkind coq_EqDec

      module MatchkindNotations :
       sig
       end

      type 'tags_t e = 'tags_t P4cub.Expr.e =
      | EBool of bool * 'tags_t
      | EBit of positive * coq_Z * 'tags_t
      | EInt of positive * coq_Z * 'tags_t
      | EVar of t * string * 'tags_t
      | ESlice of 'tags_t e * t * positive * positive * 'tags_t
      | ECast of t * 'tags_t e * 'tags_t
      | EUop of uop * t * 'tags_t e * 'tags_t
      | EBop of bop * t * t * 'tags_t e * 'tags_t e * 'tags_t
      | ETuple of 'tags_t e list * 'tags_t
      | EStruct of (string, t * 'tags_t e) P.F.fs * 'tags_t
      | EHeader of (string, t * 'tags_t e) P.F.fs * 'tags_t e * 'tags_t
      | EExprMember of string * t * 'tags_t e * 'tags_t
      | EError of string option * 'tags_t
      | EMatchKind of matchkind * 'tags_t
      | EHeaderStack of (string, t) P.F.fs * 'tags_t e list * positive
         * coq_Z * 'tags_t
      | EHeaderStackAccess of 'tags_t e * coq_Z * 'tags_t

      val e_rect :
        (bool -> 'a1 -> 'a2) -> (positive -> coq_Z -> 'a1 -> 'a2) ->
        (positive -> coq_Z -> 'a1 -> 'a2) -> (t -> string -> 'a1 -> 'a2) ->
        ('a1 e -> 'a2 -> t -> positive -> positive -> 'a1 -> 'a2) -> (t ->
        'a1 e -> 'a2 -> 'a1 -> 'a2) -> (uop -> t -> 'a1 e -> 'a2 -> 'a1 ->
        'a2) -> (bop -> t -> t -> 'a1 e -> 'a2 -> 'a1 e -> 'a2 -> 'a1 -> 'a2)
        -> ('a1 e list -> 'a1 -> 'a2) -> ((string, t * 'a1 e) P.F.fs -> 'a1
        -> 'a2) -> ((string, t * 'a1 e) P.F.fs -> 'a1 e -> 'a2 -> 'a1 -> 'a2)
        -> (string -> t -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (string option ->
        'a1 -> 'a2) -> (matchkind -> 'a1 -> 'a2) -> ((string, t) P.F.fs ->
        'a1 e list -> positive -> coq_Z -> 'a1 -> 'a2) -> ('a1 e -> 'a2 ->
        coq_Z -> 'a1 -> 'a2) -> 'a1 e -> 'a2

      val e_rec :
        (bool -> 'a1 -> 'a2) -> (positive -> coq_Z -> 'a1 -> 'a2) ->
        (positive -> coq_Z -> 'a1 -> 'a2) -> (t -> string -> 'a1 -> 'a2) ->
        ('a1 e -> 'a2 -> t -> positive -> positive -> 'a1 -> 'a2) -> (t ->
        'a1 e -> 'a2 -> 'a1 -> 'a2) -> (uop -> t -> 'a1 e -> 'a2 -> 'a1 ->
        'a2) -> (bop -> t -> t -> 'a1 e -> 'a2 -> 'a1 e -> 'a2 -> 'a1 -> 'a2)
        -> ('a1 e list -> 'a1 -> 'a2) -> ((string, t * 'a1 e) P.F.fs -> 'a1
        -> 'a2) -> ((string, t * 'a1 e) P.F.fs -> 'a1 e -> 'a2 -> 'a1 -> 'a2)
        -> (string -> t -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (string option ->
        'a1 -> 'a2) -> (matchkind -> 'a1 -> 'a2) -> ((string, t) P.F.fs ->
        'a1 e list -> positive -> coq_Z -> 'a1 -> 'a2) -> ('a1 e -> 'a2 ->
        coq_Z -> 'a1 -> 'a2) -> 'a1 e -> 'a2

      type 'tags_t args =
        (string, (t * 'tags_t e, t * 'tags_t e) P.paramarg) P.F.fs

      type 'tags_t arrowE =
        (string, t * 'tags_t e, t * 'tags_t e, t * 'tags_t e) P.arrow

      type 'tags_t constructor_arg = 'tags_t P4cub.Expr.constructor_arg =
      | CAExpr of 'tags_t e
      | CAName of string

      val constructor_arg_rect :
        ('a1 e -> 'a2) -> (string -> 'a2) -> 'a1 constructor_arg -> 'a2

      val constructor_arg_rec :
        ('a1 e -> 'a2) -> (string -> 'a2) -> 'a1 constructor_arg -> 'a2

      type 'tags_t constructor_args = (string, 'tags_t constructor_arg) P.F.fs

      module ExprNotations :
       sig
       end
     end

    type 'tags_t s = 'tags_t P4cub.Stmt.s =
    | SSkip of 'tags_t
    | SVardecl of E.t * string * 'tags_t
    | SAssign of E.t * 'tags_t E.e * 'tags_t E.e * 'tags_t
    | SConditional of E.t * 'tags_t E.e * 'tags_t s * 'tags_t s * 'tags_t
    | SSeq of 'tags_t s * 'tags_t s * 'tags_t
    | SBlock of 'tags_t s
    | SExternMethodCall of string * string * 'tags_t E.arrowE * 'tags_t
    | SFunCall of string * 'tags_t E.arrowE * 'tags_t
    | SActCall of string * 'tags_t E.args * 'tags_t
    | SReturnVoid of 'tags_t
    | SReturnFruit of E.t * 'tags_t E.e * 'tags_t
    | SExit of 'tags_t
    | SInvoke of string * 'tags_t
    | SApply of string * 'tags_t E.args * 'tags_t

    val s_rect :
      ('a1 -> 'a2) -> (E.t -> string -> 'a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1
      E.e -> 'a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1 s -> 'a2 -> 'a1 s -> 'a2
      -> 'a1 -> 'a2) -> ('a1 s -> 'a2 -> 'a1 s -> 'a2 -> 'a1 -> 'a2) -> ('a1
      s -> 'a2 -> 'a2) -> (string -> string -> 'a1 E.arrowE -> 'a1 -> 'a2) ->
      (string -> 'a1 E.arrowE -> 'a1 -> 'a2) -> (string -> 'a1 E.args -> 'a1
      -> 'a2) -> ('a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1 -> 'a2) -> ('a1 ->
      'a2) -> (string -> 'a1 -> 'a2) -> (string -> 'a1 E.args -> 'a1 -> 'a2)
      -> 'a1 s -> 'a2

    val s_rec :
      ('a1 -> 'a2) -> (E.t -> string -> 'a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1
      E.e -> 'a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1 s -> 'a2 -> 'a1 s -> 'a2
      -> 'a1 -> 'a2) -> ('a1 s -> 'a2 -> 'a1 s -> 'a2 -> 'a1 -> 'a2) -> ('a1
      s -> 'a2 -> 'a2) -> (string -> string -> 'a1 E.arrowE -> 'a1 -> 'a2) ->
      (string -> 'a1 E.arrowE -> 'a1 -> 'a2) -> (string -> 'a1 E.args -> 'a1
      -> 'a2) -> ('a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1 -> 'a2) -> ('a1 ->
      'a2) -> (string -> 'a1 -> 'a2) -> (string -> 'a1 E.args -> 'a1 -> 'a2)
      -> 'a1 s -> 'a2

    module StmtNotations :
     sig
     end
   end

  module ControlDecl :
   sig
    type 'tags_t table = 'tags_t P4cub.Control.ControlDecl.table =
    | Table of ((E.t * 'tags_t E.e) * E.matchkind) list * string list

    val table_rect :
      (((E.t * 'a1 E.e) * E.matchkind) list -> string list -> 'a2) -> 'a1
      table -> 'a2

    val table_rec :
      (((E.t * 'a1 E.e) * E.matchkind) list -> string list -> 'a2) -> 'a1
      table -> 'a2

    type 'tags_t d = 'tags_t P4cub.Control.ControlDecl.d =
    | CDAction of string * E.params * 'tags_t S.s * 'tags_t
    | CDTable of string * 'tags_t table * 'tags_t
    | CDSeq of 'tags_t d * 'tags_t d * 'tags_t

    val d_rect :
      (string -> E.params -> 'a1 S.s -> 'a1 -> 'a2) -> (string -> 'a1 table
      -> 'a1 -> 'a2) -> ('a1 d -> 'a2 -> 'a1 d -> 'a2 -> 'a1 -> 'a2) -> 'a1 d
      -> 'a2

    val d_rec :
      (string -> E.params -> 'a1 S.s -> 'a1 -> 'a2) -> (string -> 'a1 table
      -> 'a1 -> 'a2) -> ('a1 d -> 'a2 -> 'a1 d -> 'a2 -> 'a1 -> 'a2) -> 'a1 d
      -> 'a2

    module ControlDeclNotations :
     sig
     end
   end
 end

module TD :
 sig
  module E :
   sig
    type t = P4cub.Expr.t =
    | TBool
    | TBit of positive
    | TInt of positive
    | TError
    | TMatchKind
    | TTuple of t list
    | TStruct of (string, t) P.F.fs
    | THeader of (string, t) P.F.fs
    | THeaderStack of (string, t) P.F.fs * positive

    val t_rect :
      'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> 'a1 -> 'a1 -> (t list
      -> 'a1) -> ((string, t) P.F.fs -> 'a1) -> ((string, t) P.F.fs -> 'a1)
      -> ((string, t) P.F.fs -> positive -> 'a1) -> t -> 'a1

    val t_rec :
      'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> 'a1 -> 'a1 -> (t list
      -> 'a1) -> ((string, t) P.F.fs -> 'a1) -> ((string, t) P.F.fs -> 'a1)
      -> ((string, t) P.F.fs -> positive -> 'a1) -> t -> 'a1

    type params = (string, (t, t) P.paramarg) P.F.fs

    type arrowT = (string, t, t, t) P.arrow

    type ct = P4cub.Expr.ct =
    | CTType of t
    | CTControl of (string, ct) P.F.fs * params
    | CTParser of (string, ct) P.F.fs * params
    | CTPackage of (string, ct) P.F.fs
    | CTExtern of (string, ct) P.F.fs * (string, arrowT) P.F.fs

    val ct_rect :
      (t -> 'a1) -> ((string, ct) P.F.fs -> params -> 'a1) -> ((string, ct)
      P.F.fs -> params -> 'a1) -> ((string, ct) P.F.fs -> 'a1) -> ((string,
      ct) P.F.fs -> (string, arrowT) P.F.fs -> 'a1) -> ct -> 'a1

    val ct_rec :
      (t -> 'a1) -> ((string, ct) P.F.fs -> params -> 'a1) -> ((string, ct)
      P.F.fs -> params -> 'a1) -> ((string, ct) P.F.fs -> 'a1) -> ((string,
      ct) P.F.fs -> (string, arrowT) P.F.fs -> 'a1) -> ct -> 'a1

    type constructor_params = (string, ct) P.F.fs

    module TypeNotations :
     sig
     end

    type uop = P4cub.Expr.uop =
    | Not
    | BitNot
    | UMinus
    | IsValid
    | SetValid
    | SetInValid
    | NextIndex
    | Size
    | Push of positive
    | Pop of positive

    val uop_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (positive ->
      'a1) -> (positive -> 'a1) -> uop -> 'a1

    val uop_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (positive ->
      'a1) -> (positive -> 'a1) -> uop -> 'a1

    module UopNotations :
     sig
     end

    type bop = P4cub.Expr.bop =
    | Plus
    | PlusSat
    | Minus
    | MinusSat
    | Times
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

    val bop_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> bop ->
      'a1

    val bop_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> bop ->
      'a1

    module BopNotations :
     sig
     end

    type matchkind = P4cub.Expr.matchkind =
    | MKExact
    | MKTernary
    | MKLpm

    val matchkind_rect : 'a1 -> 'a1 -> 'a1 -> matchkind -> 'a1

    val matchkind_rec : 'a1 -> 'a1 -> 'a1 -> matchkind -> 'a1

    val coq_MatchKindEqDec : matchkind coq_EqDec

    module MatchkindNotations :
     sig
     end

    type 'tags_t e = 'tags_t P4cub.Expr.e =
    | EBool of bool * 'tags_t
    | EBit of positive * coq_Z * 'tags_t
    | EInt of positive * coq_Z * 'tags_t
    | EVar of t * string * 'tags_t
    | ESlice of 'tags_t e * t * positive * positive * 'tags_t
    | ECast of t * 'tags_t e * 'tags_t
    | EUop of uop * t * 'tags_t e * 'tags_t
    | EBop of bop * t * t * 'tags_t e * 'tags_t e * 'tags_t
    | ETuple of 'tags_t e list * 'tags_t
    | EStruct of (string, t * 'tags_t e) P.F.fs * 'tags_t
    | EHeader of (string, t * 'tags_t e) P.F.fs * 'tags_t e * 'tags_t
    | EExprMember of string * t * 'tags_t e * 'tags_t
    | EError of string option * 'tags_t
    | EMatchKind of matchkind * 'tags_t
    | EHeaderStack of (string, t) P.F.fs * 'tags_t e list * positive * 
       coq_Z * 'tags_t
    | EHeaderStackAccess of 'tags_t e * coq_Z * 'tags_t

    val e_rect :
      (bool -> 'a1 -> 'a2) -> (positive -> coq_Z -> 'a1 -> 'a2) -> (positive
      -> coq_Z -> 'a1 -> 'a2) -> (t -> string -> 'a1 -> 'a2) -> ('a1 e -> 'a2
      -> t -> positive -> positive -> 'a1 -> 'a2) -> (t -> 'a1 e -> 'a2 ->
      'a1 -> 'a2) -> (uop -> t -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (bop -> t ->
      t -> 'a1 e -> 'a2 -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> ('a1 e list -> 'a1
      -> 'a2) -> ((string, t * 'a1 e) P.F.fs -> 'a1 -> 'a2) -> ((string,
      t * 'a1 e) P.F.fs -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (string -> t -> 'a1
      e -> 'a2 -> 'a1 -> 'a2) -> (string option -> 'a1 -> 'a2) -> (matchkind
      -> 'a1 -> 'a2) -> ((string, t) P.F.fs -> 'a1 e list -> positive ->
      coq_Z -> 'a1 -> 'a2) -> ('a1 e -> 'a2 -> coq_Z -> 'a1 -> 'a2) -> 'a1 e
      -> 'a2

    val e_rec :
      (bool -> 'a1 -> 'a2) -> (positive -> coq_Z -> 'a1 -> 'a2) -> (positive
      -> coq_Z -> 'a1 -> 'a2) -> (t -> string -> 'a1 -> 'a2) -> ('a1 e -> 'a2
      -> t -> positive -> positive -> 'a1 -> 'a2) -> (t -> 'a1 e -> 'a2 ->
      'a1 -> 'a2) -> (uop -> t -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (bop -> t ->
      t -> 'a1 e -> 'a2 -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> ('a1 e list -> 'a1
      -> 'a2) -> ((string, t * 'a1 e) P.F.fs -> 'a1 -> 'a2) -> ((string,
      t * 'a1 e) P.F.fs -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (string -> t -> 'a1
      e -> 'a2 -> 'a1 -> 'a2) -> (string option -> 'a1 -> 'a2) -> (matchkind
      -> 'a1 -> 'a2) -> ((string, t) P.F.fs -> 'a1 e list -> positive ->
      coq_Z -> 'a1 -> 'a2) -> ('a1 e -> 'a2 -> coq_Z -> 'a1 -> 'a2) -> 'a1 e
      -> 'a2

    type 'tags_t args =
      (string, (t * 'tags_t e, t * 'tags_t e) P.paramarg) P.F.fs

    type 'tags_t arrowE =
      (string, t * 'tags_t e, t * 'tags_t e, t * 'tags_t e) P.arrow

    type 'tags_t constructor_arg = 'tags_t P4cub.Expr.constructor_arg =
    | CAExpr of 'tags_t e
    | CAName of string

    val constructor_arg_rect :
      ('a1 e -> 'a2) -> (string -> 'a2) -> 'a1 constructor_arg -> 'a2

    val constructor_arg_rec :
      ('a1 e -> 'a2) -> (string -> 'a2) -> 'a1 constructor_arg -> 'a2

    type 'tags_t constructor_args = (string, 'tags_t constructor_arg) P.F.fs

    module ExprNotations :
     sig
     end
   end

  module S :
   sig
    module E :
     sig
      type t = P4cub.Expr.t =
      | TBool
      | TBit of positive
      | TInt of positive
      | TError
      | TMatchKind
      | TTuple of t list
      | TStruct of (string, t) P.F.fs
      | THeader of (string, t) P.F.fs
      | THeaderStack of (string, t) P.F.fs * positive

      val t_rect :
        'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> 'a1 -> 'a1 -> (t
        list -> 'a1) -> ((string, t) P.F.fs -> 'a1) -> ((string, t) P.F.fs ->
        'a1) -> ((string, t) P.F.fs -> positive -> 'a1) -> t -> 'a1

      val t_rec :
        'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> 'a1 -> 'a1 -> (t
        list -> 'a1) -> ((string, t) P.F.fs -> 'a1) -> ((string, t) P.F.fs ->
        'a1) -> ((string, t) P.F.fs -> positive -> 'a1) -> t -> 'a1

      type params = (string, (t, t) P.paramarg) P.F.fs

      type arrowT = (string, t, t, t) P.arrow

      type ct = P4cub.Expr.ct =
      | CTType of t
      | CTControl of (string, ct) P.F.fs * params
      | CTParser of (string, ct) P.F.fs * params
      | CTPackage of (string, ct) P.F.fs
      | CTExtern of (string, ct) P.F.fs * (string, arrowT) P.F.fs

      val ct_rect :
        (t -> 'a1) -> ((string, ct) P.F.fs -> params -> 'a1) -> ((string, ct)
        P.F.fs -> params -> 'a1) -> ((string, ct) P.F.fs -> 'a1) -> ((string,
        ct) P.F.fs -> (string, arrowT) P.F.fs -> 'a1) -> ct -> 'a1

      val ct_rec :
        (t -> 'a1) -> ((string, ct) P.F.fs -> params -> 'a1) -> ((string, ct)
        P.F.fs -> params -> 'a1) -> ((string, ct) P.F.fs -> 'a1) -> ((string,
        ct) P.F.fs -> (string, arrowT) P.F.fs -> 'a1) -> ct -> 'a1

      type constructor_params = (string, ct) P.F.fs

      module TypeNotations :
       sig
       end

      type uop = P4cub.Expr.uop =
      | Not
      | BitNot
      | UMinus
      | IsValid
      | SetValid
      | SetInValid
      | NextIndex
      | Size
      | Push of positive
      | Pop of positive

      val uop_rect :
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (positive ->
        'a1) -> (positive -> 'a1) -> uop -> 'a1

      val uop_rec :
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (positive ->
        'a1) -> (positive -> 'a1) -> uop -> 'a1

      module UopNotations :
       sig
       end

      type bop = P4cub.Expr.bop =
      | Plus
      | PlusSat
      | Minus
      | MinusSat
      | Times
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

      val bop_rect :
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> bop ->
        'a1

      val bop_rec :
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> bop ->
        'a1

      module BopNotations :
       sig
       end

      type matchkind = P4cub.Expr.matchkind =
      | MKExact
      | MKTernary
      | MKLpm

      val matchkind_rect : 'a1 -> 'a1 -> 'a1 -> matchkind -> 'a1

      val matchkind_rec : 'a1 -> 'a1 -> 'a1 -> matchkind -> 'a1

      val coq_MatchKindEqDec : matchkind coq_EqDec

      module MatchkindNotations :
       sig
       end

      type 'tags_t e = 'tags_t P4cub.Expr.e =
      | EBool of bool * 'tags_t
      | EBit of positive * coq_Z * 'tags_t
      | EInt of positive * coq_Z * 'tags_t
      | EVar of t * string * 'tags_t
      | ESlice of 'tags_t e * t * positive * positive * 'tags_t
      | ECast of t * 'tags_t e * 'tags_t
      | EUop of uop * t * 'tags_t e * 'tags_t
      | EBop of bop * t * t * 'tags_t e * 'tags_t e * 'tags_t
      | ETuple of 'tags_t e list * 'tags_t
      | EStruct of (string, t * 'tags_t e) P.F.fs * 'tags_t
      | EHeader of (string, t * 'tags_t e) P.F.fs * 'tags_t e * 'tags_t
      | EExprMember of string * t * 'tags_t e * 'tags_t
      | EError of string option * 'tags_t
      | EMatchKind of matchkind * 'tags_t
      | EHeaderStack of (string, t) P.F.fs * 'tags_t e list * positive
         * coq_Z * 'tags_t
      | EHeaderStackAccess of 'tags_t e * coq_Z * 'tags_t

      val e_rect :
        (bool -> 'a1 -> 'a2) -> (positive -> coq_Z -> 'a1 -> 'a2) ->
        (positive -> coq_Z -> 'a1 -> 'a2) -> (t -> string -> 'a1 -> 'a2) ->
        ('a1 e -> 'a2 -> t -> positive -> positive -> 'a1 -> 'a2) -> (t ->
        'a1 e -> 'a2 -> 'a1 -> 'a2) -> (uop -> t -> 'a1 e -> 'a2 -> 'a1 ->
        'a2) -> (bop -> t -> t -> 'a1 e -> 'a2 -> 'a1 e -> 'a2 -> 'a1 -> 'a2)
        -> ('a1 e list -> 'a1 -> 'a2) -> ((string, t * 'a1 e) P.F.fs -> 'a1
        -> 'a2) -> ((string, t * 'a1 e) P.F.fs -> 'a1 e -> 'a2 -> 'a1 -> 'a2)
        -> (string -> t -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (string option ->
        'a1 -> 'a2) -> (matchkind -> 'a1 -> 'a2) -> ((string, t) P.F.fs ->
        'a1 e list -> positive -> coq_Z -> 'a1 -> 'a2) -> ('a1 e -> 'a2 ->
        coq_Z -> 'a1 -> 'a2) -> 'a1 e -> 'a2

      val e_rec :
        (bool -> 'a1 -> 'a2) -> (positive -> coq_Z -> 'a1 -> 'a2) ->
        (positive -> coq_Z -> 'a1 -> 'a2) -> (t -> string -> 'a1 -> 'a2) ->
        ('a1 e -> 'a2 -> t -> positive -> positive -> 'a1 -> 'a2) -> (t ->
        'a1 e -> 'a2 -> 'a1 -> 'a2) -> (uop -> t -> 'a1 e -> 'a2 -> 'a1 ->
        'a2) -> (bop -> t -> t -> 'a1 e -> 'a2 -> 'a1 e -> 'a2 -> 'a1 -> 'a2)
        -> ('a1 e list -> 'a1 -> 'a2) -> ((string, t * 'a1 e) P.F.fs -> 'a1
        -> 'a2) -> ((string, t * 'a1 e) P.F.fs -> 'a1 e -> 'a2 -> 'a1 -> 'a2)
        -> (string -> t -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (string option ->
        'a1 -> 'a2) -> (matchkind -> 'a1 -> 'a2) -> ((string, t) P.F.fs ->
        'a1 e list -> positive -> coq_Z -> 'a1 -> 'a2) -> ('a1 e -> 'a2 ->
        coq_Z -> 'a1 -> 'a2) -> 'a1 e -> 'a2

      type 'tags_t args =
        (string, (t * 'tags_t e, t * 'tags_t e) P.paramarg) P.F.fs

      type 'tags_t arrowE =
        (string, t * 'tags_t e, t * 'tags_t e, t * 'tags_t e) P.arrow

      type 'tags_t constructor_arg = 'tags_t P4cub.Expr.constructor_arg =
      | CAExpr of 'tags_t e
      | CAName of string

      val constructor_arg_rect :
        ('a1 e -> 'a2) -> (string -> 'a2) -> 'a1 constructor_arg -> 'a2

      val constructor_arg_rec :
        ('a1 e -> 'a2) -> (string -> 'a2) -> 'a1 constructor_arg -> 'a2

      type 'tags_t constructor_args = (string, 'tags_t constructor_arg) P.F.fs

      module ExprNotations :
       sig
       end
     end

    type 'tags_t s = 'tags_t P4cub.Stmt.s =
    | SSkip of 'tags_t
    | SVardecl of E.t * string * 'tags_t
    | SAssign of E.t * 'tags_t E.e * 'tags_t E.e * 'tags_t
    | SConditional of E.t * 'tags_t E.e * 'tags_t s * 'tags_t s * 'tags_t
    | SSeq of 'tags_t s * 'tags_t s * 'tags_t
    | SBlock of 'tags_t s
    | SExternMethodCall of string * string * 'tags_t E.arrowE * 'tags_t
    | SFunCall of string * 'tags_t E.arrowE * 'tags_t
    | SActCall of string * 'tags_t E.args * 'tags_t
    | SReturnVoid of 'tags_t
    | SReturnFruit of E.t * 'tags_t E.e * 'tags_t
    | SExit of 'tags_t
    | SInvoke of string * 'tags_t
    | SApply of string * 'tags_t E.args * 'tags_t

    val s_rect :
      ('a1 -> 'a2) -> (E.t -> string -> 'a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1
      E.e -> 'a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1 s -> 'a2 -> 'a1 s -> 'a2
      -> 'a1 -> 'a2) -> ('a1 s -> 'a2 -> 'a1 s -> 'a2 -> 'a1 -> 'a2) -> ('a1
      s -> 'a2 -> 'a2) -> (string -> string -> 'a1 E.arrowE -> 'a1 -> 'a2) ->
      (string -> 'a1 E.arrowE -> 'a1 -> 'a2) -> (string -> 'a1 E.args -> 'a1
      -> 'a2) -> ('a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1 -> 'a2) -> ('a1 ->
      'a2) -> (string -> 'a1 -> 'a2) -> (string -> 'a1 E.args -> 'a1 -> 'a2)
      -> 'a1 s -> 'a2

    val s_rec :
      ('a1 -> 'a2) -> (E.t -> string -> 'a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1
      E.e -> 'a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1 s -> 'a2 -> 'a1 s -> 'a2
      -> 'a1 -> 'a2) -> ('a1 s -> 'a2 -> 'a1 s -> 'a2 -> 'a1 -> 'a2) -> ('a1
      s -> 'a2 -> 'a2) -> (string -> string -> 'a1 E.arrowE -> 'a1 -> 'a2) ->
      (string -> 'a1 E.arrowE -> 'a1 -> 'a2) -> (string -> 'a1 E.args -> 'a1
      -> 'a2) -> ('a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1 -> 'a2) -> ('a1 ->
      'a2) -> (string -> 'a1 -> 'a2) -> (string -> 'a1 E.args -> 'a1 -> 'a2)
      -> 'a1 s -> 'a2

    module StmtNotations :
     sig
     end
   end

  module C :
   sig
    type 'tags_t table = 'tags_t P4cub.Control.ControlDecl.table =
    | Table of ((P.Control.E.t * 'tags_t
               P.Control.E.e) * P.Control.E.matchkind) list * string list

    val table_rect :
      (((P.Control.E.t * 'a1 P.Control.E.e) * P.Control.E.matchkind) list ->
      string list -> 'a2) -> 'a1 table -> 'a2

    val table_rec :
      (((P.Control.E.t * 'a1 P.Control.E.e) * P.Control.E.matchkind) list ->
      string list -> 'a2) -> 'a1 table -> 'a2

    type 'tags_t d = 'tags_t P4cub.Control.ControlDecl.d =
    | CDAction of string * P.Control.E.params * 'tags_t P.Control.S.s
       * 'tags_t
    | CDTable of string * 'tags_t table * 'tags_t
    | CDSeq of 'tags_t d * 'tags_t d * 'tags_t

    val d_rect :
      (string -> P.Control.E.params -> 'a1 P.Control.S.s -> 'a1 -> 'a2) ->
      (string -> 'a1 table -> 'a1 -> 'a2) -> ('a1 d -> 'a2 -> 'a1 d -> 'a2 ->
      'a1 -> 'a2) -> 'a1 d -> 'a2

    val d_rec :
      (string -> P.Control.E.params -> 'a1 P.Control.S.s -> 'a1 -> 'a2) ->
      (string -> 'a1 table -> 'a1 -> 'a2) -> ('a1 d -> 'a2 -> 'a1 d -> 'a2 ->
      'a1 -> 'a2) -> 'a1 d -> 'a2

    module ControlDeclNotations :
     sig
     end
   end

  module P :
   sig
    module E :
     sig
      type t = P4cub.Expr.t =
      | TBool
      | TBit of positive
      | TInt of positive
      | TError
      | TMatchKind
      | TTuple of t list
      | TStruct of (string, t) P.F.fs
      | THeader of (string, t) P.F.fs
      | THeaderStack of (string, t) P.F.fs * positive

      val t_rect :
        'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> 'a1 -> 'a1 -> (t
        list -> 'a1) -> ((string, t) P.F.fs -> 'a1) -> ((string, t) P.F.fs ->
        'a1) -> ((string, t) P.F.fs -> positive -> 'a1) -> t -> 'a1

      val t_rec :
        'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> 'a1 -> 'a1 -> (t
        list -> 'a1) -> ((string, t) P.F.fs -> 'a1) -> ((string, t) P.F.fs ->
        'a1) -> ((string, t) P.F.fs -> positive -> 'a1) -> t -> 'a1

      type params = (string, (t, t) P.paramarg) P.F.fs

      type arrowT = (string, t, t, t) P.arrow

      type ct = P4cub.Expr.ct =
      | CTType of t
      | CTControl of (string, ct) P.F.fs * params
      | CTParser of (string, ct) P.F.fs * params
      | CTPackage of (string, ct) P.F.fs
      | CTExtern of (string, ct) P.F.fs * (string, arrowT) P.F.fs

      val ct_rect :
        (t -> 'a1) -> ((string, ct) P.F.fs -> params -> 'a1) -> ((string, ct)
        P.F.fs -> params -> 'a1) -> ((string, ct) P.F.fs -> 'a1) -> ((string,
        ct) P.F.fs -> (string, arrowT) P.F.fs -> 'a1) -> ct -> 'a1

      val ct_rec :
        (t -> 'a1) -> ((string, ct) P.F.fs -> params -> 'a1) -> ((string, ct)
        P.F.fs -> params -> 'a1) -> ((string, ct) P.F.fs -> 'a1) -> ((string,
        ct) P.F.fs -> (string, arrowT) P.F.fs -> 'a1) -> ct -> 'a1

      type constructor_params = (string, ct) P.F.fs

      module TypeNotations :
       sig
       end

      type uop = P4cub.Expr.uop =
      | Not
      | BitNot
      | UMinus
      | IsValid
      | SetValid
      | SetInValid
      | NextIndex
      | Size
      | Push of positive
      | Pop of positive

      val uop_rect :
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (positive ->
        'a1) -> (positive -> 'a1) -> uop -> 'a1

      val uop_rec :
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (positive ->
        'a1) -> (positive -> 'a1) -> uop -> 'a1

      module UopNotations :
       sig
       end

      type bop = P4cub.Expr.bop =
      | Plus
      | PlusSat
      | Minus
      | MinusSat
      | Times
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

      val bop_rect :
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> bop ->
        'a1

      val bop_rec :
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> bop ->
        'a1

      module BopNotations :
       sig
       end

      type matchkind = P4cub.Expr.matchkind =
      | MKExact
      | MKTernary
      | MKLpm

      val matchkind_rect : 'a1 -> 'a1 -> 'a1 -> matchkind -> 'a1

      val matchkind_rec : 'a1 -> 'a1 -> 'a1 -> matchkind -> 'a1

      val coq_MatchKindEqDec : matchkind coq_EqDec

      module MatchkindNotations :
       sig
       end

      type 'tags_t e = 'tags_t P4cub.Expr.e =
      | EBool of bool * 'tags_t
      | EBit of positive * coq_Z * 'tags_t
      | EInt of positive * coq_Z * 'tags_t
      | EVar of t * string * 'tags_t
      | ESlice of 'tags_t e * t * positive * positive * 'tags_t
      | ECast of t * 'tags_t e * 'tags_t
      | EUop of uop * t * 'tags_t e * 'tags_t
      | EBop of bop * t * t * 'tags_t e * 'tags_t e * 'tags_t
      | ETuple of 'tags_t e list * 'tags_t
      | EStruct of (string, t * 'tags_t e) P.F.fs * 'tags_t
      | EHeader of (string, t * 'tags_t e) P.F.fs * 'tags_t e * 'tags_t
      | EExprMember of string * t * 'tags_t e * 'tags_t
      | EError of string option * 'tags_t
      | EMatchKind of matchkind * 'tags_t
      | EHeaderStack of (string, t) P.F.fs * 'tags_t e list * positive
         * coq_Z * 'tags_t
      | EHeaderStackAccess of 'tags_t e * coq_Z * 'tags_t

      val e_rect :
        (bool -> 'a1 -> 'a2) -> (positive -> coq_Z -> 'a1 -> 'a2) ->
        (positive -> coq_Z -> 'a1 -> 'a2) -> (t -> string -> 'a1 -> 'a2) ->
        ('a1 e -> 'a2 -> t -> positive -> positive -> 'a1 -> 'a2) -> (t ->
        'a1 e -> 'a2 -> 'a1 -> 'a2) -> (uop -> t -> 'a1 e -> 'a2 -> 'a1 ->
        'a2) -> (bop -> t -> t -> 'a1 e -> 'a2 -> 'a1 e -> 'a2 -> 'a1 -> 'a2)
        -> ('a1 e list -> 'a1 -> 'a2) -> ((string, t * 'a1 e) P.F.fs -> 'a1
        -> 'a2) -> ((string, t * 'a1 e) P.F.fs -> 'a1 e -> 'a2 -> 'a1 -> 'a2)
        -> (string -> t -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (string option ->
        'a1 -> 'a2) -> (matchkind -> 'a1 -> 'a2) -> ((string, t) P.F.fs ->
        'a1 e list -> positive -> coq_Z -> 'a1 -> 'a2) -> ('a1 e -> 'a2 ->
        coq_Z -> 'a1 -> 'a2) -> 'a1 e -> 'a2

      val e_rec :
        (bool -> 'a1 -> 'a2) -> (positive -> coq_Z -> 'a1 -> 'a2) ->
        (positive -> coq_Z -> 'a1 -> 'a2) -> (t -> string -> 'a1 -> 'a2) ->
        ('a1 e -> 'a2 -> t -> positive -> positive -> 'a1 -> 'a2) -> (t ->
        'a1 e -> 'a2 -> 'a1 -> 'a2) -> (uop -> t -> 'a1 e -> 'a2 -> 'a1 ->
        'a2) -> (bop -> t -> t -> 'a1 e -> 'a2 -> 'a1 e -> 'a2 -> 'a1 -> 'a2)
        -> ('a1 e list -> 'a1 -> 'a2) -> ((string, t * 'a1 e) P.F.fs -> 'a1
        -> 'a2) -> ((string, t * 'a1 e) P.F.fs -> 'a1 e -> 'a2 -> 'a1 -> 'a2)
        -> (string -> t -> 'a1 e -> 'a2 -> 'a1 -> 'a2) -> (string option ->
        'a1 -> 'a2) -> (matchkind -> 'a1 -> 'a2) -> ((string, t) P.F.fs ->
        'a1 e list -> positive -> coq_Z -> 'a1 -> 'a2) -> ('a1 e -> 'a2 ->
        coq_Z -> 'a1 -> 'a2) -> 'a1 e -> 'a2

      type 'tags_t args =
        (string, (t * 'tags_t e, t * 'tags_t e) P.paramarg) P.F.fs

      type 'tags_t arrowE =
        (string, t * 'tags_t e, t * 'tags_t e, t * 'tags_t e) P.arrow

      type 'tags_t constructor_arg = 'tags_t P4cub.Expr.constructor_arg =
      | CAExpr of 'tags_t e
      | CAName of string

      val constructor_arg_rect :
        ('a1 e -> 'a2) -> (string -> 'a2) -> 'a1 constructor_arg -> 'a2

      val constructor_arg_rec :
        ('a1 e -> 'a2) -> (string -> 'a2) -> 'a1 constructor_arg -> 'a2

      type 'tags_t constructor_args = (string, 'tags_t constructor_arg) P.F.fs

      module ExprNotations :
       sig
       end
     end

    module S :
     sig
      module E :
       sig
        type t = P4cub.Expr.t =
        | TBool
        | TBit of positive
        | TInt of positive
        | TError
        | TMatchKind
        | TTuple of t list
        | TStruct of (string, t) P.F.fs
        | THeader of (string, t) P.F.fs
        | THeaderStack of (string, t) P.F.fs * positive

        val t_rect :
          'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> 'a1 -> 'a1 -> (t
          list -> 'a1) -> ((string, t) P.F.fs -> 'a1) -> ((string, t) P.F.fs
          -> 'a1) -> ((string, t) P.F.fs -> positive -> 'a1) -> t -> 'a1

        val t_rec :
          'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> 'a1 -> 'a1 -> (t
          list -> 'a1) -> ((string, t) P.F.fs -> 'a1) -> ((string, t) P.F.fs
          -> 'a1) -> ((string, t) P.F.fs -> positive -> 'a1) -> t -> 'a1

        type params = (string, (t, t) P.paramarg) P.F.fs

        type arrowT = (string, t, t, t) P.arrow

        type ct = P4cub.Expr.ct =
        | CTType of t
        | CTControl of (string, ct) P.F.fs * params
        | CTParser of (string, ct) P.F.fs * params
        | CTPackage of (string, ct) P.F.fs
        | CTExtern of (string, ct) P.F.fs * (string, arrowT) P.F.fs

        val ct_rect :
          (t -> 'a1) -> ((string, ct) P.F.fs -> params -> 'a1) -> ((string,
          ct) P.F.fs -> params -> 'a1) -> ((string, ct) P.F.fs -> 'a1) ->
          ((string, ct) P.F.fs -> (string, arrowT) P.F.fs -> 'a1) -> ct -> 'a1

        val ct_rec :
          (t -> 'a1) -> ((string, ct) P.F.fs -> params -> 'a1) -> ((string,
          ct) P.F.fs -> params -> 'a1) -> ((string, ct) P.F.fs -> 'a1) ->
          ((string, ct) P.F.fs -> (string, arrowT) P.F.fs -> 'a1) -> ct -> 'a1

        type constructor_params = (string, ct) P.F.fs

        module TypeNotations :
         sig
         end

        type uop = P4cub.Expr.uop =
        | Not
        | BitNot
        | UMinus
        | IsValid
        | SetValid
        | SetInValid
        | NextIndex
        | Size
        | Push of positive
        | Pop of positive

        val uop_rect :
          'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (positive
          -> 'a1) -> (positive -> 'a1) -> uop -> 'a1

        val uop_rec :
          'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (positive
          -> 'a1) -> (positive -> 'a1) -> uop -> 'a1

        module UopNotations :
         sig
         end

        type bop = P4cub.Expr.bop =
        | Plus
        | PlusSat
        | Minus
        | MinusSat
        | Times
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

        val bop_rect :
          'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
          -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
          bop -> 'a1

        val bop_rec :
          'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
          -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
          bop -> 'a1

        module BopNotations :
         sig
         end

        type matchkind = P4cub.Expr.matchkind =
        | MKExact
        | MKTernary
        | MKLpm

        val matchkind_rect : 'a1 -> 'a1 -> 'a1 -> matchkind -> 'a1

        val matchkind_rec : 'a1 -> 'a1 -> 'a1 -> matchkind -> 'a1

        val coq_MatchKindEqDec : matchkind coq_EqDec

        module MatchkindNotations :
         sig
         end

        type 'tags_t e = 'tags_t P4cub.Expr.e =
        | EBool of bool * 'tags_t
        | EBit of positive * coq_Z * 'tags_t
        | EInt of positive * coq_Z * 'tags_t
        | EVar of t * string * 'tags_t
        | ESlice of 'tags_t e * t * positive * positive * 'tags_t
        | ECast of t * 'tags_t e * 'tags_t
        | EUop of uop * t * 'tags_t e * 'tags_t
        | EBop of bop * t * t * 'tags_t e * 'tags_t e * 'tags_t
        | ETuple of 'tags_t e list * 'tags_t
        | EStruct of (string, t * 'tags_t e) P.F.fs * 'tags_t
        | EHeader of (string, t * 'tags_t e) P.F.fs * 'tags_t e * 'tags_t
        | EExprMember of string * t * 'tags_t e * 'tags_t
        | EError of string option * 'tags_t
        | EMatchKind of matchkind * 'tags_t
        | EHeaderStack of (string, t) P.F.fs * 'tags_t e list * positive
           * coq_Z * 'tags_t
        | EHeaderStackAccess of 'tags_t e * coq_Z * 'tags_t

        val e_rect :
          (bool -> 'a1 -> 'a2) -> (positive -> coq_Z -> 'a1 -> 'a2) ->
          (positive -> coq_Z -> 'a1 -> 'a2) -> (t -> string -> 'a1 -> 'a2) ->
          ('a1 e -> 'a2 -> t -> positive -> positive -> 'a1 -> 'a2) -> (t ->
          'a1 e -> 'a2 -> 'a1 -> 'a2) -> (uop -> t -> 'a1 e -> 'a2 -> 'a1 ->
          'a2) -> (bop -> t -> t -> 'a1 e -> 'a2 -> 'a1 e -> 'a2 -> 'a1 ->
          'a2) -> ('a1 e list -> 'a1 -> 'a2) -> ((string, t * 'a1 e) P.F.fs
          -> 'a1 -> 'a2) -> ((string, t * 'a1 e) P.F.fs -> 'a1 e -> 'a2 ->
          'a1 -> 'a2) -> (string -> t -> 'a1 e -> 'a2 -> 'a1 -> 'a2) ->
          (string option -> 'a1 -> 'a2) -> (matchkind -> 'a1 -> 'a2) ->
          ((string, t) P.F.fs -> 'a1 e list -> positive -> coq_Z -> 'a1 ->
          'a2) -> ('a1 e -> 'a2 -> coq_Z -> 'a1 -> 'a2) -> 'a1 e -> 'a2

        val e_rec :
          (bool -> 'a1 -> 'a2) -> (positive -> coq_Z -> 'a1 -> 'a2) ->
          (positive -> coq_Z -> 'a1 -> 'a2) -> (t -> string -> 'a1 -> 'a2) ->
          ('a1 e -> 'a2 -> t -> positive -> positive -> 'a1 -> 'a2) -> (t ->
          'a1 e -> 'a2 -> 'a1 -> 'a2) -> (uop -> t -> 'a1 e -> 'a2 -> 'a1 ->
          'a2) -> (bop -> t -> t -> 'a1 e -> 'a2 -> 'a1 e -> 'a2 -> 'a1 ->
          'a2) -> ('a1 e list -> 'a1 -> 'a2) -> ((string, t * 'a1 e) P.F.fs
          -> 'a1 -> 'a2) -> ((string, t * 'a1 e) P.F.fs -> 'a1 e -> 'a2 ->
          'a1 -> 'a2) -> (string -> t -> 'a1 e -> 'a2 -> 'a1 -> 'a2) ->
          (string option -> 'a1 -> 'a2) -> (matchkind -> 'a1 -> 'a2) ->
          ((string, t) P.F.fs -> 'a1 e list -> positive -> coq_Z -> 'a1 ->
          'a2) -> ('a1 e -> 'a2 -> coq_Z -> 'a1 -> 'a2) -> 'a1 e -> 'a2

        type 'tags_t args =
          (string, (t * 'tags_t e, t * 'tags_t e) P.paramarg) P.F.fs

        type 'tags_t arrowE =
          (string, t * 'tags_t e, t * 'tags_t e, t * 'tags_t e) P.arrow

        type 'tags_t constructor_arg = 'tags_t P4cub.Expr.constructor_arg =
        | CAExpr of 'tags_t e
        | CAName of string

        val constructor_arg_rect :
          ('a1 e -> 'a2) -> (string -> 'a2) -> 'a1 constructor_arg -> 'a2

        val constructor_arg_rec :
          ('a1 e -> 'a2) -> (string -> 'a2) -> 'a1 constructor_arg -> 'a2

        type 'tags_t constructor_args =
          (string, 'tags_t constructor_arg) P.F.fs

        module ExprNotations :
         sig
         end
       end

      type 'tags_t s = 'tags_t P4cub.Stmt.s =
      | SSkip of 'tags_t
      | SVardecl of E.t * string * 'tags_t
      | SAssign of E.t * 'tags_t E.e * 'tags_t E.e * 'tags_t
      | SConditional of E.t * 'tags_t E.e * 'tags_t s * 'tags_t s * 'tags_t
      | SSeq of 'tags_t s * 'tags_t s * 'tags_t
      | SBlock of 'tags_t s
      | SExternMethodCall of string * string * 'tags_t E.arrowE * 'tags_t
      | SFunCall of string * 'tags_t E.arrowE * 'tags_t
      | SActCall of string * 'tags_t E.args * 'tags_t
      | SReturnVoid of 'tags_t
      | SReturnFruit of E.t * 'tags_t E.e * 'tags_t
      | SExit of 'tags_t
      | SInvoke of string * 'tags_t
      | SApply of string * 'tags_t E.args * 'tags_t

      val s_rect :
        ('a1 -> 'a2) -> (E.t -> string -> 'a1 -> 'a2) -> (E.t -> 'a1 E.e ->
        'a1 E.e -> 'a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1 s -> 'a2 -> 'a1 s ->
        'a2 -> 'a1 -> 'a2) -> ('a1 s -> 'a2 -> 'a1 s -> 'a2 -> 'a1 -> 'a2) ->
        ('a1 s -> 'a2 -> 'a2) -> (string -> string -> 'a1 E.arrowE -> 'a1 ->
        'a2) -> (string -> 'a1 E.arrowE -> 'a1 -> 'a2) -> (string -> 'a1
        E.args -> 'a1 -> 'a2) -> ('a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1 ->
        'a2) -> ('a1 -> 'a2) -> (string -> 'a1 -> 'a2) -> (string -> 'a1
        E.args -> 'a1 -> 'a2) -> 'a1 s -> 'a2

      val s_rec :
        ('a1 -> 'a2) -> (E.t -> string -> 'a1 -> 'a2) -> (E.t -> 'a1 E.e ->
        'a1 E.e -> 'a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1 s -> 'a2 -> 'a1 s ->
        'a2 -> 'a1 -> 'a2) -> ('a1 s -> 'a2 -> 'a1 s -> 'a2 -> 'a1 -> 'a2) ->
        ('a1 s -> 'a2 -> 'a2) -> (string -> string -> 'a1 E.arrowE -> 'a1 ->
        'a2) -> (string -> 'a1 E.arrowE -> 'a1 -> 'a2) -> (string -> 'a1
        E.args -> 'a1 -> 'a2) -> ('a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1 ->
        'a2) -> ('a1 -> 'a2) -> (string -> 'a1 -> 'a2) -> (string -> 'a1
        E.args -> 'a1 -> 'a2) -> 'a1 s -> 'a2

      module StmtNotations :
       sig
       end
     end

    type state = P4cub.Parser.state =
    | STStart
    | STAccept
    | STReject
    | STName of string

    val state_rect : 'a1 -> 'a1 -> 'a1 -> (string -> 'a1) -> state -> 'a1

    val state_rec : 'a1 -> 'a1 -> 'a1 -> (string -> 'a1) -> state -> 'a1

    type pat = P4cub.Parser.pat =
    | PATWild
    | PATMask of pat * pat
    | PATRange of pat * pat
    | PATBit of positive * coq_Z
    | PATInt of positive * coq_Z
    | PATTuple of pat list

    val pat_rect :
      'a1 -> (pat -> 'a1 -> pat -> 'a1 -> 'a1) -> (pat -> 'a1 -> pat -> 'a1
      -> 'a1) -> (positive -> coq_Z -> 'a1) -> (positive -> coq_Z -> 'a1) ->
      (pat list -> 'a1) -> pat -> 'a1

    val pat_rec :
      'a1 -> (pat -> 'a1 -> pat -> 'a1 -> 'a1) -> (pat -> 'a1 -> pat -> 'a1
      -> 'a1) -> (positive -> coq_Z -> 'a1) -> (positive -> coq_Z -> 'a1) ->
      (pat list -> 'a1) -> pat -> 'a1

    type 'tags_t e = 'tags_t P4cub.Parser.e =
    | PGoto of state * 'tags_t
    | PSelect of 'tags_t E.e * 'tags_t e * (pat, 'tags_t e) P.F.fs * 'tags_t

    val e_rect :
      (state -> 'a1 -> 'a2) -> ('a1 E.e -> 'a1 e -> 'a2 -> (pat, 'a1 e)
      P.F.fs -> 'a1 -> 'a2) -> 'a1 e -> 'a2

    val e_rec :
      (state -> 'a1 -> 'a2) -> ('a1 E.e -> 'a1 e -> 'a2 -> (pat, 'a1 e)
      P.F.fs -> 'a1 -> 'a2) -> 'a1 e -> 'a2

    type 'tags_t state_block = 'tags_t P4cub.Parser.state_block =
    | State of 'tags_t S.s * 'tags_t e

    val state_block_rect : ('a1 S.s -> 'a1 e -> 'a2) -> 'a1 state_block -> 'a2

    val state_block_rec : ('a1 S.s -> 'a1 e -> 'a2) -> 'a1 state_block -> 'a2

    module ParserNotations :
     sig
     end
   end

  type 'tags_t d = 'tags_t P4cub.TopDecl.d =
  | TPInstantiate of string * string * 'tags_t E.constructor_args * 'tags_t
  | TPExtern of string * E.constructor_params
     * (string, E.arrowT) Coq__1.F.fs * 'tags_t
  | TPControl of string * E.constructor_params * E.params * 'tags_t C.d
     * 'tags_t S.s * 'tags_t
  | TPParser of string * E.constructor_params * E.params
     * 'tags_t P.state_block * (string, 'tags_t P.state_block) Coq__1.F.fs
     * 'tags_t
  | TPFunction of string * E.arrowT * 'tags_t S.s * 'tags_t
  | TPPackage of string * E.constructor_params * 'tags_t
  | TPSeq of 'tags_t d * 'tags_t d * 'tags_t

  val d_rect :
    (string -> string -> 'a1 E.constructor_args -> 'a1 -> 'a2) -> (string ->
    E.constructor_params -> (string, E.arrowT) Coq__1.F.fs -> 'a1 -> 'a2) ->
    (string -> E.constructor_params -> E.params -> 'a1 C.d -> 'a1 S.s -> 'a1
    -> 'a2) -> (string -> E.constructor_params -> E.params -> 'a1
    P.state_block -> (string, 'a1 P.state_block) Coq__1.F.fs -> 'a1 -> 'a2)
    -> (string -> E.arrowT -> 'a1 S.s -> 'a1 -> 'a2) -> (string ->
    E.constructor_params -> 'a1 -> 'a2) -> ('a1 d -> 'a2 -> 'a1 d -> 'a2 ->
    'a1 -> 'a2) -> 'a1 d -> 'a2

  val d_rec :
    (string -> string -> 'a1 E.constructor_args -> 'a1 -> 'a2) -> (string ->
    E.constructor_params -> (string, E.arrowT) Coq__1.F.fs -> 'a1 -> 'a2) ->
    (string -> E.constructor_params -> E.params -> 'a1 C.d -> 'a1 S.s -> 'a1
    -> 'a2) -> (string -> E.constructor_params -> E.params -> 'a1
    P.state_block -> (string, 'a1 P.state_block) Coq__1.F.fs -> 'a1 -> 'a2)
    -> (string -> E.arrowT -> 'a1 S.s -> 'a1 -> 'a2) -> (string ->
    E.constructor_params -> 'a1 -> 'a2) -> ('a1 d -> 'a2 -> 'a1 d -> 'a2 ->
    'a1 -> 'a2) -> 'a1 d -> 'a2

  module TopDeclNotations :
   sig
   end
 end

val metadata : E.t

val hdrs : E.t

val parser_start_state : nat PA.state_block

val parsr_cparams : E.constructor_params

val parsr_params : E.params

val myparser : nat TD.d

val control_cparams : E.constructor_params

val control_params : E.params

val mycontrol_decl : nat CT.ControlDecl.d

val mycontrol : nat TD.d

val deparser_cparams : E.constructor_params

val deparser_params : E.params

val mydeparser_decl : nat CT.ControlDecl.d

val mydeparser : nat TD.d

val helloworld_program : nat TD.d
