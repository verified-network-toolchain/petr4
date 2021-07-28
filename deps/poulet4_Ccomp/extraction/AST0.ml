open BinNums
open Datatypes
open EquivDec
open EquivUtil
open P4Field

module P4cub =
 struct
  module F = Field

  type ('a, 'b) paramarg =
  | PAIn of 'a
  | PAOut of 'b
  | PAInOut of 'b

  (** val paramarg_rect :
      ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) paramarg ->
      'a3 **)

  let paramarg_rect f0 f1 f2 = function
  | PAIn x -> f0 x
  | PAOut x -> f1 x
  | PAInOut x -> f2 x

  (** val paramarg_rec :
      ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) paramarg ->
      'a3 **)

  let paramarg_rec f0 f1 f2 = function
  | PAIn x -> f0 x
  | PAOut x -> f1 x
  | PAInOut x -> f2 x

  (** val paramarg_map :
      ('a1 -> 'a3) -> ('a2 -> 'a4) -> ('a1, 'a2) paramarg -> ('a3, 'a4)
      paramarg **)

  let paramarg_map f0 g = function
  | PAIn a -> PAIn (f0 a)
  | PAOut b -> PAOut (g b)
  | PAInOut b -> PAInOut (g b)

  type ('k, 'a, 'b, 'r) arrow =
  | Arrow of ('k, ('a, 'b) paramarg) F.fs * 'r option

  (** val arrow_rect :
      (('a1, ('a2, 'a3) paramarg) F.fs -> 'a4 option -> 'a5) -> ('a1, 'a2,
      'a3, 'a4) arrow -> 'a5 **)

  let arrow_rect f0 = function
  | Arrow (x, x0) -> f0 x x0

  (** val arrow_rec :
      (('a1, ('a2, 'a3) paramarg) F.fs -> 'a4 option -> 'a5) -> ('a1, 'a2,
      'a3, 'a4) arrow -> 'a5 **)

  let arrow_rec f0 = function
  | Arrow (x, x0) -> f0 x x0

  module Expr =
   struct
    type t =
    | TBool
    | TBit of positive
    | TInt of positive
    | TError
    | TMatchKind
    | TTuple of t list
    | TStruct of (string, t) F.fs
    | THeader of (string, t) F.fs
    | THeaderStack of (string, t) F.fs * positive

    (** val t_rect :
        'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> 'a1 -> 'a1 -> (t
        list -> 'a1) -> ((string, t) F.fs -> 'a1) -> ((string, t) F.fs ->
        'a1) -> ((string, t) F.fs -> positive -> 'a1) -> t -> 'a1 **)

    let t_rect f0 f1 f2 f3 f4 f5 f6 f7 f8 = function
    | TBool -> f0
    | TBit x -> f1 x
    | TInt x -> f2 x
    | TError -> f3
    | TMatchKind -> f4
    | TTuple x -> f5 x
    | TStruct x -> f6 x
    | THeader x -> f7 x
    | THeaderStack (x, x0) -> f8 x x0

    (** val t_rec :
        'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> 'a1 -> 'a1 -> (t
        list -> 'a1) -> ((string, t) F.fs -> 'a1) -> ((string, t) F.fs ->
        'a1) -> ((string, t) F.fs -> positive -> 'a1) -> t -> 'a1 **)

    let t_rec f0 f1 f2 f3 f4 f5 f6 f7 f8 = function
    | TBool -> f0
    | TBit x -> f1 x
    | TInt x -> f2 x
    | TError -> f3
    | TMatchKind -> f4
    | TTuple x -> f5 x
    | TStruct x -> f6 x
    | THeader x -> f7 x
    | THeaderStack (x, x0) -> f8 x x0

    type params = (string, (t, t) paramarg) F.fs

    type arrowT = (string, t, t, t) arrow

    type ct =
    | CTType of t
    | CTControl of (string, ct) F.fs * params
    | CTParser of (string, ct) F.fs * params
    | CTPackage of (string, ct) F.fs
    | CTExtern of (string, ct) F.fs * (string, arrowT) F.fs

    (** val ct_rect :
        (t -> 'a1) -> ((string, ct) F.fs -> params -> 'a1) -> ((string, ct)
        F.fs -> params -> 'a1) -> ((string, ct) F.fs -> 'a1) -> ((string, ct)
        F.fs -> (string, arrowT) F.fs -> 'a1) -> ct -> 'a1 **)

    let ct_rect f0 f1 f2 f3 f4 = function
    | CTType x -> f0 x
    | CTControl (x, x0) -> f1 x x0
    | CTParser (x, x0) -> f2 x x0
    | CTPackage x -> f3 x
    | CTExtern (x, x0) -> f4 x x0

    (** val ct_rec :
        (t -> 'a1) -> ((string, ct) F.fs -> params -> 'a1) -> ((string, ct)
        F.fs -> params -> 'a1) -> ((string, ct) F.fs -> 'a1) -> ((string, ct)
        F.fs -> (string, arrowT) F.fs -> 'a1) -> ct -> 'a1 **)

    let ct_rec f0 f1 f2 f3 f4 = function
    | CTType x -> f0 x
    | CTControl (x, x0) -> f1 x x0
    | CTParser (x, x0) -> f2 x x0
    | CTPackage x -> f3 x
    | CTExtern (x, x0) -> f4 x x0

    type constructor_params = (string, ct) F.fs

    module TypeNotations =
     struct
     end

    type uop =
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

    (** val uop_rect :
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (positive ->
        'a1) -> (positive -> 'a1) -> uop -> 'a1 **)

    let uop_rect f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 = function
    | Not -> f0
    | BitNot -> f1
    | UMinus -> f2
    | IsValid -> f3
    | SetValid -> f4
    | SetInValid -> f5
    | NextIndex -> f6
    | Size -> f7
    | Push x -> f8 x
    | Pop x -> f9 x

    (** val uop_rec :
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (positive ->
        'a1) -> (positive -> 'a1) -> uop -> 'a1 **)

    let uop_rec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 = function
    | Not -> f0
    | BitNot -> f1
    | UMinus -> f2
    | IsValid -> f3
    | SetValid -> f4
    | SetInValid -> f5
    | NextIndex -> f6
    | Size -> f7
    | Push x -> f8 x
    | Pop x -> f9 x

    module UopNotations =
     struct
     end

    type bop =
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

    (** val bop_rect :
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> bop ->
        'a1 **)

    let bop_rect f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 = function
    | Plus -> f0
    | PlusSat -> f1
    | Minus -> f2
    | MinusSat -> f3
    | Times -> f4
    | Shl -> f5
    | Shr -> f6
    | Le -> f7
    | Ge -> f8
    | Lt -> f9
    | Gt -> f10
    | Eq -> f11
    | NotEq -> f12
    | BitAnd -> f13
    | BitXor -> f14
    | BitOr -> f15
    | PlusPlus -> f16
    | And -> f17
    | Or -> f18

    (** val bop_rec :
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
        'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> bop ->
        'a1 **)

    let bop_rec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 = function
    | Plus -> f0
    | PlusSat -> f1
    | Minus -> f2
    | MinusSat -> f3
    | Times -> f4
    | Shl -> f5
    | Shr -> f6
    | Le -> f7
    | Ge -> f8
    | Lt -> f9
    | Gt -> f10
    | Eq -> f11
    | NotEq -> f12
    | BitAnd -> f13
    | BitXor -> f14
    | BitOr -> f15
    | PlusPlus -> f16
    | And -> f17
    | Or -> f18

    module BopNotations =
     struct
     end

    type matchkind =
    | MKExact
    | MKTernary
    | MKLpm

    (** val matchkind_rect : 'a1 -> 'a1 -> 'a1 -> matchkind -> 'a1 **)

    let matchkind_rect f0 f1 f2 = function
    | MKExact -> f0
    | MKTernary -> f1
    | MKLpm -> f2

    (** val matchkind_rec : 'a1 -> 'a1 -> 'a1 -> matchkind -> 'a1 **)

    let matchkind_rec f0 f1 f2 = function
    | MKExact -> f0
    | MKTernary -> f1
    | MKLpm -> f2

    (** val coq_MatchKindEqDec : matchkind coq_EqDec **)

    let coq_MatchKindEqDec x y =
      match x with
      | MKExact -> (match y with
                    | MKExact -> true
                    | _ -> false)
      | MKTernary -> (match y with
                      | MKTernary -> true
                      | _ -> false)
      | MKLpm -> (match y with
                  | MKLpm -> true
                  | _ -> false)

    module MatchkindNotations =
     struct
     end

    type 'tags_t e =
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

    (** val e_rect :
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
        'a1 -> 'a2) -> 'a1 e -> 'a2 **)

    let rec e_rect f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 = function
    | EBool (b, i) -> f0 b i
    | EBit (width, val0, i) -> f1 width val0 i
    | EInt (width, val0, i) -> f2 width val0 i
    | EVar (type0, x, i) -> f3 type0 x i
    | ESlice (n, _UU03c4_, hi, lo, i) ->
      f4 n (e_rect f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 n)
        _UU03c4_ hi lo i
    | ECast (type0, arg, i) ->
      f5 type0 arg
        (e_rect f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 arg) i
    | EUop (op, type0, arg, i) ->
      f6 op type0 arg
        (e_rect f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 arg) i
    | EBop (op, lhs_type, rhs_type, lhs, rhs, i) ->
      f7 op lhs_type rhs_type lhs
        (e_rect f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 lhs)
        rhs
        (e_rect f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rhs) i
    | ETuple (es, i) -> f8 es i
    | EStruct (fields, i) -> f9 fields i
    | EHeader (fields, valid, i) ->
      f10 fields valid
        (e_rect f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 valid) i
    | EExprMember (mem, expr_type, arg, i) ->
      f11 mem expr_type arg
        (e_rect f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 arg) i
    | EError (err, i) -> f12 err i
    | EMatchKind (mk, i) -> f13 mk i
    | EHeaderStack (fields, headers, size, next_index, i) ->
      f14 fields headers size next_index i
    | EHeaderStackAccess (stack, index, i) ->
      f15 stack
        (e_rect f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 stack)
        index i

    (** val e_rec :
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
        'a1 -> 'a2) -> 'a1 e -> 'a2 **)

    let rec e_rec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 = function
    | EBool (b, i) -> f0 b i
    | EBit (width, val0, i) -> f1 width val0 i
    | EInt (width, val0, i) -> f2 width val0 i
    | EVar (type0, x, i) -> f3 type0 x i
    | ESlice (n, _UU03c4_, hi, lo, i) ->
      f4 n (e_rec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 n)
        _UU03c4_ hi lo i
    | ECast (type0, arg, i) ->
      f5 type0 arg
        (e_rec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 arg) i
    | EUop (op, type0, arg, i) ->
      f6 op type0 arg
        (e_rec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 arg) i
    | EBop (op, lhs_type, rhs_type, lhs, rhs, i) ->
      f7 op lhs_type rhs_type lhs
        (e_rec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 lhs) rhs
        (e_rec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rhs) i
    | ETuple (es, i) -> f8 es i
    | EStruct (fields, i) -> f9 fields i
    | EHeader (fields, valid, i) ->
      f10 fields valid
        (e_rec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 valid) i
    | EExprMember (mem, expr_type, arg, i) ->
      f11 mem expr_type arg
        (e_rec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 arg) i
    | EError (err, i) -> f12 err i
    | EMatchKind (mk, i) -> f13 mk i
    | EHeaderStack (fields, headers, size, next_index, i) ->
      f14 fields headers size next_index i
    | EHeaderStackAccess (stack, index, i) ->
      f15 stack
        (e_rec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 stack)
        index i

    type 'tags_t args = (string, (t * 'tags_t e, t * 'tags_t e) paramarg) F.fs

    type 'tags_t arrowE =
      (string, t * 'tags_t e, t * 'tags_t e, t * 'tags_t e) arrow

    type 'tags_t constructor_arg =
    | CAExpr of 'tags_t e
    | CAName of string

    (** val constructor_arg_rect :
        ('a1 e -> 'a2) -> (string -> 'a2) -> 'a1 constructor_arg -> 'a2 **)

    let constructor_arg_rect f0 f1 = function
    | CAExpr x -> f0 x
    | CAName x -> f1 x

    (** val constructor_arg_rec :
        ('a1 e -> 'a2) -> (string -> 'a2) -> 'a1 constructor_arg -> 'a2 **)

    let constructor_arg_rec f0 f1 = function
    | CAExpr x -> f0 x
    | CAName x -> f1 x

    type 'tags_t constructor_args = (string, 'tags_t constructor_arg) F.fs

    module ExprNotations =
     struct
     end
   end

  module Stmt =
   struct
    module E = Expr

    type 'tags_t s =
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

    (** val s_rect :
        ('a1 -> 'a2) -> (E.t -> string -> 'a1 -> 'a2) -> (E.t -> 'a1 E.e ->
        'a1 E.e -> 'a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1 s -> 'a2 -> 'a1 s ->
        'a2 -> 'a1 -> 'a2) -> ('a1 s -> 'a2 -> 'a1 s -> 'a2 -> 'a1 -> 'a2) ->
        ('a1 s -> 'a2 -> 'a2) -> (string -> string -> 'a1 E.arrowE -> 'a1 ->
        'a2) -> (string -> 'a1 E.arrowE -> 'a1 -> 'a2) -> (string -> 'a1
        E.args -> 'a1 -> 'a2) -> ('a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1 ->
        'a2) -> ('a1 -> 'a2) -> (string -> 'a1 -> 'a2) -> (string -> 'a1
        E.args -> 'a1 -> 'a2) -> 'a1 s -> 'a2 **)

    let rec s_rect f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 = function
    | SSkip i -> f0 i
    | SVardecl (type0, x, i) -> f1 type0 x i
    | SAssign (type0, lhs, rhs, i) -> f2 type0 lhs rhs i
    | SConditional (guard_type, guard, tru_blk, fls_blk, i) ->
      f3 guard_type guard tru_blk
        (s_rect f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 tru_blk)
        fls_blk
        (s_rect f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 fls_blk) i
    | SSeq (s1, s2, i) ->
      f4 s1 (s_rect f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 s1) s2
        (s_rect f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 s2) i
    | SBlock blk ->
      f5 blk (s_rect f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 blk)
    | SExternMethodCall (e0, f14, args0, i) -> f6 e0 f14 args0 i
    | SFunCall (f14, args0, i) -> f7 f14 args0 i
    | SActCall (f14, args0, i) -> f8 f14 args0 i
    | SReturnVoid i -> f9 i
    | SReturnFruit (t0, e0, i) -> f10 t0 e0 i
    | SExit i -> f11 i
    | SInvoke (x, i) -> f12 x i
    | SApply (x, args0, i) -> f13 x args0 i

    (** val s_rec :
        ('a1 -> 'a2) -> (E.t -> string -> 'a1 -> 'a2) -> (E.t -> 'a1 E.e ->
        'a1 E.e -> 'a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1 s -> 'a2 -> 'a1 s ->
        'a2 -> 'a1 -> 'a2) -> ('a1 s -> 'a2 -> 'a1 s -> 'a2 -> 'a1 -> 'a2) ->
        ('a1 s -> 'a2 -> 'a2) -> (string -> string -> 'a1 E.arrowE -> 'a1 ->
        'a2) -> (string -> 'a1 E.arrowE -> 'a1 -> 'a2) -> (string -> 'a1
        E.args -> 'a1 -> 'a2) -> ('a1 -> 'a2) -> (E.t -> 'a1 E.e -> 'a1 ->
        'a2) -> ('a1 -> 'a2) -> (string -> 'a1 -> 'a2) -> (string -> 'a1
        E.args -> 'a1 -> 'a2) -> 'a1 s -> 'a2 **)

    let rec s_rec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 = function
    | SSkip i -> f0 i
    | SVardecl (type0, x, i) -> f1 type0 x i
    | SAssign (type0, lhs, rhs, i) -> f2 type0 lhs rhs i
    | SConditional (guard_type, guard, tru_blk, fls_blk, i) ->
      f3 guard_type guard tru_blk
        (s_rec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 tru_blk) fls_blk
        (s_rec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 fls_blk) i
    | SSeq (s1, s2, i) ->
      f4 s1 (s_rec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 s1) s2
        (s_rec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 s2) i
    | SBlock blk ->
      f5 blk (s_rec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 blk)
    | SExternMethodCall (e0, f14, args0, i) -> f6 e0 f14 args0 i
    | SFunCall (f14, args0, i) -> f7 f14 args0 i
    | SActCall (f14, args0, i) -> f8 f14 args0 i
    | SReturnVoid i -> f9 i
    | SReturnFruit (t0, e0, i) -> f10 t0 e0 i
    | SExit i -> f11 i
    | SInvoke (x, i) -> f12 x i
    | SApply (x, args0, i) -> f13 x args0 i

    module StmtNotations =
     struct
     end
   end

  module Parser =
   struct
    module E = Expr

    module S = Stmt

    type state =
    | STStart
    | STAccept
    | STReject
    | STName of string

    (** val state_rect :
        'a1 -> 'a1 -> 'a1 -> (string -> 'a1) -> state -> 'a1 **)

    let state_rect f0 f1 f2 f3 = function
    | STStart -> f0
    | STAccept -> f1
    | STReject -> f2
    | STName x -> f3 x

    (** val state_rec :
        'a1 -> 'a1 -> 'a1 -> (string -> 'a1) -> state -> 'a1 **)

    let state_rec f0 f1 f2 f3 = function
    | STStart -> f0
    | STAccept -> f1
    | STReject -> f2
    | STName x -> f3 x

    type pat =
    | PATWild
    | PATMask of pat * pat
    | PATRange of pat * pat
    | PATBit of positive * coq_Z
    | PATInt of positive * coq_Z
    | PATTuple of pat list

    (** val pat_rect :
        'a1 -> (pat -> 'a1 -> pat -> 'a1 -> 'a1) -> (pat -> 'a1 -> pat -> 'a1
        -> 'a1) -> (positive -> coq_Z -> 'a1) -> (positive -> coq_Z -> 'a1)
        -> (pat list -> 'a1) -> pat -> 'a1 **)

    let rec pat_rect f0 f1 f2 f3 f4 f5 = function
    | PATWild -> f0
    | PATMask (p1, p2) ->
      f1 p1 (pat_rect f0 f1 f2 f3 f4 f5 p1) p2 (pat_rect f0 f1 f2 f3 f4 f5 p2)
    | PATRange (p1, p2) ->
      f2 p1 (pat_rect f0 f1 f2 f3 f4 f5 p1) p2 (pat_rect f0 f1 f2 f3 f4 f5 p2)
    | PATBit (w, n) -> f3 w n
    | PATInt (w, n) -> f4 w n
    | PATTuple ps -> f5 ps

    (** val pat_rec :
        'a1 -> (pat -> 'a1 -> pat -> 'a1 -> 'a1) -> (pat -> 'a1 -> pat -> 'a1
        -> 'a1) -> (positive -> coq_Z -> 'a1) -> (positive -> coq_Z -> 'a1)
        -> (pat list -> 'a1) -> pat -> 'a1 **)

    let rec pat_rec f0 f1 f2 f3 f4 f5 = function
    | PATWild -> f0
    | PATMask (p1, p2) ->
      f1 p1 (pat_rec f0 f1 f2 f3 f4 f5 p1) p2 (pat_rec f0 f1 f2 f3 f4 f5 p2)
    | PATRange (p1, p2) ->
      f2 p1 (pat_rec f0 f1 f2 f3 f4 f5 p1) p2 (pat_rec f0 f1 f2 f3 f4 f5 p2)
    | PATBit (w, n) -> f3 w n
    | PATInt (w, n) -> f4 w n
    | PATTuple ps -> f5 ps

    type 'tags_t e =
    | PGoto of state * 'tags_t
    | PSelect of 'tags_t E.e * 'tags_t e * (pat, 'tags_t e) F.fs * 'tags_t

    (** val e_rect :
        (state -> 'a1 -> 'a2) -> ('a1 E.e -> 'a1 e -> 'a2 -> (pat, 'a1 e)
        F.fs -> 'a1 -> 'a2) -> 'a1 e -> 'a2 **)

    let rec e_rect f0 f1 = function
    | PGoto (st, i) -> f0 st i
    | PSelect (exp, default, cases, i) ->
      f1 exp default (e_rect f0 f1 default) cases i

    (** val e_rec :
        (state -> 'a1 -> 'a2) -> ('a1 E.e -> 'a1 e -> 'a2 -> (pat, 'a1 e)
        F.fs -> 'a1 -> 'a2) -> 'a1 e -> 'a2 **)

    let rec e_rec f0 f1 = function
    | PGoto (st, i) -> f0 st i
    | PSelect (exp, default, cases, i) ->
      f1 exp default (e_rec f0 f1 default) cases i

    type 'tags_t state_block =
    | State of 'tags_t S.s * 'tags_t e

    (** val state_block_rect :
        ('a1 S.s -> 'a1 e -> 'a2) -> 'a1 state_block -> 'a2 **)

    let state_block_rect f0 = function
    | State (x, x0) -> f0 x x0

    (** val state_block_rec :
        ('a1 S.s -> 'a1 e -> 'a2) -> 'a1 state_block -> 'a2 **)

    let state_block_rec f0 = function
    | State (x, x0) -> f0 x x0

    module ParserNotations =
     struct
     end
   end

  module Control =
   struct
    module E = Expr

    module S = Stmt

    module ControlDecl =
     struct
      type 'tags_t table =
      | Table of ((E.t * 'tags_t E.e) * E.matchkind) list * string list

      (** val table_rect :
          (((E.t * 'a1 E.e) * E.matchkind) list -> string list -> 'a2) -> 'a1
          table -> 'a2 **)

      let table_rect f0 = function
      | Table (x, x0) -> f0 x x0

      (** val table_rec :
          (((E.t * 'a1 E.e) * E.matchkind) list -> string list -> 'a2) -> 'a1
          table -> 'a2 **)

      let table_rec f0 = function
      | Table (x, x0) -> f0 x x0

      type 'tags_t d =
      | CDAction of string * E.params * 'tags_t S.s * 'tags_t
      | CDTable of string * 'tags_t table * 'tags_t
      | CDSeq of 'tags_t d * 'tags_t d * 'tags_t

      (** val d_rect :
          (string -> E.params -> 'a1 S.s -> 'a1 -> 'a2) -> (string -> 'a1
          table -> 'a1 -> 'a2) -> ('a1 d -> 'a2 -> 'a1 d -> 'a2 -> 'a1 ->
          'a2) -> 'a1 d -> 'a2 **)

      let rec d_rect f0 f1 f2 = function
      | CDAction (a, signature, body, i) -> f0 a signature body i
      | CDTable (t0, bdy, i) -> f1 t0 bdy i
      | CDSeq (d1, d2, i) ->
        f2 d1 (d_rect f0 f1 f2 d1) d2 (d_rect f0 f1 f2 d2) i

      (** val d_rec :
          (string -> E.params -> 'a1 S.s -> 'a1 -> 'a2) -> (string -> 'a1
          table -> 'a1 -> 'a2) -> ('a1 d -> 'a2 -> 'a1 d -> 'a2 -> 'a1 ->
          'a2) -> 'a1 d -> 'a2 **)

      let rec d_rec f0 f1 f2 = function
      | CDAction (a, signature, body, i) -> f0 a signature body i
      | CDTable (t0, bdy, i) -> f1 t0 bdy i
      | CDSeq (d1, d2, i) ->
        f2 d1 (d_rec f0 f1 f2 d1) d2 (d_rec f0 f1 f2 d2) i

      module ControlDeclNotations =
       struct
       end
     end
   end

  module TopDecl =
   struct
    module E = Expr

    module S = Stmt

    module C = Control.ControlDecl

    module P = Parser

    type 'tags_t d =
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

    (** val d_rect :
        (string -> string -> 'a1 E.constructor_args -> 'a1 -> 'a2) -> (string
        -> E.constructor_params -> (string, E.arrowT) F.fs -> 'a1 -> 'a2) ->
        (string -> E.constructor_params -> E.params -> 'a1 C.d -> 'a1 S.s ->
        'a1 -> 'a2) -> (string -> E.constructor_params -> E.params -> 'a1
        P.state_block -> (string, 'a1 P.state_block) F.fs -> 'a1 -> 'a2) ->
        (string -> E.arrowT -> 'a1 S.s -> 'a1 -> 'a2) -> (string ->
        E.constructor_params -> 'a1 -> 'a2) -> ('a1 d -> 'a2 -> 'a1 d -> 'a2
        -> 'a1 -> 'a2) -> 'a1 d -> 'a2 **)

    let rec d_rect f0 f1 f2 f3 f4 f5 f6 = function
    | TPInstantiate (c, x, cargs, i) -> f0 c x cargs i
    | TPExtern (e0, cparams, methods, i) -> f1 e0 cparams methods i
    | TPControl (c, cparams, params0, body, apply_blk, i) ->
      f2 c cparams params0 body apply_blk i
    | TPParser (p, cparams, params0, start, states, i) ->
      f3 p cparams params0 start states i
    | TPFunction (f7, signature, body, i) -> f4 f7 signature body i
    | TPPackage (p, cparams, i) -> f5 p cparams i
    | TPSeq (d1, d2, i) ->
      f6 d1 (d_rect f0 f1 f2 f3 f4 f5 f6 d1) d2
        (d_rect f0 f1 f2 f3 f4 f5 f6 d2) i

    (** val d_rec :
        (string -> string -> 'a1 E.constructor_args -> 'a1 -> 'a2) -> (string
        -> E.constructor_params -> (string, E.arrowT) F.fs -> 'a1 -> 'a2) ->
        (string -> E.constructor_params -> E.params -> 'a1 C.d -> 'a1 S.s ->
        'a1 -> 'a2) -> (string -> E.constructor_params -> E.params -> 'a1
        P.state_block -> (string, 'a1 P.state_block) F.fs -> 'a1 -> 'a2) ->
        (string -> E.arrowT -> 'a1 S.s -> 'a1 -> 'a2) -> (string ->
        E.constructor_params -> 'a1 -> 'a2) -> ('a1 d -> 'a2 -> 'a1 d -> 'a2
        -> 'a1 -> 'a2) -> 'a1 d -> 'a2 **)

    let rec d_rec f0 f1 f2 f3 f4 f5 f6 = function
    | TPInstantiate (c, x, cargs, i) -> f0 c x cargs i
    | TPExtern (e0, cparams, methods, i) -> f1 e0 cparams methods i
    | TPControl (c, cparams, params0, body, apply_blk, i) ->
      f2 c cparams params0 body apply_blk i
    | TPParser (p, cparams, params0, start, states, i) ->
      f3 p cparams params0 start states i
    | TPFunction (f7, signature, body, i) -> f4 f7 signature body i
    | TPPackage (p, cparams, i) -> f5 p cparams i
    | TPSeq (d1, d2, i) ->
      f6 d1 (d_rec f0 f1 f2 f3 f4 f5 f6 d1) d2
        (d_rec f0 f1 f2 f3 f4 f5 f6 d2) i

    module TopDeclNotations =
     struct
     end
   end

  module P4cubNotations =
   struct
   end
 end
