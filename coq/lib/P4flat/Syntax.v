Require Import Coq.PArith.BinPos Coq.ZArith.BinInt.
Require Export Poulet4.P4cub.Syntax.P4Field.
Import String.

(** * P4flat AST *)

Record bits := { width: N;
                 value: N }.

(** * Expressions *)
Module Expr.

  Inductive struct_kind :=
  | Header
  | Struct.

  Inductive t : Set :=
  | TBit (b : bits)
  | TStruct (kind: struct_kind)
            (fields: list t)
  | TVar (type_name : nat).
  
  (** Function signatures/instantiations. *)
  Record arrow : Set :=
    { in_params : list (string * t);
      out_params : list (string * t);
      return_typ : option t }.
    
  Inductive uop : Set :=
  | BitNot
  | Negate
  | IsValid
  | SetValidity (validity : bool).
  
  Variant arith_signedness :=
  | Unsigned
  | Signed.

  Variant arith_bop : Set :=
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
  | Gt.

  Inductive bop : Set :=
  | Arith (s: arith_signedness) (o: arith_bop)
  | Eq
  | NotEq
  | And
  | Xor
  | Or
  | PlusPlus.

  (** "list" variants:
      structs, headers, and arrays. *)
  Variant lists : Set :=
  | lists_struct
  | lists_header (b : bool).
  
  (** Expressions annotated with types,
      unless the type is obvious. *)  
  Inductive e : Set :=
  | Var (type : t) (original_name : string) (x : nat)
  | Bit (width : N) (val : Z)
  (* VARIOUS SIDE-EFFECT-FREE OPERATORS *)
  | Lists (flag : lists)
          (es : list e)
  | Slice (hi lo : positive) (arg : e)
  | Cast (type : t) (arg : e)
  | Uop (result_type : t)
        (op : uop)
        (arg : e)
  | Bop (result_type : t)
        (op : bop)
        (lhs rhs : e)
  | Index (elem_type : t) (array index : e)
  | Member (result_type : t) (mem : nat) (arg : e)
  | Error (err : string).
  
End Expr.

Module Lval.
  Inductive lv :=
  | Var (v: string)
  | Index (array : lv) (index : nat)
  | Member (struct: lv) (field : nat).
End Lval.

Module Pattern.
  Inductive pat : Set :=
  | Wild                             (** wild-card/anything pattern *)
  | Mask  (p1 p2 : bits)             (** mask pattern *)
  | Range (p1 p2 : bits)             (** range pattern *)
  | Bit (b : bits)                   (** unsigned-int pattern *)
  | Lists (ps : list pat)            (** lists pattern *).
End Pattern.

(** * Statement and Block Grammar *)
Module Stmt.

  (** Statements. *)
  Inductive s : Set :=
  | Skip
  | Seq (s1 s2 : s)
  | If (cond : Expr.e) (tru fls : s)
  | Var (name : string) (initializer : Expr.e)
  | Assign (lhs : Lval.lv) (rhs : Expr.e)
  | Call (func : string)
         (in_args : list Expr.e)
         (out_args : list Lval.lv)
         (ret : option Expr.e)
  | Table (const_rules: list (list Pattern.pat * s))
          (ctrl_plane_name: string)
          (key: list Expr.e).
End Stmt.

(** Top-Level Declarations *)
Module TopDecl.
  
  (** Top-level declarations. *)
  Variant d : Set :=
    | FunBlock
        (action_name : string)
        (in_params: list string)
        (out_params: list string)
        (body : Stmt.s)
    | Pkg (name: string) (cargs: list string).

  (** A p4cub program. *)
  Definition prog : Set := list d.
End TopDecl.
