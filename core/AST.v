Require Coq.Strings.String.
Module CSS := Coq.Strings.String.
Require Coq.Arith.PeanoNat.
Module CAP := Coq.Arith.PeanoNat.
Require Export Coq.Lists.List.
Import ListNotations.

(** * P4 Data Types Signature *)
Module Type P4DataTypes.
  (** Names *)
  Parameter id : Set.

  (** Integer values *)
  Parameter int : Set.

  (** Large Integer values *)
  Parameter bigint : Set.
End P4DataTypes.

(** Directions. *)
Inductive dir : Set := DIn | DOut | DInOut | DZilch.

(** * Expression Grammar *)
Module Expr (P4 : P4DataTypes).
  Inductive recfield (A : Set) := rfield (x : P4.id) : A -> recfield A.

  (** Expression types. *)
  Inductive t : Set :=
    | TInteger
    | TBitstring (n : P4.int)
    | TError
    | TMatchKind
    | TRecord (fields : list (P4.id * t))
    | THeader (fields : list (P4.id * t))
    | TTypeName (X : P4.id).

  (* TODO: define appropriate induction principle *)
  (** Custom induction principle for [t] *)
  Section TypeInduction.
    (** An arbitrary property. *)
    Variable P : t -> Prop.

    Hypothesis HTInteger : P TInteger.

    Hypothesis HTBitstring : forall n : P4.int, P (TBitstring n).

    Hypothesis HTError : P TError.

    Hypothesis HTMatchKind : P TMatchKind.

    Hypothesis HTRecord : forall fields : list (P4.id * t),
        Forall (fun '(_, ty) => P ty) fields -> P (TRecord fields).

    Hypothesis HTHeader : forall fields : list (P4.id * t),
        Forall (fun '(_, ty) => P ty) fields -> P (THeader fields).

    Hypothesis HTTypeName : forall X : P4.id, P (TTypeName X).

    Fixpoint custom_t_ind (type : t) : P type :=
      match type as ty return P ty with
      | TInteger => HTInteger
      | TBitstring n => HTBitstring n
      | TError => HTError
      | TMatchKind => HTMatchKind
      | TTypeName X => HTTypeName X
      | TRecord fields =>
          let fix list_ih (fs : list (P4.id * t))
              : Forall (fun '(_, typ) => P typ) fs :=
              match fs as fs_ty return Forall (fun '(_, typ) => P typ) fs_ty with
              | [] => Forall_nil (fun '(_, typ) => P typ)
              | (hf, hft) :: tf =>
                  Forall_cons (hf, hft) (custom_t_ind hft) (list_ih tf)
              end in
          HTRecord fields (list_ih fields)
  | THeader fields =>
          let fix list_ih (fs : list (P4.id * t))
              : Forall (fun '(_, typ) => P typ) fs :=
              match fs as fs_ty return Forall (fun '(_, typ) => P typ) fs_ty with
              | [] => Forall_nil (fun '(_, typ) => P typ)
              | (hf, hft) :: tf =>
                  Forall_cons (hf, hft) (custom_t_ind hft) (list_ih tf)
              end in
          HTHeader fields (list_ih fields)
      end.
  End TypeInduction.

  Inductive uop : Set := Not | BitNot | UMinus.

  (** Binary operations.
      The "Sat" suffix denotes
      saturating arithmetic:
      where there is no overflow. *)
  Inductive bop : Set :=
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
    | Or.

   (** Expressions annotated with types,
       unless the type is obvious. *)
  Inductive e : Set :=
    | Integer (n : P4.int)
    | Bitstring (width : P4.int) (value : P4.bigint)
    | Var (type : t) (x : P4.id)
    | Uop (op : uop) (type : t) : e -> e
    | Bop (op : bop)
          (lhs_type : t) (lhs : e)
          (rhs_type : t) (rhs : e)
    | Cast (cast_type : t) (expr_type : t) : e -> e
    | Rec (fields : list (P4.id * t * e))
    | ExprMember (mem : P4.id) (expr_type : t) : e -> e
    | Error (name : P4.id)
    (* Extern or action calls. *)
    | Call
        (callee_type : t) (callee : e)
        (args : list (t * e)).
End Expr.
