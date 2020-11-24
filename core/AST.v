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

(** * Definitions and Lemmas regarding Fields *)
Module Field (P4 : P4DataTypes).
  (** Field type. *)
  Definition f (T : Set) : Set := P4.id * T.

  (** Fields. *)
  Definition fs (T : Set) : Set := list (f T).

  (** Predicate on a field's data. *)
  Definition predf_data {T : Set} (P : T -> Prop) : f T -> Prop :=
    fun '(_, t) => P t.

  (** Predicate over every data in fields. *)
  Definition predfs_data {T : Set} (P : T -> Prop) : fs T -> Prop :=
    Forall (predf_data P).
End Field.

(** Directions. *)
Inductive dir : Set := DIn | DOut | DInOut | DZilch.

(** * Expression Grammar *)
Module Expr (P4 : P4DataTypes).
  Module F := Field P4.
  Export F.

  (** Expression types. *)
  Inductive t : Set :=
    | TInteger
    | TBitstring (n : P4.int)
    | TError
    | TMatchKind
    | TRecord (fields : fs t)
    | THeader (fields : fs t)
    | TTypeName (X : P4.id).

  (** Custom induction principle for [t]. *)
  Section TypeInduction.
    (** An arbitrary property. *)
    Variable P : t -> Prop.

    Hypothesis HTInteger : P TInteger.

    Hypothesis HTBitstring : forall n : P4.int, P (TBitstring n).

    Hypothesis HTError : P TError.

    Hypothesis HTMatchKind : P TMatchKind.

    Hypothesis HTRecord : forall fields : list (P4.id * t),
        predfs_data P fields -> P (TRecord fields).

    Hypothesis HTHeader : forall fields : list (P4.id * t),
        predfs_data P fields -> P (THeader fields).

    Hypothesis HTTypeName : forall X : P4.id, P (TTypeName X).

    (** A custom induction principle.
        Do [induction ?t using custom_t_ind]. *)
    Definition custom_t_ind : forall ty : t, P ty :=
      fix custom_t_ind (type : t) : P type :=
        let fix fields_ind (flds : fs t) : predfs_data P flds :=
            match flds as fs_ty return predfs_data P fs_ty with
            | [] => Forall_nil (fun '(_, typ) => P typ)
            | ((_, hft) as hf) :: tf =>
              Forall_cons hf (custom_t_ind hft) (fields_ind tf)
            end in
        match type as ty return P ty with
        | TInteger => HTInteger
        | TBitstring n => HTBitstring n
        | TError => HTError
        | TMatchKind => HTMatchKind
        | TTypeName X => HTTypeName X
        | TRecord fields => HTRecord fields (fields_ind fields)
        | THeader fields => HTHeader fields (fields_ind fields)
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
    | EInteger (n : P4.int)
    | EBitstring (width : P4.int) (value : P4.bigint)
    | EVar (type : t) (x : P4.id)
    | EUop (op : uop) (type : t) : e -> e
    | EBop (op : bop) (lhs_type rhs_type : t) (lhs rhs : e)
    | ECast (cast_type : t) (expr_type : t) : e -> e
    | ERecord (fields : fs (t * e))
    | EExprMember (mem : P4.id) (expr_type : t) : e -> e
    | EError (name : P4.id)
    (* Extern or action calls. *)
    | ECall
        (callee_type : t) (callee : e)
        (args : fs (t * e)).

  (** A custom induction principle for [e]. *)
  Section ExprInduction.
    (** An arbitrary predicate. *)
    Variable P : e -> Prop.

    Hypothesis HEInteger : forall n : P4.int,
        P (EInteger n).

    Hypothesis HEBitstring : forall (w : P4.int) (v : P4.bigint),
        P (EBitstring w v).

    Hypothesis HEVar : forall (ty : t) (x : P4.id),
        P (EVar ty x).

    Hypothesis HEUop : forall (op : uop) (ty : t) (ex : e),
        P ex -> P (EUop op ty ex).

    Hypothesis HEBop : forall (op : bop) (lt rt : t) (lhs rhs : e),
        P lhs -> P rhs -> P (EBop op lt rt lhs rhs).

    Hypothesis HECast : forall (ct et : t) (ex : e),
        P ex -> P (ECast ct et ex).

    Hypothesis HERecord : forall (fields : fs (t * e)),
        predfs_data (fun '(_,ex) => P ex) fields -> P (ERecord fields).

    Hypothesis HEExprMember : forall (x : P4.id) (ty : t) (ex : e),
        P ex -> P (EExprMember x ty ex).

    Hypothesis HEError : forall (err : P4.id),
        P (EError err).

    Hypothesis HECall : forall (ty : t) (callee : e) (args : fs (t * e)),
        P callee -> predfs_data (fun '(_, exp) => P exp) args ->
        P (ECall ty callee args).

    (** A custom induction principle.
        Do [induction ?e using custom_e_ind]. *)
    Definition custom_e_ind : forall exp : e, P exp :=
      fix custom_e_ind (expr : e) : P expr :=
        let fix fields_ind (flds : fs (t * e))
            : predfs_data (fun '(_, exp) => P exp) flds :=
            match flds as fs_ex
                  return predfs_data (fun '(_, exp) => P exp) fs_ex with
            | [] => Forall_nil (predf_data (fun '(_, exp) => P exp))
            | ((_, (_, hfe)) as hf) :: tf =>
              Forall_cons hf (custom_e_ind hfe) (fields_ind tf)
            end in
        match expr as e' return P e' with
        | EInteger n => HEInteger n
        | EBitstring w v => HEBitstring w v
        | EVar ty x => HEVar ty x
        | EUop ty op exp => HEUop ty op exp (custom_e_ind exp)
        | EBop op lt rt lhs rhs =>
            HEBop op lt rt lhs rhs
                  (custom_e_ind lhs) (custom_e_ind rhs)
        | ECast ct et exp => HECast ct et exp (custom_e_ind exp)
        | ERecord fields => HERecord fields (fields_ind fields)
        | EExprMember x ty exp =>
            HEExprMember x ty exp (custom_e_ind exp)
        | EError err => HEError err
        | ECall ty callee args =>
            HECall ty callee args
                   (custom_e_ind callee)
                   (fields_ind args)
        end.
  End ExprInduction.
End Expr.
