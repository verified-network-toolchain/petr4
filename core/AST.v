Require Coq.Strings.String.
Module CSS := Coq.Strings.String.
Require Coq.Arith.PeanoNat.
Module CAP := Coq.Arith.PeanoNat.
Require Export Coq.Lists.List.
Import ListNotations.
Require Coq.Bool.Bool.
Module CBB := Coq.Bool.Bool.

Definition pipeline {A B : Type} (x : A) (f : A -> B) : B := f x.

Infix "▷" := pipeline (at level 45, left associativity).

Infix "∘" := Basics.compose
  (at level 40, left associativity).

(** * P4 Data Types Signature *)
Module Type P4Data.
  Parameter t : Type.
  Parameter eqb : t -> t -> bool.
  Axiom eqb_reflect : forall x y : t, CBB.reflect (x = y) (eqb x y).
End P4Data.

Module P4DataUtil (Export D : P4Data).
  Infix "=?" := eqb (at level 70, no associativity).

  Lemma eq_dec : forall x y : t, x = y \/ x <> y.
  Proof.
    intros x y. pose proof eqb_reflect x y as REFL.
    inversion REFL as [HT Hxy | HF Hxy]; subst; auto.
  Qed.
End P4DataUtil.

(** * P4 Numeric Types *)
Module Type P4Numeric <: P4Data.
  Include P4Data.

  (** Arithmetic operations and lemmas. *)

  Parameter add : t -> t -> t.
  Axiom add_comm : forall m n : t, add m n = add n m.
  Axiom add_assoc : forall a b c : t, add a (add b c) = add (add a b) c.

  Parameter sub : t -> t -> t.
  Axiom sub_assoc : forall a b c : t, sub a (sub b c) = sub (sub a b) c.

  Parameter mul : t -> t -> t.
  Axiom mul_comm : forall m n : t, mul m n = mul n m.
  Axiom mul_assoc : forall a b c : t, mul a (mul b c) = mul (mul a b) c.

  (** Ordered relations. *)

  Parameter le : t -> t -> Prop.

  Parameter lt : t -> t -> Prop.
End P4Numeric.

Module P4NumericUtil (N : P4Numeric).
  Include N.

  Infix "+" := add (at level 50, left associativity).

  Infix "-" := sub (at level 50, left associativity).

  Infix "*" := mul (at level 40, left associativity).

  Infix "<=" := le (at level 70, no associativity).

  Infix "<" := lt (at level 70, no associativity).
End P4NumericUtil.

(** * Definitions and Lemmas regarding Fields *)
Module Field (NAME : P4Data).
  (** Field type. *)
  Definition f (T : Type) : Type := NAME.t * T.

  (** Fields. *)
  Definition fs (T : Type) : Type := list (f T).

  (** Predicate on a field's data. *)
  Definition predf_data {T : Type} (P : T -> Prop) : f T -> Prop :=
    fun '(_, t) => P t.

  (** Predicate over every data in fields. *)
  Definition predfs_data {T : Type} (P : T -> Prop) : fs T -> Prop :=
    Forall (predf_data P).

  (** Relation betwixt two field instances. *)
  Definition relf {U V : Type} (R : U -> V -> Prop) : f U -> f V -> Prop :=
    fun u v => fst u = fst v /\ R (snd u) (snd v).

  (** Relation between two instances of fields. *)
  Definition relfs {U V : Type}
             (R : U -> V -> Prop) : fs U -> fs V -> Prop :=
    Forall2 (relf R).

  (** Filter. *)
  Definition filter {U : Type} (f : U -> bool) : fs U -> fs U :=
    List.filter (f ∘ snd).

  (** Map. *)
  Definition map {U V : Type} (f : U -> V) : fs U -> fs V :=
    List.map (fun '(x,u) => (x, f u)).

  (** Fold. *)
  Definition fold {U V : Type}
             (f : NAME.t -> U -> V -> V) (fs : fs U) (init : V) : V :=
    List.fold_right (fun '(x,u) acc => f x u acc) init fs.
End Field.

(** * P4 AST *)
Module P4 (NAME : P4Data) (INT BIGINT : P4Numeric).
  Module F := Field NAME.

  (** Directions. *)
  Module Dir.
    Inductive d := DIn | DOut | DInOut | DZilch.
  End Dir.

  (** * Expression Grammar *)
  Module Expr.
    Import Dir.

    (** Expression types. *)
    Inductive t : Type :=
      | TBool
      | TInteger
      | TBitstring (n : INT.t)
      | TError
      | TMatchKind
      | TRecord (fields : F.fs t)
      | THeader (fields : F.fs t)
      (* | TTypeName (X : NAME.t) *)
      (* | TArrow (params : F.fs (d * t)). *)
    (**[]*)

    (** Function signatures. *)
    Inductive arrow (A R : Type) : Type :=
      Arrow (params : F.fs (d * A)) (returns : option R).
    (**[]*)

    Arguments Arrow {A} _ _ _.

    (** Function types. *)
    Definition arrowT : Type := arrow t t.

    Module TypeNotations.
      Declare Custom Entry p4type.

      Notation "'{{' ty '}}'" := ty (ty custom p4type at level 99).
      Notation "( x )" := x (in custom p4type, x at level 99).
      Notation "x" := x (in custom p4type at level 0, x constr at level 0).
      Notation "'Bool'" := TBool (in custom p4type at level 0).
      Notation "'int'"
        := TInteger (in custom p4type at level 0, no associativity).
      Notation "'bit' '<' w '>'"
        := (TBitstring w)
            (in custom p4type at level 2,
                w custom p4type at level 99, no associativity).
      Notation "'error'" := TError
                              (in custom p4type at level 0, no associativity).
      Notation "'matchkind'"
        := TMatchKind (in custom p4type at level 0, no associativity).
      (*  Notation "'rec' { fx ';;' fy ';;' .. ';;' fz }"
              := (TRecord  (cons fx (cons fy .. (cons fz nil) ..)))
                          (in custom p4type at level 6, no associativity). *)
      Notation "'rec' { fields } "
        := (TRecord fields)
            (in custom p4type at level 6, no associativity).
      (*  Notation "'hdr' { fx ';;' fy ';;' .. ';;' fz }"
              := (THeader  (cons fx (cons fy .. (cons fz nil) ..)))
                          (in custom p4type at level 6, no associativity). *)
      Notation "'hdr' { fields } "
        := (THeader fields)
            (in custom p4type at level 6, no associativity).
      (* Notation "params ↦ return_typ"
              := (TArrow params return_typ)
                    (in custom p4type at level 10, no associativity). *)
    End TypeNotations.
    Import TypeNotations.

    (** Custom induction principle for [t]. *)
    Section TypeInduction.
      (** An arbitrary property. *)
      Variable P : t -> Prop.

      Hypothesis HTBool : P {{ Bool }}.

      Hypothesis HTInteger : P {{ int }}.

      Hypothesis HTBitstring : forall n : INT.t, P {{ bit<n> }}.

      Hypothesis HTError : P {{ error }}.

      Hypothesis HTMatchKind : P {{ matchkind }}.

      Hypothesis HTRecord : forall fields : F.fs t,
          F.predfs_data P fields -> P {{ rec { fields } }}.

      Hypothesis HTHeader : forall fields : F.fs t,
          F.predfs_data P fields -> P {{ hdr { fields } }}.

      (* Hypothesis HTTypeName : forall X : NAME.t, P (TTypeName X). *)

      (* Hypothesis HTArrow : forall (params : F.fs (d * t)),
          F.predfs_data (P ∘ snd) params -> P (TArrow params). *)

      (** A custom induction principle.
          Do [induction ?t using custom_t_ind]. *)
      Definition custom_t_ind : forall ty : t, P ty :=
        fix custom_t_ind (type : t) : P type :=
          let fix fields_ind (flds : F.fs t) : F.predfs_data P flds :=
              match flds as fs_ty return F.predfs_data P fs_ty with
              | [] => Forall_nil (F.predf_data P)
              | (_, hft) as hf :: tf =>
                Forall_cons hf (custom_t_ind hft) (fields_ind tf)
              end in
          let fix fields_ind_dir
                  (flds : F.fs (d * t)) : F.predfs_data (P ∘ snd) flds :=
              match flds as fs_ty return F.predfs_data (P ∘ snd) fs_ty with
              | [] => Forall_nil (F.predf_data (P ∘ snd))
              | (_, (_, hft)) as hf :: tf =>
                Forall_cons hf (custom_t_ind hft) (fields_ind_dir tf)
              end in
          match type as ty return P ty with
          | {{ Bool }} => HTBool
          | {{ int }} => HTInteger
          | {{ bit<w> }} => HTBitstring w
          | {{ error }} => HTError
          | {{ matchkind }} => HTMatchKind
          (* |   TTypeName X => HTTypeName X *)
          | {{ rec { fields } }} => HTRecord fields (fields_ind fields)
          | {{ hdr { fields } }} => HTHeader fields (fields_ind fields)
          (* | TArrow params => HTArrow params (fields_ind_dir params) *)
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
    (**[]*)

    (** Expressions annotated with types,
      unless the type is obvious. *)
    Inductive e : Type :=
      | EBool (b : bool)
      | EInteger (n : INT.t)
      | EBitstring (width : INT.t) (value : BIGINT.t)
      | EVar (type : t) (x : NAME.t)
      | EUop (op : uop) (type : t) : e -> e
      | EBop (op : bop) (lhs_type rhs_type : t) (lhs rhs : e)
      | ECast (cast_type : t) (expr_type : t) : e -> e
      | ERecord (fields : F.fs (t * e))
      | EExprMember (mem : NAME.t) (expr_type : t) : e -> e
      | EError (name : NAME.t)
      | EMatchKind (name : NAME.t).
      (* | ECall
          (callee_type : t) (callee : e)
          (args : F.fs (d * t * e)). *)
    (**[]*)

    (** Function call. *)
    Definition arrowE : Type := arrow (t * e) (t * NAME.t).

    Module ExprNotations.
      Export TypeNotations.

      Declare Custom Entry p4expr.

      Notation "'<{' exp '}>'" := exp (exp custom p4expr at level 99).
      Notation "( x )" := x (in custom p4expr, x at level 99).
      Notation "x" := x (in custom p4expr at level 0, x constr at level 0).
      Notation "'True'" := (EBool true) (in custom p4expr at level 0).
      Notation "'False'" := (EBool false) (in custom p4expr at level 0).
      Notation "'BOOL' b" := (EBool b) (in custom p4expr at level 0).
      Notation "'Int' n" := (EInteger n) (in custom p4expr at level 0).
      Notation "n '@' m" := (EBitstring n m)
                              (in custom p4expr at level 1, no associativity).
      Notation "'Var' x '::' ty 'end'" := (EVar ty x)
                            (in custom p4expr at level 0, no associativity).
      (*  Notation "'Loc' x" := (ELoc x)
                            (in custom p4expr at level 0, no associativity). *)
      Notation "'!' x '::' ty 'end'" := (EUop Not ty x)
                                  (in custom p4expr at level 2,
                                      x custom p4expr, ty custom p4type,
                                      no associativity).
      Notation "'~' x '::' ty 'end'" := (EUop BitNot ty x)
                                  (in custom p4expr at level 2,
                                      x custom p4expr, ty custom p4type,
                                      no associativity).
      Notation "'-' x '::' ty 'end'" := (EUop UMinus ty x)
                                  (in custom p4expr at level 2,
                                      x custom p4expr, ty custom p4type,
                                      no associativity).
      Notation "'+' x '::' tx y '::' ty 'end'"
        := (EBop Plus tx ty x y)
            (in custom p4expr at level 3,
                x custom p4expr, tx custom p4type,
                y custom p4expr, ty custom p4type, left associativity).
      Notation "'|+|' x '::' tx y '::' ty 'end'"
        := (EBop PlusSat tx ty x y)
            (in custom p4expr at level 4,
                x custom p4expr, tx custom p4type,
                y custom p4expr, ty custom p4type, left associativity).
      Notation "'--' x '::' tx y '::' ty 'end'"
        := (EBop Minus tx ty x y)
            (in custom p4expr at level 3,
                x custom p4expr, tx custom p4type,
                y custom p4expr, ty custom p4type, left associativity).
      Notation "'|-|' x '::' tx y '::' ty 'end'"
        := (EBop MinusSat tx ty x y)
            (in custom p4expr at level 4,
                x custom p4expr, tx custom p4type,
                y custom p4expr, ty custom p4type, left associativity).
      Notation "'<<' x '::' tx y '::' ty 'end'"
        := (EBop Shl tx ty x y)
            (in custom p4expr at level 5,
                x custom p4expr, tx custom p4type,
                y custom p4expr, ty custom p4type, left associativity).
      Notation "'>>' x '::' tx y '::' ty 'end'"
        := (EBop Shr tx ty x y)
            (in custom p4expr at level 5,
                x custom p4expr, tx custom p4type,
                y custom p4expr, ty custom p4type, left associativity).
      Notation "'<=' x '::' tx y '::' ty 'end'"
        := (EBop Le tx ty x y)
            (in custom p4expr at level 12,
                x custom p4expr, tx custom p4type,
                y custom p4expr, ty custom p4type, no associativity).
      Notation "'>=' x '::' tx y '::' ty 'end'"
        := (EBop Ge tx ty x y)
            (in custom p4expr at level 12,
                x custom p4expr, tx custom p4type,
                y custom p4expr, ty custom p4type, no associativity).
      Notation "'<' x '::' tx y '::' ty 'end'"
        := (EBop Lt tx ty x y)
            (in custom p4expr at level 12,
                x custom p4expr, tx custom p4type,
                y custom p4expr, ty custom p4type, no associativity).
      Notation "'>' x '::' tx y '::' ty 'end'"
        := (EBop Gt tx ty x y)
            (in custom p4expr at level 12,
                x custom p4expr, tx custom p4type,
                y custom p4expr, ty custom p4type, no associativity).
      Notation "'==' x '::' tx y '::' ty 'end'"
        := (EBop Eq tx ty x y)
            (in custom p4expr at level 12,
                x custom p4expr, tx custom p4type,
                y custom p4expr, ty custom p4type, no associativity).
      Notation "'!=' x '::' tx y '::' ty 'end'"
        := (EBop NotEq tx ty x y)
            (in custom p4expr at level 12,
                x custom p4expr, tx custom p4type,
                y custom p4expr, ty custom p4type, no associativity).
      Notation "'&' x '::' tx y '::' ty 'end'"
        := (EBop BitAnd tx ty x y)
            (in custom p4expr at level 7,
                x custom p4expr, tx custom p4type,
                y custom p4expr, ty custom p4type, left associativity).
      Notation "'^' x '::' tx y '::' ty 'end'"
        := (EBop BitXor tx ty x y)
            (in custom p4expr at level 8,
                x custom p4expr, tx custom p4type,
                y custom p4expr, ty custom p4type, left associativity).
      Notation "'|' x '::' tx y '::' ty 'end'"
        := (EBop BitOr tx ty x y)
            (in custom p4expr at level 9,
                x custom p4expr, tx custom p4type,
                y custom p4expr, ty custom p4type, left associativity).
      Notation "'&&' x '::' tx y '::' ty 'end'"
        := (EBop And tx ty x y)
            (in custom p4expr at level 14,
                x custom p4expr, tx custom p4type,
                y custom p4expr, ty custom p4type, no associativity).
      Notation "'||' x '::' tx y '::' ty 'end'"
        := (EBop Or tx ty x y)
            (in custom p4expr at level 15,
                x custom p4expr, tx custom p4type,
                y custom p4expr, ty custom p4type, no associativity).
      Notation "'++' x '::' tx y '::' ty 'end'"
        := (EBop PlusPlus tx ty x y)
            (in custom p4expr at level 6,
                x custom p4expr, tx custom p4type,
                y custom p4expr, ty custom p4type, left associativity).
      Notation "'(' ty ')' x '::' tx 'end'"
        := (ECast ty tx x)
            (in custom p4expr at level 16,
                x custom p4expr, ty custom p4type,
                tx custom p4type, no associativity).
      (*  Notation "'rec' { fx ';;' fy ';;' .. ';;' fz }"
              := (ERecord  (cons fx (cons fy .. (cons fz nil) ..)))
                          (in custom p4expr at level 6, no associativity). *)
      Notation "'rec' { fields } "
        := (ERecord fields)
            (in custom p4expr at level 6, no associativity).
      Notation "'Mem' x '::' ty 'dot' y 'end'"
              := (EExprMember y ty x)
                    (in custom p4expr at level 10, x custom p4expr,
                        ty custom p4type, left associativity).
      Notation "'Error' x" := (EError x)
                              (in custom p4expr at level 0, no associativity).
      Notation "'Matchkind' x" := (EMatchKind x)
                              (in custom p4expr at level 0, no associativity).
      (* Notation " 'call' f '::' tf 'with' args 'end' "
        := (ECall tf f args) (in custom p4expr at level 30,
                                tf custom p4type,
                                f custom p4expr, left associativity). *)
    End ExprNotations.
    Import ExprNotations.

    (** A custom induction principle for [e]. *)
    Section ExprInduction.
      (** An arbitrary predicate. *)
      Variable P : e -> Prop.

      Hypothesis HEBool : forall b : bool,
          P <{ BOOL b }>.

      Hypothesis HEInteger : forall n : INT.t,
          P <{ Int n }>.

      Hypothesis HEBitstring : forall (w : INT.t) (v : BIGINT.t),
          P <{ w @ v }>.

      Hypothesis HEVar : forall (ty : t) (x : NAME.t),
          P (EVar ty x).

      Hypothesis HEUop : forall (op : uop) (ty : t) (ex : e),
          P ex -> P (EUop op ty ex).

      Hypothesis HEBop : forall (op : bop) (lt rt : t) (lhs rhs : e),
          P lhs -> P rhs -> P (EBop op lt rt lhs rhs).

      Hypothesis HECast : forall (ct et : t) (ex : e),
          P ex -> P <{ (ct) ex :: et end }>.

      Hypothesis HERecord : forall (fields : F.fs (t * e)),
          F.predfs_data (P ∘ snd) fields -> P <{ rec {fields} }>.

      Hypothesis HEExprMember : forall (x : NAME.t) (ty : t) (ex : e),
          P ex -> P <{ Mem ex :: ty dot x end }>.

      Hypothesis HEError : forall err : NAME.t,
          P <{ Error err }>.

      Hypothesis HEMatchKind : forall mkd : NAME.t,
          P <{ Matchkind mkd }>.

      (* Hypothesis HECall : forall (ty : t) (callee : e) (args : F.fs (d * t * e)),
          P callee -> F.predfs_data (P ∘ snd) args ->
          P <{ call callee :: ty with args end }>. *)

      (* Hypothesis HELoc : forall l : LOC.t,
          P (ELoc l). *)

      (** A custom induction principle.
          Do [induction ?e using custom_e_ind]. *)
      Definition custom_e_ind : forall exp : e, P exp :=
        fix custom_e_ind (expr : e) : P expr :=
          let fix fields_ind {A:Type} (flds : F.fs (A * e))
              : F.predfs_data (P ∘ snd) flds :=
              match flds as fs_ex
                    return F.predfs_data (P ∘ snd) fs_ex with
              | [] => Forall_nil (F.predf_data (P ∘ snd))
              | (_, (_, hfe)) as hf :: tf =>
                Forall_cons hf (custom_e_ind hfe) (fields_ind tf)
              end in
          match expr as e' return P e' with
          | <{ BOOL b }> => HEBool b
          | <{ Int n }> => HEInteger n
          | <{ w @ v }> => HEBitstring w v
          | <{ Var x :: ty end }> => HEVar ty x
          | EUop ty op exp => HEUop ty op exp (custom_e_ind exp)
          | EBop op lt rt lhs rhs =>
              HEBop op lt rt lhs rhs
                    (custom_e_ind lhs) (custom_e_ind rhs)
          | <{ (ct) exp :: et end }> => HECast ct et exp (custom_e_ind exp)
          | <{ rec { fields } }> => HERecord fields (fields_ind fields)
          | <{ Mem exp :: ty dot x end }> =>
              HEExprMember x ty exp (custom_e_ind exp)
          | <{ Error err }> => HEError err
          | <{ Matchkind mkd }> => HEMatchKind mkd
          (* | <{ call callee :: ty with args end }> =>
              HECall ty callee args
                    (custom_e_ind callee)
                    (fields_ind args) *)
          (* | <{ Loc l }> => HELoc l *)
          end.
    End ExprInduction.
  End Expr.

  (** * Statement Grammar *)
  Module Stmt.
    Import Dir.
    Module E := Expr.

    Inductive s : Type :=
      (* Skip is useful for small-step semantics. *)
      | SSkip
      | SAssign (type : E.t) (lhs rhs : E.e)
      | SConditional (guard_type : E.t)
                    (guard : E.e) (tru_blk fls_blk : s)
      (* Sequences, a possibly easier-to-verify alternative to blocks. *)
      | SSeq (s1 s2 : s)
      | SVarDecl (typ : E.t) (var : NAME.t) (rhs : E.e)
      | SCall (f : NAME.t) (args : E.arrowE).
    (**[]*)

    Module StmtNotations.
      Export E.ExprNotations.

      Declare Custom Entry p4stmt.

      Notation "$ stmt $" := stmt (stmt custom p4stmt at level 99).
      Notation "( x )" := x (in custom p4stmt, x at level 99).
      Notation "x"
        := x (in custom p4stmt at level 0, x constr at level 0).
      Notation "'skip'" := SSkip (in custom p4stmt at level 0).
      Notation "s1 ; s2"
        := (SSeq s1 s2) (in custom p4stmt at level 99,
                            s1 custom p4stmt, s2 custom p4stmt,
                            right associativity).

      Notation "'asgn' e1 ':=' e2 :: t 'fin'"
              := (SAssign t e1 e2)
                    (in custom p4stmt at level 40,
                        e1 custom p4expr, e2 custom p4expr,
                        t custom p4type, no associativity).

      Notation "'decl' x ≜ e :: t 'fin'"
              := (SVarDecl t x e)
                    (in custom p4stmt at level 40,
                        e custom p4expr, t custom p4type,
                        no associativity).

      Notation "'if' e :: t 'then' s1 'else' s2 'fin'"
              := (SConditional t e s1 s2)
                    (in custom p4stmt at level 80,
                        t custom p4type, e custom p4expr,
                        s1 custom p4stmt, s2 custom p4stmt,
                        no associativity).

      Notation "'call' f 'with' args 'fin'"
        := (SCall f (E.Arrow (E.t * NAME.t) args None))
             (in custom p4stmt at level 30, no associativity).

      Notation "'let' e '::' t ':=' 'call' f 'with' args 'fin'"
               := (SCall f (E.Arrow (E.t * NAME.t) args (Some (t,e))))
                    (in custom p4stmt at level 30,
                        e custom p4expr, t custom p4stmt, no associativity).
    End StmtNotations.
  End Stmt.

  (** * Declaration Grammar *)
  Module Decl.
    Module E := Expr.
    Module S := Stmt.

    (** Here is the subset of declarations that
        may occur within controls, parsers,
        and even the top-level. *)
    Inductive d : Type :=
      | DVardecl (typ : E.t) (x : NAME.t)
      | DVarinit (typ : E.t) (x : NAME.t) (rhs : E.e)
      | DConst   (typ : E.t) (x : NAME.t) (rhs : E.e)
      (** [C] is the constructor name,
          and [x] is the instance name. *)
      | DInstantiate (C x : NAME.t) (args : F.fs (E.t * E.e))
      | DFunction (f : NAME.t) (signature : E.arrowT) (body : S.s)
      | DSeq (d1 d2 : d).
    (**[]*)
  End Decl.

  (** * Controls *)
  Module Control.
    Module E := Expr.
    Module S := Stmt.
    Module D := Decl.

    (** Declarations that may occur within Controls. *)
    (* TODO, this is a stub. *)
    Inductive d : Type :=
      | DTable (* TODO! *)
      | DDecl (d : D.d)
      | DSeq (d1 d2 : d).
    (**[]*)
  End Control.

  (** * Top-Level Declarations *)
  Module TopDecl.
    Module E := Expr.
    Module S := Stmt.
    Module D := Decl.
    Module C := Control.

    (** Top-level declarations. *)
    (* TODO, this is a stub. *)
    Inductive d : Type :=
      | TPDecl (d : D.d)
      | TPControl (cparams : F.fs E.t) (params : F.fs (Dir.d * E.t))
                  (body : C.d) (apply_blk : S.s)
      | TPParser (cparams : F.fs E.t) (params : F.fs (Dir.d * E.t)) (* TODO! *)
      | TPSeq (d1 d2 : d).
    (**[]*)
  End TopDecl.
End P4.
