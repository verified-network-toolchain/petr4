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

(** * Info *)
Module Type P4Info.
  (* TODO! line/column number, lexical info *)
  Parameter t : Type.
End P4Info.

(** * Qualified Names *)
Module P4Name (STRING : P4Data) <: P4Data.
  Module S := STRING.

  (** Names, qualified or otherwise. *)
  Inductive t' : Type :=
    | Bare (x : S.t)                       (* bare/unqualified names *)
    | Qualified (name_space : S.t) (x : t') (* qualified names *).

  Definition t := t'.

  (** Get just the name. *)
  Fixpoint get_name (n : t) : S.t :=
    match n with
    | Bare x        => x
    | Qualified _ n => get_name n
    end.

  Fixpoint eqb (n1 n2 : t) : bool :=
    match n1, n2 with
    | Bare x1, Bare x2                   => S.eqb x1 x2
    | Qualified ns1 n1, Qualified ns2 n2 => S.eqb ns1 ns2 && eqb n1 n2
    | _, _                               => false
    end.

  Lemma eqb_reflect : forall x y : t, CBB.reflect (x = y) (eqb x y).
  Proof.
    induction x as [x | nsx x IHx]; intros [y | nsy y]; simpl in *.
    - pose proof S.eqb_reflect x y as H.
      inversion H as [HEq Hxy | HNEq Hxy]; subst.
      + left. reflexivity.
      + right. intros H'.
        inversion H'; subst. contradiction.
    - right. intros H. inversion H.
    - right. intros H. inversion H.
    - pose proof S.eqb_reflect nsx nsy as H.
      specialize IHx with y.
      inversion H as [HEq Hxy | HNEq Hxy]; subst; simpl;
        inversion IHx as [IH IHxy | IH IHxy]; subst;
          try (right; intros H'; inversion H'; contradiction).
      left. reflexivity.
  Qed.
End P4Name.

(** * P4Light AST *)
Module P4Light (STRING : P4Data) (INT BIGINT : P4Numeric) (I : P4Info).
  Module F := Field STRING.
  Module N := P4Name STRING.

  (** Directions. *)
  Module Dir.
    Inductive d : Set :=
      | DIn    (* in *)
      | DOut   (* out *)
      | DInOut (* inout *)
      | DZilch (* no direction *).
    (**[]*)
  End Dir.

  (** * Expression Grammar *)
  Module Expr.
    Import Dir.

    (** Expression types. *)
    Inductive t : Type :=
      | TBool                     (* bool *)
      | TInteger                  (* arbitrary-size integers *)
      | TBitstring (n : INT.t)    (* fixed-width integers *)
      | TError                    (* the error type *)
      | TMatchKind                (* the matchkind type *)
      | TRecord (fields : F.fs t) (* the record and struct type *)
      | THeader (fields : F.fs t) (* the header type *).
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
      Notation "'rec' { fields }"
        := (TRecord fields)
            (in custom p4type at level 6, no associativity).
      Notation "'hdr' { fields }"
        := (THeader fields)
            (in custom p4type at level 6, no associativity).
    End TypeNotations.
    Import TypeNotations.

    (** Custom induction principle for [t]. *)
    Section TypeInduction.
      (** An arbitrary property. *)
      Variable P : t -> Prop.

      Hypothesis HTBool : P {{ Bool }}.

      Hypothesis HTInteger : P {{ int }}.

      Hypothesis HTBitstring : forall w, P {{ bit<w> }}.

      Hypothesis HTError : P {{ error }}.

      Hypothesis HTMatchKind : P {{ matchkind }}.

      Hypothesis HTRecord : forall fields,
          F.predfs_data P fields -> P {{ rec { fields } }}.

      Hypothesis HTHeader : forall fields,
          F.predfs_data P fields -> P {{ hdr { fields } }}.

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
          | {{ rec { fields } }} => HTRecord fields (fields_ind fields)
          | {{ hdr { fields } }} => HTHeader fields (fields_ind fields)
          end.
    End TypeInduction.

    Inductive uop : Set :=
      | Not    (* boolean negation *)
      | BitNot (* bitwise negation *)
      | UMinus (* integer negation *).

    (** Binary operations.
        The "Sat" suffix denotes
        saturating arithmetic:
        where there is no overflow. *)
    Inductive bop : Set :=
      | Plus     (* integer addition *)
      | PlusSat  (* saturating addition *)
      | Minus    (* integer subtraction *)
      | MinusSat (* saturating subtraction *)
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

    (** Expressions annotated with types,
      unless the type is obvious. *)
    Inductive e : Type :=
      | EBool (b : bool) (i : I.t) (* booleans *)
      | EInteger (n : INT.t) (i : I.t) (* arbitrary-size integers *)
      | EBitstring (width : INT.t) (value : BIGINT.t)
                   (i : I.t) (* fixed-width integers *)
      | EVar (type : t) (x : N.t) (i : I.t) (* variables *)
      | EUop (op : uop) (type : t)
             (arg : e) (i : I.t) (* unary operations *)
      | EBop (op : bop) (lhs_type rhs_type : t)
             (lhs rhs : e) (i : I.t) (* binary operations *)
      | ECast (cast_type : t) (expr_type : t)
              (arg : e) (i : I.t) (* explicit casts *)
      | ERecord (fields : F.fs (t * e))
                (i : I.t) (* records and structs *)
      | EExprMember (mem : STRING.t) (expr_type : t)
                    (arg : e) (i : I.t)      (* member-expressions *)
      | EError (name : STRING.t) (i : I.t)     (* error literals *)
      | EMatchKind (name : STRING.t) (i : I.t) (* matchkind literals *).
    (**[]*)

    (** Function call. *)
    Definition arrowE : Type := arrow (t * e) (t * N.t).

    Module ExprNotations.
      Declare Custom Entry p4expr.

      Notation "'<{' exp '}>'" := exp (exp custom p4expr at level 99).
      Notation "( x )" := x (in custom p4expr, x at level 99).
      Notation "x" := x (in custom p4expr at level 0, x constr at level 0).
      Notation "'True' @ i" := (EBool true i) (in custom p4expr at level 0).
      Notation "'False' @ i" := (EBool false i) (in custom p4expr at level 0).
      Notation "'BOOL' b @ i" := (EBool b i) (in custom p4expr at level 0).
      Notation "'Int' n @ i" := (EInteger n i) (in custom p4expr at level 0).
      Notation "'Bit' '<' w '>' n @ i" := (EBitstring w n i)
                              (in custom p4expr at level 1, no associativity).
      Notation "'Var' x '::' ty @ i 'end'" := (EVar ty x i)
                            (in custom p4expr at level 0, no associativity).
      Notation "'!' x '::' ty @ i 'end'" := (EUop Not ty x i)
                                  (in custom p4expr at level 2,
                                      x custom p4expr, ty custom p4type,
                                      no associativity).
      Notation "'~' x '::' ty @ i 'end'" := (EUop BitNot ty x i)
                                  (in custom p4expr at level 2,
                                      x custom p4expr, ty custom p4type,
                                      no associativity).
      Notation "'-' x '::' ty @ i 'end'" := (EUop UMinus ty x i)
                                  (in custom p4expr at level 2,
                                      x custom p4expr, ty custom p4type,
                                      no associativity).
      Notation "'+' x '::' tx y '::' ty @ i 'end'"
        := (EBop Plus tx ty x y i)
            (in custom p4expr at level 3,
                x custom p4expr, tx custom p4type,
                y custom p4expr, ty custom p4type, left associativity).
      Notation "'|+|' x '::' tx y '::' ty @ i 'end'"
        := (EBop PlusSat tx ty x y i)
            (in custom p4expr at level 4,
                x custom p4expr, tx custom p4type,
                y custom p4expr, ty custom p4type, left associativity).
      Notation "'--' x '::' tx y '::' ty @ i 'end'"
        := (EBop Minus tx ty x y i)
            (in custom p4expr at level 3,
                x custom p4expr, tx custom p4type,
                y custom p4expr, ty custom p4type, left associativity).
      Notation "'|-|' x '::' tx y '::' ty @ i 'end'"
        := (EBop MinusSat tx ty x y i)
            (in custom p4expr at level 4,
                x custom p4expr, tx custom p4type,
                y custom p4expr, ty custom p4type, left associativity).
      Notation "'<<' x '::' tx y '::' ty @ i 'end'"
        := (EBop Shl tx ty x y i)
            (in custom p4expr at level 5,
                x custom p4expr, tx custom p4type,
                y custom p4expr, ty custom p4type, left associativity).
      Notation "'>>' x '::' tx y '::' ty @ i 'end'"
        := (EBop Shr tx ty x y i)
            (in custom p4expr at level 5,
                x custom p4expr, tx custom p4type,
                y custom p4expr, ty custom p4type, left associativity).
      Notation "'<=' x '::' tx y '::' ty @ i 'end'"
        := (EBop Le tx ty x y i)
            (in custom p4expr at level 12,
                x custom p4expr, tx custom p4type,
                y custom p4expr, ty custom p4type, no associativity).
      Notation "'>=' x '::' tx y '::' ty @ i 'end'"
        := (EBop Ge tx ty x y i)
            (in custom p4expr at level 12,
                x custom p4expr, tx custom p4type,
                y custom p4expr, ty custom p4type, no associativity).
      Notation "'<' x '::' tx y '::' ty @ i 'end'"
        := (EBop Lt tx ty x y i)
            (in custom p4expr at level 12,
                x custom p4expr, tx custom p4type,
                y custom p4expr, ty custom p4type, no associativity).
      Notation "'>' x '::' tx y '::' ty @ i 'end'"
        := (EBop Gt tx ty x y i)
            (in custom p4expr at level 12,
                x custom p4expr, tx custom p4type,
                y custom p4expr, ty custom p4type, no associativity).
      Notation "'==' x '::' tx y '::' ty @ i 'end'"
        := (EBop Eq tx ty x y i)
            (in custom p4expr at level 12,
                x custom p4expr, tx custom p4type,
                y custom p4expr, ty custom p4type, no associativity).
      Notation "'!=' x '::' tx y '::' ty @ i 'end'"
        := (EBop NotEq tx ty x y i)
            (in custom p4expr at level 12,
                x custom p4expr, tx custom p4type,
                y custom p4expr, ty custom p4type, no associativity).
      Notation "'&' x '::' tx y '::' ty @ i 'end'"
        := (EBop BitAnd tx ty x y i)
            (in custom p4expr at level 7,
                x custom p4expr, tx custom p4type,
                y custom p4expr, ty custom p4type, left associativity).
      Notation "'^' x '::' tx y '::' ty @ i 'end'"
        := (EBop BitXor tx ty x y i)
            (in custom p4expr at level 8,
                x custom p4expr, tx custom p4type,
                y custom p4expr, ty custom p4type, left associativity).
      Notation "'|' x '::' tx y '::' ty @ i 'end'"
        := (EBop BitOr tx ty x y i)
            (in custom p4expr at level 9,
                x custom p4expr, tx custom p4type,
                y custom p4expr, ty custom p4type, left associativity).
      Notation "'&&' x '::' tx y '::' ty @ i 'end'"
        := (EBop And tx ty x y i)
            (in custom p4expr at level 14,
                x custom p4expr, tx custom p4type,
                y custom p4expr, ty custom p4type, no associativity).
      Notation "'||' x '::' tx y '::' ty @ i 'end'"
        := (EBop Or tx ty x y i)
            (in custom p4expr at level 15,
                x custom p4expr, tx custom p4type,
                y custom p4expr, ty custom p4type, no associativity).
      Notation "'++' x '::' tx y '::' ty @ i 'end'"
        := (EBop PlusPlus tx ty x y i)
            (in custom p4expr at level 6,
                x custom p4expr, tx custom p4type,
                y custom p4expr, ty custom p4type, left associativity).
      Notation "'(' ty ')' x '::' tx @ i 'end'"
        := (ECast ty tx x i)
            (in custom p4expr at level 16,
                x custom p4expr, ty custom p4type,
                tx custom p4type, no associativity).
      Notation "'rec' { fields } @ i "
        := (ERecord fields i)
            (in custom p4expr at level 6, no associativity).
      Notation "'Mem' x '::' ty 'dot' y @ i 'end'"
              := (EExprMember y ty x i)
                    (in custom p4expr at level 10, x custom p4expr,
                        ty custom p4type, left associativity).
      Notation "'Error' x @ i" := (EError x i)
                              (in custom p4expr at level 0, no associativity).
      Notation "'Matchkind' x @ i" := (EMatchKind x i)
                              (in custom p4expr at level 0, no associativity).
    End ExprNotations.
    Import ExprNotations.

    (** A custom induction principle for [e]. *)
    Section ExprInduction.
      (** An arbitrary predicate. *)
      Variable P : e -> Prop.

      Hypothesis HEBool : forall b i,
          P <{ BOOL b @ i }>.

      Hypothesis HEInteger : forall n i,
          P <{ Int n @ i }>.

      Hypothesis HEBitstring : forall (w : INT.t) (v : BIGINT.t) i,
          P <{ Bit<w> v @ i }>.

      Hypothesis HEVar : forall (ty : t) (x : N.t) i,
          P <{ Var x :: ty @ i end }>.

      Hypothesis HEUop : forall (op : uop) (ty : t) (ex : e) i,
          P ex -> P (EUop op ty ex i).

      Hypothesis HEBop : forall (op : bop) (lt rt : t) (lhs rhs : e) i,
          P lhs -> P rhs -> P (EBop op lt rt lhs rhs i).

      Hypothesis HECast : forall (ct et : t) (ex : e) i,
          P ex -> P <{ (ct) ex :: et @ i end }>.

      Hypothesis HERecord : forall (fields : F.fs (t * e)) i,
          F.predfs_data (P ∘ snd) fields -> P <{ rec {fields} @ i }>.

      Hypothesis HEExprMember : forall (x : STRING.t) (ty : t) (ex : e) i,
          P ex -> P <{ Mem ex :: ty dot x @ i end }>.

      Hypothesis HEError : forall err i,
          P <{ Error err @ i }>.

      Hypothesis HEMatchKind : forall mkd i,
          P <{ Matchkind mkd @ i }>.

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
          | <{ BOOL b @ i }> => HEBool b i
          | <{ Int n @ i }> => HEInteger n i
          | <{ Bit<w> v @ i }> => HEBitstring w v i
          | <{ Var x :: ty @ i end }> => HEVar ty x i
          | EUop ty op exp i => HEUop ty op exp i (custom_e_ind exp)
          | EBop op lt rt lhs rhs i =>
              HEBop op lt rt lhs rhs i
                    (custom_e_ind lhs) (custom_e_ind rhs)
          | <{ (ct) exp :: et @ i end }> => HECast ct et exp i (custom_e_ind exp)
          | <{ rec { fields } @ i }> => HERecord fields i (fields_ind fields)
          | <{ Mem exp :: ty dot x @ i end }> =>
              HEExprMember x ty exp i (custom_e_ind exp)
          | <{ Error err @ i }> => HEError err i
          | <{ Matchkind mkd @ i }> => HEMatchKind mkd i
          end.
    End ExprInduction.
  End Expr.

  (** * Statement Grammar *)
  Module Stmt.
    Import Dir.
    Module E := Expr.

    Inductive s : Type :=
      | SSkip (i : I.t) (* skip, useful for small-step semantics *)
      | SAssign (type : E.t) (lhs rhs : E.e)
                (i : I.t) (* assignment *)
      | SConditional (guard_type : E.t) (guard : E.e)
                     (tru_blk fls_blk : s) (i : I.t) (* conditionals *)
      | SSeq (s1 s2 : s)
             (i : I.t) (* sequences, an alternative to blocks *)
      | SVarDecl (typ : E.t) (var : N.t)
                 (rhs : E.e) (i : I.t) (* variable declaration *)
      | SCall (f : N.t) (args : E.arrowE)
              (i : I.t) (* function/action/extern call *)
      | SReturnVoid (i : I.t) (* void return statement *)
      | SReturnFruit (t : E.t) (e : E.e)
                     (i : I.t) (* fruitful return statement *).
    (**[]*)

    Module StmtNotations.
      Import E.TypeNotations.
      Import E.ExprNotations.

      Declare Custom Entry p4stmt.

      Notation "$ stmt $" := stmt (stmt custom p4stmt at level 99).
      Notation "( x )" := x (in custom p4stmt, x at level 99).
      Notation "x"
        := x (in custom p4stmt at level 0, x constr at level 0).
      Notation "'skip' @ i" := (SSkip i) (in custom p4stmt at level 0).
      Notation "s1 ; s2 @ i"
        := (SSeq s1 s2 i) (in custom p4stmt at level 99,
                            s1 custom p4stmt, s2 custom p4stmt,
                            right associativity).
      Notation "'asgn' e1 ':=' e2 :: t @ i 'fin'"
              := (SAssign t e1 e2 i)
                    (in custom p4stmt at level 40,
                        e1 custom p4expr, e2 custom p4expr,
                        t custom p4type, no associativity).
      Notation "'decl' x ≜ e :: t @ i 'fin'"
              := (SVarDecl t x e i)
                    (in custom p4stmt at level 40,
                        e custom p4expr, t custom p4type,
                        no associativity).
      Notation "'if' e :: t 'then' s1 'else' s2 @ i 'fin'"
              := (SConditional t e s1 s2 i)
                    (in custom p4stmt at level 80,
                        t custom p4type, e custom p4expr,
                        s1 custom p4stmt, s2 custom p4stmt,
                        no associativity).
      Notation "'call' f 'with' args @ i 'fin'"
        := (SCall f (E.Arrow (E.t * N.t) args None) i)
             (in custom p4stmt at level 30, no associativity).
      Notation "'let' e '::' t ':=' 'call' f 'with' args @ i 'fin'"
               := (SCall f (E.Arrow (E.t * N.t) args (Some (t,e))) i)
                    (in custom p4stmt at level 30,
                        e custom p4expr, t custom p4stmt, no associativity).
      Notation "'return' e '::' t @ i 'fin'"
               := (SReturnFruit t e i)
                    (in custom p4stmt at level 30,
                        e custom p4expr, t custom p4type, no associativity).
      Notation "'returns' @ i"
               := (SReturnVoid i)
                    (in custom p4stmt at level 0, no associativity).
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
      | DVardecl (typ : E.t) (x : N.t) (i : I.t)             (* unitialized variable *)
      | DVarinit (typ : E.t) (x : N.t) (rhs : E.e) (i : I.t) (* initialized variable *)
      | DConst   (typ : E.t) (x : N.t) (rhs : E.e) (i : I.t) (* constant *)
      | DInstantiate (C x : N.t) (args : F.fs (E.t * E.e))
                     (i : I.t) (* constructor [C] with [args] makes [x] *)
      | DFunction (f : N.t) (signature : E.arrowT)
                  (body : S.s) (i : I.t) (* function/method declaration *)
      | DSeq (d1 d2 : d) (i : I.t)       (* sequence of declarations *).
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
      | DTable (i : I.t) (* TODO! *)
      | DDecl (d : D.d) (i : I.t)
      | DSeq (d1 d2 : d) (i : I.t).
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
      | TPDecl (d : D.d) (i : I.t)
      | TPControl (cparams : F.fs E.t)
                  (params : F.fs (Dir.d * E.t))
                  (body : C.d) (apply_blk : S.s) (i : I.t)
      | TPParser (cparams : F.fs E.t)
                 (params : F.fs (Dir.d * E.t)) (i : I.t) (* TODO! *)
      | TPSeq (d1 d2 : d) (i : I.t).
    (**[]*)
  End TopDecl.
End P4Light.
