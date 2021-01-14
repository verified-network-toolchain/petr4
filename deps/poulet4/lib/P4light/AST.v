Require Export Coq.Lists.List.
Export ListNotations.
Require Export Coq.Bool.Bool.
Require Export Coq.Classes.EquivDec.
Require Export Coq.Numbers.BinNums. (** Big Integers. *)
Require Petr4.String. (** Strings. *)
Require Petr4.P4String. (** Names. *)
Require Petr4.P4Int. (** Integers. *)

Definition string : Type := Petr4.String.t.
Instance StringEqDec : EqDec string eq := Petr4.String.StringEqDec.

Section TypeSynonyms.
  Variable (tags_t : Type).

  Definition name : Type := Petr4.P4String.t tags_t.

  Instance P4StringEqDec : EqDec name (@P4String.equiv tags_t) :=
    P4String.P4StringEqDec tags_t.
  (**[]*)

  Definition int : Type := Petr4.P4Int.t tags_t.

  Instance P4IntEquivalence : Equivalence (@P4Int.equiv tags_t) :=
    P4Int.IntEquivalence tags_t.
  (**[]*)

  Instance P4IntEqDec : EqDec int (P4Int.equiv) :=
    P4Int.IntEqDec tags_t.
  (**[]*)
End TypeSynonyms.

Definition pipeline {A B : Type} (x : A) (f : A -> B) : B := f x.

Infix "▷" := pipeline (at level 45, left associativity).

Infix "∘" := Basics.compose (at level 40, left associativity).

(** * Definitions and Lemmas regarding Fields *)
Module Field.
  Section FieldTypes.
    Variable (tags_t : Type).

    (** Field type. *)
    Definition f (T : Type) : Type := (name tags_t) * T.

    (** Fields. *)
    Definition fs (T : Type) : Type := list (f T).
  End FieldTypes.

  Section FieldLibrary.
    Context {tags_t : Type}.

    (** Predicate on a field's data. *)
    Definition predf_data {T : Type} (P : T -> Prop) : f tags_t T -> Prop :=
      fun '(_, t) => P t.
    (**[]*)

    (** Predicate over every data in fields. *)
    Definition predfs_data {T : Type} (P : T -> Prop) : fs tags_t T -> Prop :=
      Forall (predf_data P).
    (**[]*)

    (** Relation betwixt two field instances. *)
    Definition relf {U V : Type} (R : U -> V -> Prop) : f tags_t U -> f tags_t V -> Prop :=
      fun u v => fst u = fst v /\ R (snd u) (snd v).
    (**[]*)

    (** Relation between two instances of fields. *)
    Definition relfs {U V : Type}
               (R : U -> V -> Prop) : fs tags_t U -> fs tags_t V -> Prop :=
      Forall2 (relf R).
    (**[]*)

    (** Filter. *)
    Definition filter {U : Type} (f : U -> bool) : fs tags_t U -> fs tags_t U :=
      List.filter (f ∘ snd).
    (**[]*)

    (** Map. *)
    Definition map {U V : Type} (f : U -> V) : fs tags_t U -> fs tags_t V :=
      List.map (fun '(x,u) => (x, f u)).
    (**[]*)

    (** Fold. *)
    Definition fold {U V : Type}
               (f : name tags_t -> U -> V -> V) (fds : fs tags_t U) (init : V) : V :=
      List.fold_right (fun '(x,u) acc => f x u acc) init fds.
    (**[]*)
  End FieldLibrary.
End Field.

(** * P4light AST *)
Module P4light.
  Module F := Field.

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

    Section P4Types.
      Variable (tags_t : Type).

      (** Expression types. *)
      Inductive t : Type :=
      | TBool                            (* bool *)
      | TInteger                         (* arbitrary-size integers *)
      | TBitstring (n : nat)               (* fixed-width integers *)
      | TError                           (* the error type *)
      | TMatchKind                       (* the matchkind type *)
      | TRecord (fields : F.fs tags_t t) (* the record and struct type *)
      | THeader (fields : F.fs tags_t t) (* the header type *).
      (**[]*)

      (** Function signatures. *)
      Inductive arrow (A R : Type) : Type :=
        Arrow (params : F.fs tags_t (Dir.d * A)) (returns : option R).
      (**[]*)

      (** Function types. *)
      Definition arrowT : Type := arrow t t.
    End P4Types.

    Arguments TBool {_}.
    Arguments TInteger {_}.
    Arguments TBitstring {_}.
    Arguments TError {_}.
    Arguments TMatchKind {_}.
    Arguments TRecord {_}.
    Arguments THeader {_}.
    Arguments Arrow {_} {_} {_}.

    Module TypeNotations.
      Declare Custom Entry p4type.

      Notation "'{{' ty '}}'" := ty (ty custom p4type at level 99).
      Notation "( x )" := x (in custom p4type, x at level 99).
      Notation "x" := x (in custom p4type at level 0, x constr at level 0).
      Notation "'Bool'" := TBool (in custom p4type at level 0).
      Notation "'Int'"
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
      Context {tags_t : Type}.

      (** An arbitrary property. *)
      Variable P : t tags_t -> Prop.

      Hypothesis HTBool : P {{ Bool }}.

      Hypothesis HTInteger : P {{ Int }}.

      Hypothesis HTBitstring : forall w, P {{ bit<w> }}.

      Hypothesis HTError : P {{ error }}.

      Hypothesis HTMatchKind : P {{ matchkind }}.

      Hypothesis HTRecord : forall fields,
          F.predfs_data P fields -> P {{ rec { fields } }}.

      Hypothesis HTHeader : forall fields,
          F.predfs_data P fields -> P {{ hdr { fields } }}.

      (** A custom induction principle.
          Do [induction ?t using custom_t_ind]. *)
      Definition custom_t_ind : forall ty : t tags_t, P ty :=
        fix custom_t_ind (type : t tags_t) : P type :=
          let fix fields_ind (flds : F.fs tags_t (t tags_t)) : F.predfs_data P flds :=
              match flds as fs_ty return F.predfs_data P fs_ty with
              | [] => Forall_nil (F.predf_data P)
              | (_, hft) as hf :: tf =>
                Forall_cons hf (custom_t_ind hft) (fields_ind tf)
              end in
          let fix fields_ind_dir
                  (flds : F.fs tags_t (d * t tags_t)) : F.predfs_data (P ∘ snd) flds :=
              match flds as fs_ty return F.predfs_data (P ∘ snd) fs_ty with
              | [] => Forall_nil (F.predf_data (P ∘ snd))
              | (_, (_, hft)) as hf :: tf =>
                Forall_cons hf (custom_t_ind hft) (fields_ind_dir tf)
              end in
          match type as ty return P ty with
          | {{ Bool }} => HTBool
          | {{ Int }} => HTInteger
          | {{ bit<w> }} => HTBitstring w
          | {{ error }} => HTError
          | {{ matchkind }} => HTMatchKind
          | {{ rec { fields } }} => HTRecord fields (fields_ind fields)
          | {{ hdr { fields } }} => HTHeader fields (fields_ind fields)
          end.
      (**[]*)
    End TypeInduction.

    Inductive uop : Set :=
    | Not    (* boolean negation *)
    | BitNot (* bitwise negation *)
    | UMinus (* integer negation *).
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

    Section Expressions.
      Variable (tags_t : Type).

      (** Expressions annotated with types,
          unless the type is obvious. *)
      Inductive e : Type :=
      | EBool (b : bool) (i : tags_t)                      (* booleans *)
      | EInteger (n : int tags_t) (i : tags_t)          (* arbitrary-size integers *)
      | EBitstring (width : nat) (value : N) (i : tags_t) (* fixed-width integers *)
      | EVar (type : t tags_t) (x : name tags_t)
             (i : tags_t)                               (* variables *)
      | EUop (op : uop) (type : t tags_t)
             (arg : e) (i : tags_t)                     (* unary operations *)
      | EBop (op : bop) (lhs_type rhs_type : t tags_t)
             (lhs rhs : e) (i : tags_t)                 (* binary operations *)
      | ECast (cast_type : t tags_t)
              (expr_type : t tags_t)
              (arg : e) (i : tags_t)                   (* explicit casts *)
      | ERecord (fields : F.fs tags_t (t tags_t * e))
                (i : tags_t)                           (* records and structs *)
      | EExprMember (mem : name tags_t)
                    (expr_type : t tags_t)
                    (arg : e) (i : tags_t)             (* member-expressions *)
      | EError (err : name tags_t) (i : tags_t)        (* error literals *)
      | EMatchKind (err : name tags_t) (i : tags_t)    (* matchkind literals *).
      (**[]*)

      (** Function call. *)
      Definition arrowE : Type := arrow tags_t (t tags_t * e) (t tags_t * (name tags_t)).
    End Expressions.

    Arguments EBool {tags_t}.
    Arguments EInteger {tags_t}.
    Arguments EBitstring {tags_t}.
    Arguments EVar {tags_t}.
    Arguments EUop {tags_t}.
    Arguments EBop {tags_t}.
    Arguments ECast {tags_t}.
    Arguments ERecord {tags_t}.
    Arguments EExprMember {tags_t}.
    Arguments EError {tags_t}.
    Arguments EMatchKind {tags_t}.

    Module ExprNotations.
      Declare Custom Entry p4expr.

      Notation "'<{' exp '}>'" := exp (exp custom p4expr at level 99).
      Notation "( x )" := x (in custom p4expr, x at level 99).
      Notation "x" := x (in custom p4expr at level 0, x constr at level 0).
      Notation "'True' @ i" := (EBool true i) (in custom p4expr at level 0).
      Notation "'False' @ i" := (EBool false i) (in custom p4expr at level 0).
      Notation "'BOOL' b @ i" := (EBool b i) (in custom p4expr at level 0).
      Notation "'INT' n @ i" := (EInteger n i) (in custom p4expr at level 0).
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
      Context {tags_t : Type}.

      Variable P : e tags_t -> Prop.

      Hypothesis HEBool : forall b i,
          P <{ BOOL b @ i }>.

      Hypothesis HEInteger : forall n i,
          P <{ INT n @ i }>.

      Hypothesis HEBitstring : forall (w : nat) (v : N) i,
          P <{ Bit<w> v @ i }>.

      Hypothesis HEVar : forall (ty : t tags_t) (x : name tags_t) i,
          P <{ Var x :: ty @ i end }>.

      Hypothesis HEUop : forall (op : uop) (ty : t tags_t) (ex : e tags_t) i,
          P ex -> P (EUop op ty ex i).

      Hypothesis HEBop : forall (op : bop) (lt rt : t tags_t) (lhs rhs : e tags_t) i,
          P lhs -> P rhs -> P (EBop op lt rt lhs rhs i).

      Hypothesis HECast : forall (ct et : t tags_t) (ex : e tags_t) i,
          P ex -> P <{ (ct) ex :: et @ i end }>.

      Hypothesis HERecord : forall (fields : F.fs tags_t (t tags_t * e tags_t)) i,
          F.predfs_data (P ∘ snd) fields -> P <{ rec {fields} @ i }>.

      Hypothesis HEExprMember : forall (x : name tags_t) (ty : t tags_t) (ex : e tags_t) i,
          P ex -> P <{ Mem ex :: ty dot x @ i end }>.

      Hypothesis HEError : forall err i,
          P <{ Error err @ i }>.

      Hypothesis HEMatchKind : forall mkd i,
          P <{ Matchkind mkd @ i }>.

      (** A custom induction principle.
          Do [induction ?e using custom_e_ind]. *)
      Definition custom_e_ind : forall exp : e tags_t, P exp :=
        fix custom_e_ind (expr : e tags_t) : P expr :=
          let fix fields_ind {A:Type} (flds : F.fs tags_t (A * e tags_t))
              : F.predfs_data (P ∘ snd) flds :=
              match flds as fs_ex
                    return F.predfs_data (P ∘ snd) fs_ex with
              | [] => Forall_nil (F.predf_data (P ∘ snd))
              | (_, (_, hfe)) as hf :: tf =>
                Forall_cons hf (custom_e_ind hfe) (fields_ind tf)
              end in
          match expr as e' return P e' with
          | <{ BOOL b @ i }> => HEBool b i
          | <{ INT n @ i }> => HEInteger n i
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
      (**[]*)
    End ExprInduction.
  End Expr.

  (** * Statement Grammar *)
  Module Stmt.
    Import Dir.
    Module E := Expr.

    Section Statements.
      Variable (tags_t : Type).

      Inductive s : Type :=
      | SSkip (i : tags_t)                               (* skip, useful for
                                                            small-step semantics *)
      | SAssign (type : E.t tags_t) (lhs rhs : E.e tags_t)
                (i : tags_t)                             (* assignment *)
      | SConditional (guard_type : E.t tags_t) (guard : E.e tags_t)
                     (tru_blk fls_blk : s) (i : tags_t)  (* conditionals *)
      | SSeq (s1 s2 : s) (i : tags_t)                    (* sequences,
                                                            an alternative to blocks *)
      | SVarDecl (typ : E.t tags_t) (var : name tags_t)
                 (rhs : E.e tags_t) (i : tags_t)         (* variable declaration *)
      | SCall (f : name tags_t) (args : E.arrowE tags_t)
              (i : tags_t)                               (* function/action/extern call *)
      | SReturnVoid (i : tags_t)                         (* void return statement *)
      | SReturnFruit (t : E.t tags_t)
                     (e : E.e tags_t)(i : tags_t)        (* fruitful return statement *).
    (**[]*)
    End Statements.

    Arguments SSkip {tags_t}.
    Arguments SAssign {tags_t}.
    Arguments SConditional {tags_t}.
    Arguments SSeq {tags_t}.
    Arguments SVarDecl {tags_t}.
    Arguments SCall {tags_t}.
    Arguments SReturnVoid {tags_t}.
    Arguments SReturnFruit {tags_t}.

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
        := (SCall f (E.Arrow args None) i)
             (in custom p4stmt at level 30, no associativity).
      Notation "'let' e '::' t ':=' 'call' f 'with' args @ i 'fin'"
               := (SCall f (E.Arrow args (Some (t,e))) i)
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

    Section Declarations.
      Variable (tags_t : Type).

      (** Here is the subset of declarations that
          may occur within controls, parsers,
          and even the top-level. *)
      Inductive d : Type :=
      | DVardecl (typ : E.t tags_t) (x : name tags_t)
                 (i : tags_t)                      (* unitialized variable *)
      | DVarinit (typ : E.t tags_t) (x : name tags_t)
                 (rhs : E.e tags_t) (i : tags_t)   (* initialized variable *)
      | DConst   (typ : E.t tags_t) (x : name tags_t)
                 (rhs : E.e tags_t) (i : tags_t)   (* constant *)
      | DInstantiate (C x : name tags_t) (args : F.fs tags_t (E.t tags_t * E.e tags_t))
                     (i : tags_t)                  (* constructor [C]
                                                      with [args] makes [x] *)
      | DFunction (f : name tags_t) (signature : E.arrowT tags_t)
                  (body : S.s tags_t) (i : tags_t) (* function/method declaration *)
      | DSeq (d1 d2 : d) (i : tags_t)              (* sequence of declarations *).
    (**[]*)
    End Declarations.

    Arguments DVardecl {tags_t}.
    Arguments DVarinit {tags_t}.
    Arguments DConst {tags_t}.
    Arguments DInstantiate {tags_t}.
    Arguments DFunction {tags_t}.
    Arguments DSeq {tags_t}.
  End Decl.

  (** * Controls *)
  Module Control.
    Module E := Expr.
    Module S := Stmt.
    Module D := Decl.

    Section ControlDecls.
      Variable (tags_t : Type).

      (** Declarations that may occur within Controls. *)
      (* TODO, this is a stub. *)
      Inductive d : Type :=
      | DTable (i : tags_t) (* TODO! *)
      | DDecl (d : D.d tags_t) (i : tags_t)
      | DSeq (d1 d2 : d) (i : tags_t).
      (**[]*)
    End ControlDecls.
  End Control.

  (** * Top-Level Declarations *)
  Module TopDecl.
    Module E := Expr.
    Module S := Stmt.
    Module D := Decl.
    Module C := Control.

    Section TopDeclarations.
      Variable (tags_t : Type).

      (** Top-level declarations. *)
      (* TODO, this is a stub. *)
      Inductive d : Type :=
      | TPDecl (d : D.d tags_t) (i : tags_t)
      | TPControl (cparams : F.fs tags_t (E.t tags_t))
                  (params : F.fs tags_t (Dir.d * tags_t))
                  (body : C.d tags_t) (apply_blk : S.s tags_t) (i : tags_t)
      | TPParser (cparams : F.fs tags_t (E.t tags_t))
                 (params : F.fs tags_t (Dir.d * E.t tags_t)) (i : tags_t) (* TODO! *)
      | TPSeq (d1 d2 : d) (i : tags_t).
      (**[]*)
    End TopDeclarations.
  End TopDecl.
End P4light.
