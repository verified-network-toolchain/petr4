Require Export Coq.Lists.List.
Export ListNotations.
Require Export Coq.Bool.Bool.
Require Export Coq.Classes.EquivDec.
Require Export Coq.Numbers.BinNums. (** Integers. *)
Require Petr4.String.
Require Petr4.P4String. (** Strings. *)
Require Petr4.Typed. (** Names. *)

Instance PositiveEqDec : EqDec positive eq := { equiv_dec := BinPos.Pos.eq_dec }.

Instance NEqDec : EqDec N eq := { equiv_dec := BinNat.N.eq_dec }.

Instance ZEqDec : EqDec Z eq := { equiv_dec := BinInt.Z.eq_dec }.

Instance StringEqDec : EqDec Petr4.String.t eq := Petr4.String.StringEqDec.

Section TypeSynonyms.
  Variable (tags_t : Type).

  Definition string : Type := Petr4.P4String.t tags_t.

  Instance P4StringEqDec : EqDec string (@P4String.equiv tags_t) :=
    P4String.P4StringEqDec tags_t.
  (**[]*)

  Definition int : Type := Petr4.P4Int.t tags_t.

  Instance P4IntEquivalence : Equivalence (@P4Int.equiv tags_t) :=
    P4Int.IntEquivalence tags_t.
  (**[]*)

  Instance P4IntEqDec : EqDec int (P4Int.equiv) :=
    P4Int.IntEqDec tags_t.
  (**[]*)

  Definition name : Type := @Typed.name tags_t.

  Definition equivn (n1 n2 : name) : Prop :=
    match n1, n2 with
    | Typed.BareName x1,
      Typed.BareName x2          => P4String.equiv x1 x2
    | Typed.QualifiedName xs1 x1,
      Typed.QualifiedName xs2 x2 =>
        P4String.equiv x1 x2 /\
        List.Forall2 (@P4String.equiv tags_t) xs1 xs2
    | _, _ => False
    end.

  Lemma equivn_reflexive : Reflexive equivn.
  Proof.
    intros [x | xs x]; simpl.
    - reflexivity.
    - split; try reflexivity.
      induction xs as [| h xs IHxs];
        constructor; auto. reflexivity.
  Qed.

  Lemma equivn_symmetric : Symmetric equivn.
  Proof.
    intros [x | xs x] [y | ys y] H; simpl in *; auto.
    - symmetry. assumption.
    - destruct H as [Hxy H]. split; try (symmetry; assumption).
      generalize dependent ys; induction xs as [| hx xs IHxs];
        intros [| hy ys] H; inversion H; clear H; subst; auto;
      constructor; auto. symmetry. assumption.
  Qed.

  Lemma equivn_transitive : Transitive equivn.
  Proof.
    intros [x | xs x] [y | ys y] [z | zs z] Hxy Hyz;
      simpl in *; auto; try contradiction.
    - transitivity y; auto.
    - destruct Hxy as [Hxy Hxys]; destruct Hyz as [Hyz Hyzs]; split.
      + transitivity y; auto.
      + clear x y z Hxy Hyz.
        generalize dependent zs; generalize dependent ys.
        induction xs as [| x xs IHxs];
          intros [| y ys] Hxy [| z zs] Hyz;
          inversion Hxy; clear Hxy;
            inversion Hyz; clear Hyz; subst; auto.
        constructor.
        * transitivity y; auto.
        * apply IHxs with ys; auto.
  Qed.

  Instance NameEquivalence : Equivalence equivn.
  Proof.
    constructor; [ apply equivn_reflexive
                 | apply equivn_symmetric
                 | apply equivn_transitive].
  Defined.

  Definition equivn_dec : forall n1 n2 : name,
      { equivn n1 n2 } + { ~ equivn n1 n2 }.
  Proof.
    intros [x | xs x] [y | ys y]; simpl; auto.
    - pose proof equiv_dec x y; auto.
    - assert (H : {List.Forall2 (@P4String.equiv tags_t) xs ys} +
                  {~ List.Forall2 (@P4String.equiv tags_t) xs ys}).
      { clear x y; generalize dependent ys.
        induction xs as [| x xs IHxs]; intros [| y ys];
          try (right; intros H'; inversion H'; contradiction).
        - left; constructor.
        - pose proof equiv_dec x y as Hxy; specialize IHxs with ys;
            unfold equiv in *; unfold complement in *.
          destruct Hxy as [Hxy | Hxy]; destruct IHxs as [IH | IH];
            try (right; intros H'; inversion H'; contradiction).
          left. constructor; auto. }
      destruct (equiv_dec x y) as [Hxy | Hxy]; destruct H as [H | H];
        unfold equiv in *; unfold complement in *;
          try (right; intros [Hxy' H']; contradiction).
      left; auto.
  Defined.

  Instance NameEqDec : EqDec name equivn :=
    { equiv_dec := equivn_dec }.
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
    Definition f (T : Type) : Type := (string tags_t) * T.

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
    Definition relf {U V : Type}
               (R : U -> V -> Prop) : f tags_t U -> f tags_t V -> Prop :=
      fun u v => P4String.equiv (fst u) (fst v) /\ R (snd u) (snd v).
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
    Definition fold {U V : Type} (f : string tags_t -> U -> V -> V)
               (fds : fs tags_t U) (init : V) : V :=
      List.fold_right (fun '(x,u) acc => f x u acc) init fds.
    (**[]*)

    (** Member access. *)
    Fixpoint get {U : Type} (x : string tags_t)
             (fds : fs tags_t U) : option U :=
      match fds with
      | []            => None
      | (x',u') :: fds => if equiv_dec x x' then Some u'
                        else get x fds
      end.

    (** Member update. *)
    Fixpoint update {U : Type} (x : string tags_t) (u : U)
             (fds : fs tags_t U) : fs tags_t U :=
      match fds with
      | [] => []
      | (x',u') :: fds => (x', if equiv_dec x x' then u else u') :: update x u fds
      end.
    (**[]*)
  End FieldLibrary.
End Field.

(** * P4light AST *)
Module P4light.
  Module F := Field.

  (** Function call parameters/arguments. *)
  Inductive paramarg (A B : Type) : Type :=
  | PAIn (a : A)
  | PAOut (b : B)
  | PAInOut (b : B).

  Arguments PAIn {_} {_}.
  Arguments PAOut {_} {_}.
  Arguments PAInOut {_} {_}.

  (** Relating [paramarg]s. *)
  Definition rel_paramarg {A1 A2 B1 B2 : Type}
             (RA : A1 -> A2 -> Prop) (RB : B1 -> B2 -> Prop)
             (pa1 : paramarg A1 B1)
             (pa2 : paramarg A2 B2) : Prop :=
    match pa1, pa2 with
    | PAIn a1, PAIn a2       => RA a1 a2
    | PAOut b1, PAOut b2
    | PAInOut b1, PAInOut b2 => RB b1 b2
    | _, _ => False
    end.
  (**[]*)

  (** Function signatures/instantiations. *)
  Inductive arrow (tags_t A B R : Type) : Type :=
    Arrow (pas : F.fs tags_t (paramarg A B)) (returns : option R).
  (**[]*)

  Arguments Arrow {_} {_} {_} {_}.

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
      | TBit (width : positive)          (* unsigned integers *)
      | TInt (width : positive)          (* signed integers *)
      | TError                           (* the error type *)
      | TMatchKind                       (* the matchkind type *)
      | TRecord (fields : F.fs tags_t t) (* the record and struct type *)
      | THeader (fields : F.fs tags_t t) (* the header type *).
      (**[]*)

      (** Function parameters. *)
      Definition params : Type := F.fs tags_t (paramarg t t).

      (** Function types. *)
      Definition arrowT : Type := arrow tags_t t t t.
    End P4Types.

    Arguments TBool {_}.
    Arguments TBit {_}.
    Arguments TInt {_}.
    Arguments TError {_}.
    Arguments TMatchKind {_}.
    Arguments TRecord {_}.
    Arguments THeader {_}.

    Module TypeNotations.
      Declare Custom Entry p4type.

      Notation "'{{' ty '}}'" := ty (ty custom p4type at level 99).
      Notation "( x )" := x (in custom p4type, x at level 99).
      Notation "x" := x (in custom p4type at level 0, x constr at level 0).
      Notation "'Bool'" := TBool (in custom p4type at level 0).
      Notation "'bit' '<' w '>'"
        := (TBit w)
            (in custom p4type at level 2,
                w custom p4type at level 99, no associativity).
      Notation "'int' '<' w '>'"
        := (TInt w)
            (in custom p4type at level 2,
                w custom p4type at level 99, no associativity).
      Notation "'error'" := TError
                              (in custom p4type at level 0,
                                  no associativity).
      Notation "'matchkind'"
        := TMatchKind (in custom p4type at level 0, no associativity).
      Notation "'rec' { fields }"
        := (TRecord fields)
            (in custom p4type at level 6, no associativity).
      Notation "'hdr' { fields }"
        := (THeader fields)
            (in custom p4type at level 6, no associativity).
    End TypeNotations.

    (** Custom induction principle for [t]. *)
    Section TypeInduction.
      Import TypeNotations.

      Context {tags_t : Type}.

      (** An arbitrary property. *)
      Variable P : t tags_t -> Prop.

      Hypothesis HTBool : P {{ Bool }}.

      Hypothesis HTBit : forall w, P {{ bit<w> }}.

      Hypothesis HTInt : forall w, P {{ int<w> }}.

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
          let fix fields_ind
                  (flds : F.fs tags_t (t tags_t)) : F.predfs_data P flds :=
              match flds as fs_ty return F.predfs_data P fs_ty with
              | [] => Forall_nil (F.predf_data P)
              | (_, hft) as hf :: tf =>
                Forall_cons hf (custom_t_ind hft) (fields_ind tf)
              end in
          let fix fields_ind_dir
                  (flds : F.fs tags_t (d * t tags_t)) :
                F.predfs_data (P ∘ snd) flds :=
              match flds as fs_ty return F.predfs_data (P ∘ snd) fs_ty with
              | [] => Forall_nil (F.predf_data (P ∘ snd))
              | (_, (_, hft)) as hf :: tf =>
                Forall_cons hf (custom_t_ind hft) (fields_ind_dir tf)
              end in
          match type as ty return P ty with
          | {{ Bool }} => HTBool
          | {{ bit<w> }} => HTBit w
          | {{ int<w> }} => HTInt w
          | {{ error }} => HTError
          | {{ matchkind }} => HTMatchKind
          | {{ rec { fields } }} => HTRecord fields (fields_ind fields)
          | {{ hdr { fields } }} => HTHeader fields (fields_ind fields)
          end.
      (**[]*)
    End TypeInduction.

    Section TypeEquivalence.
      Context {tags_t : Type}.

      (** Equality of types. *)
      Inductive equivt : t tags_t -> t tags_t -> Prop :=
      | equivt_bool : equivt TBool TBool
      | equivt_bit (w : positive) : equivt (TBit w) (TBit w)
      | equivt_int (w : positive) : equivt (TInt w) (TInt w)
      | equivt_error : equivt TError TError
      | equivt_matchkind : equivt TMatchKind TMatchKind
      | equivt_record (fs1 fs2 : F.fs tags_t (t tags_t)) :
          F.relfs equivt fs1 fs2 ->
          equivt (TRecord fs1) (TRecord fs2)
      | equivt_header (fs1 fs2 : F.fs tags_t (t tags_t)) :
          F.relfs equivt fs1 fs2 ->
          equivt (THeader fs1) (THeader fs2).
      (**[]*)

      Lemma equivt_reflexive : Reflexive equivt.
      Proof.
        intros ty;
          induction ty using custom_t_ind; constructor;
            try (induction H; constructor; auto;
                 destruct x as [x ty]; unfold F.relf; simpl in *;
                 split; auto; try reflexivity).
      Qed.

      Lemma equivt_symmetric : Symmetric equivt.
      Proof.
        intros t1;
        induction t1 using custom_t_ind;
          intros [] HEQ; inversion HEQ; clear HEQ; constructor;
            symmetry in H0, H1; subst;
              induction H2; constructor;
                inversion H; clear H; subst;
                  try (destruct x as [x1 t1];
                       destruct y as [x2 t2];
                       unfold F.predf_data in H4;
                       unfold F.relf in *; simpl in *;
                       destruct H0; split; auto;
                       symmetry; assumption);
        try (apply IHForall2; auto).
      Qed.

      Lemma equivt_transitive : Transitive equivt.
      Proof.
        intros x; induction x using custom_t_ind;
          intros [] [] Hxy Hyz; auto;
          inversion Hxy; inversion Hyz; subst; auto; clear Hxy Hyz;
        try (rename fields into fs1; rename fields0 into fs2;
             rename fields1 into fs3; constructor;
             generalize dependent fs3; generalize dependent fs2;
             induction fs1 as [| [x1 t1] fs1 IHfs1];
             intros [| [x2 t2] fs2] H12; intros [| [x3 t3] fs3] H23;
             inversion H12; inversion H23; inversion H;
             clear H12 H23 H; subst; constructor;
             [ unfold F.relf in *; simpl in *;
               destruct H3; destruct H9; split; eauto;
               transitivity x2; assumption
             | eapply IHfs1; eauto]).
      Qed.

      Instance TypeEquivalence : Equivalence equivt.
      Proof.
        constructor; [ apply equivt_reflexive
                     | apply equivt_symmetric
                     | apply equivt_transitive].
      Defined.

      Lemma equivt_dec : forall (t1 t2 : t tags_t),
          equivt t1 t2 \/ ~ equivt t1 t2.
      Proof.
        induction t1 using custom_t_ind; intros [];
          try (left; apply equivt_reflexive);
          try (right; intros HR; inversion HR; assumption);
          try (destruct (equiv_dec w width) as [Hwidth | Hwidth];
               unfold equiv in *; unfold complement in *; subst;
               try (right; intros H'; inversion H'; contradiction);
               try (left; reflexivity)).
        - rename fields into fs1; rename fields0 into fs2.
          generalize dependent fs2.
          induction fs1 as [| [x1 t1] fs1 IHfs1]; intros [| [x2 t2] fs2];
            try (left; reflexivity);
            try (right; intros H';
                 inversion H'; inversion H2; assumption); subst.
          inversion H; clear H; subst; unfold F.predf_data in H2.
          pose proof IHfs1 H3 fs2 as IH; clear IHfs1 H3.
          destruct (equiv_dec x1 x2) as [H12 | H12];
            unfold equiv in *; unfold complement in *;
              destruct (H2 t2) as [HT | HT]; clear H2;
              destruct IH as [IH | IH];
              try (right; intros H'; inversion H';
                   clear H'; subst; inversion H1;
                   clear H1; subst; unfold F.relf in *;
                   simpl in *; destruct H3; contradiction).
          + left; constructor; inversion IH; subst;
            constructor; auto; unfold F.relf; split; auto.
          + right; intros H'; inversion H'; subst;
              clear H'; inversion H1; subst; apply IH;
                constructor; auto.
        - rename fields into fs1; rename fields0 into fs2.
          generalize dependent fs2.
          induction fs1 as [| [x1 t1] fs1 IHfs1]; intros [| [x2 t2] fs2];
            try (left; reflexivity);
            try (right; intros H';
                 inversion H'; inversion H2; assumption); subst.
          inversion H; clear H; subst; unfold F.predf_data in H2.
          pose proof IHfs1 H3 fs2 as IH; clear IHfs1 H3.
          destruct (equiv_dec x1 x2) as [H12 | H12];
            unfold equiv in *; unfold complement in *;
              destruct (H2 t2) as [HT | HT]; clear H2;
              destruct IH as [IH | IH];
              try (right; intros H'; inversion H';
                   clear H'; subst; inversion H1;
                   clear H1; subst; unfold F.relf in *;
                   simpl in *; destruct H3; contradiction).
          + left; constructor; inversion IH; subst;
            constructor; auto; unfold F.relf; split; auto.
          + right; intros H'; inversion H'; subst;
              clear H'; inversion H1; subst; apply IH;
                constructor; auto.
      Qed.
    End TypeEquivalence.

    Inductive uop : Set :=
    | Not    (* boolean negation *)
    | BitNot (* bitwise negation *)
    | UMinus (* integer negation *).
    (**[]*)

    Module UopNotations.
      Declare Custom Entry p4uop.

      Notation "x" := x (in custom p4uop at level 0, x constr at level 0).
      Notation "!" := Not (in custom p4uop at level 0).
      Notation "~" := BitNot (in custom p4uop at level 0).
      Notation "-" := UMinus (in custom p4uop at level 0).
    End UopNotations.

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

    Module BopNotations.
      Declare Custom Entry p4bop.

      Notation "x" := x (in custom p4bop at level 0, x constr at level 0).
      Notation "+" := Plus (in custom p4bop at level 0).
      Notation "-" := Minus (in custom p4bop at level 0).
      Notation "'|+|'" := PlusSat (in custom p4bop at level 0).
      Notation "'|-|'" := MinusSat (in custom p4bop at level 0).
      Notation "'<<'" := Shl (in custom p4bop at level 0).
      Notation "'>>'" := Shr (in custom p4bop at level 0).
      Notation "'<='" := Le (in custom p4bop at level 0).
      Notation "'>='" := Ge (in custom p4bop at level 0).
      Notation "<" := Lt (in custom p4bop at level 0).
      Notation ">" := Gt (in custom p4bop at level 0).
      Notation "'=='" := Eq (in custom p4bop at level 0).
      Notation "'!='" := NotEq (in custom p4bop at level 0).
      Notation "&" := BitAnd (in custom p4bop at level 0).
      Notation "^" := BitXor (in custom p4bop at level 0).
      Notation "|" := BitOr (in custom p4bop at level 0).
      Notation "'&&'" := And (in custom p4bop at level 0).
      Notation "'||'" := Or (in custom p4bop at level 0).
      Notation "'++'" := PlusPlus (in custom p4bop at level 0).
    End BopNotations.

    (** Default matchkinds. *)
    Inductive matchkind : Set :=
    | MKExact
    | MKTernary
    | MKLpm.
    (**[]*)

    Module MatchkindNotations.
      Declare Custom Entry p4matchkind.

      Notation "x" := x (in custom p4matchkind at level 0, x constr at level 0).
      Notation "'exact'" := MKExact (in custom p4matchkind at level 0).
      Notation "'ternary'" := MKTernary (in custom p4matchkind at level 0).
      Notation "'lpm'" := MKLpm (in custom p4matchkind at level 0).
    End MatchkindNotations.

    Section Expressions.
      Variable (tags_t : Type).

      (** Expressions annotated with types,
          unless the type is obvious. *)
      Inductive e : Type :=
      | EBool (b : bool) (i : tags_t)                      (* booleans *)
      | EBit (width : positive) (val : N) (i : tags_t)  (* unsigned integers *)
      | EInt (width : positive) (val : Z) (i : tags_t)  (* signed integers *)
      | EVar (type : t tags_t) (x : name tags_t)
             (i : tags_t)                               (* variables *)
      | EUop (op : uop) (type : t tags_t)
             (arg : e) (i : tags_t)                     (* unary operations *)
      | EBop (op : bop) (lhs_type rhs_type : t tags_t)
             (lhs rhs : e) (i : tags_t)                 (* binary operations *)
      | ERecord (fields : F.fs tags_t (t tags_t * e))
                (i : tags_t)                           (* records and structs *)
      | EHeader (fields : F.fs tags_t (t tags_t * e))
                (i : tags_t)                           (* header literals *)
      | EExprMember (mem : string tags_t)
                    (expr_type : t tags_t)
                    (arg : e) (i : tags_t)             (* member-expressions *)
      | EError (err : option (string tags_t))
               (i : tags_t)                            (* error literals *)
      | EMatchKind (mk : matchkind) (i : tags_t)       (* matchkind literals *).
      (**[]*)

      (** Function call arguments. *)
      Definition args : Type :=
        F.fs tags_t (paramarg (t tags_t * e) (t tags_t * e)).
      (**[]*)

      (** Function call. *)
      Definition arrowE : Type :=
        arrow tags_t (t tags_t * e) (t tags_t * e) (t tags_t * e).
      (**[]*)
    End Expressions.

    Arguments EBool {tags_t}.
    Arguments EBit {_}.
    Arguments EInt {_}.
    Arguments EVar {tags_t}.
    Arguments EUop {tags_t}.
    Arguments EBop {tags_t}.
    Arguments ERecord {tags_t}.
    Arguments EHeader {_}.
    Arguments EExprMember {tags_t}.
    Arguments EError {tags_t}.
    Arguments EMatchKind {tags_t}.

    Module ExprNotations.
      Declare Custom Entry p4expr.

      Export UopNotations.
      Export BopNotations.
      Export MatchkindNotations.
      Export TypeNotations.

      Notation "'<{' exp '}>'" := exp (exp custom p4expr at level 99).
      Notation "( x )" := x (in custom p4expr, x at level 99).
      Notation "x" := x (in custom p4expr at level 0, x constr at level 0).
      Notation "'True' @ i" := (EBool true i) (in custom p4expr at level 0).
      Notation "'False' @ i" := (EBool false i) (in custom p4expr at level 0).
      Notation "'BOOL' b @ i" := (EBool b i) (in custom p4expr at level 0).
      Notation "w 'W' n @ i" := (EBit w n i) (in custom p4expr at level 0).
      Notation "w 'S' n @ i" := (EInt w n i) (in custom p4expr at level 0).
      Notation "'Var' x '::' ty @ i 'end'" := (EVar ty x i)
                            (in custom p4expr at level 0, no associativity).
      Notation "'UOP' op x '::' ty @ i 'end'"
               := (EUop op ty x i)
                    (in custom p4expr at level 2,
                        x custom p4expr, ty custom p4type,
                        op custom p4uop, no associativity).
      Notation "'BOP' x '::' tx op y '::' ty @ i 'end'"
               := (EBop op tx ty x y i)
                    (in custom p4expr at level 10,
                        x custom p4expr, tx custom p4type,
                        y custom p4expr, ty custom p4type,
                        op custom p4bop, left associativity).
      Notation "'rec' { fields } @ i "
        := (ERecord fields i)
            (in custom p4expr at level 6, no associativity).
      Notation "'hdr' { fields } @ i "
        := (EHeader fields i)
            (in custom p4expr at level 6, no associativity).
      Notation "'Mem' x '::' ty 'dot' y @ i 'end'"
              := (EExprMember y ty x i)
                    (in custom p4expr at level 10, x custom p4expr,
                        ty custom p4type, left associativity).
      Notation "'Error' x @ i" := (EError x i)
                              (in custom p4expr at level 0, no associativity).
      Notation "'Matchkind' mk @ i" := (EMatchKind mk i)
                              (in custom p4expr at level 0,
                                  mk custom p4matchkind, no associativity).
    End ExprNotations.

    (** A custom induction principle for [e]. *)
    Section ExprInduction.
      Import ExprNotations.

      (** An arbitrary predicate. *)
      Context {tags_t : Type}.

      Variable P : e tags_t -> Prop.

      Hypothesis HEBool : forall b i, P <{ BOOL b @ i }>.

      Hypothesis HEBit : forall w n i, P <{ w W n @ i }>.

      Hypothesis HEInt : forall w n i, P <{ w S n @ i }>.

      Hypothesis HEVar : forall (ty : t tags_t) (x : name tags_t) i,
          P <{ Var x :: ty @ i end }>.

      Hypothesis HEUop : forall (op : uop) (ty : t tags_t) (ex : e tags_t) i,
          P ex -> P <{ UOP op ex :: ty @ i end }>.

      Hypothesis HEBop : forall (op : bop) (lt rt : t tags_t) (lhs rhs : e tags_t) i,
          P lhs -> P rhs -> P <{ BOP lhs :: lt op rhs :: rt @ i end }>.

      Hypothesis HERecord : forall (fields : F.fs tags_t (t tags_t * e tags_t)) i,
          F.predfs_data (P ∘ snd) fields -> P <{ rec {fields} @ i }>.

      Hypothesis HEHeader : forall (fields : F.fs tags_t (t tags_t * e tags_t)) i,
          F.predfs_data (P ∘ snd) fields -> P <{ hdr {fields} @ i }>.

      Hypothesis HEExprMember : forall (x : string tags_t)
                                  (ty : t tags_t) (ex : e tags_t) i,
          P ex -> P <{ Mem ex :: ty dot x @ i end }>.

      Hypothesis HEError : forall err i, P <{ Error err @ i }>.

      Hypothesis HEMatchKind : forall mkd i, P <{ Matchkind mkd @ i }>.

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
          | <{ w W n @ i }>  => HEBit w n i
          | <{ w S n @ i }>  => HEInt w n i
          | <{ Var x :: ty @ i end }> => HEVar ty x i
          | <{ UOP op exp :: ty @ i end }> => HEUop op ty exp i (custom_e_ind exp)
          | <{ BOP lhs :: lt op rhs :: rt @ i end }> =>
              HEBop op lt rt lhs rhs i
                    (custom_e_ind lhs) (custom_e_ind rhs)
          | <{ rec { fields } @ i }> => HERecord fields i (fields_ind fields)
          | <{ hdr { fields } @ i }> => HEHeader fields i (fields_ind fields)
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
      | SSkip (i : tags_t)                              (* skip, useful for
                                                           small-step semantics *)
      | SVardecl (type : E.t tags_t)
                 (x : name tags_t) (i : tags_t)         (* Variable declaration. *)
      | SAssign (type : E.t tags_t) (lhs rhs : E.e tags_t)
                (i : tags_t)                            (* assignment *)
      | SConditional (guard_type : E.t tags_t)
                     (guard : E.e tags_t)
                     (tru_blk fls_blk : s) (i : tags_t) (* conditionals *)
      | SSeq (s1 s2 : s) (i : tags_t)                   (* sequences,
                                                           an alternative to blocks *)
      | SCall (f : name tags_t) (args : E.arrowE tags_t)
              (i : tags_t)                              (* function/action/extern call *)
      | SReturnVoid (i : tags_t)                        (* void return statement *)
      | SReturnFruit (t : E.t tags_t)
                     (e : E.e tags_t)(i : tags_t)       (* fruitful return statement *)
      | SExit (i : tags_t)                              (* exit statement *).
    (**[]*)
    End Statements.

    Arguments SSkip {tags_t}.
    Arguments SVardecl {_}.
    Arguments SAssign {tags_t}.
    Arguments SConditional {tags_t}.
    Arguments SSeq {tags_t}.
    Arguments SCall {tags_t}.
    Arguments SReturnVoid {tags_t}.
    Arguments SReturnFruit {tags_t}.
    Arguments SExit {_}.

    Module StmtNotations.
      Export E.ExprNotations.

      Declare Custom Entry p4stmt.

      Notation "'-{' stmt '}-'" := stmt (stmt custom p4stmt at level 99).
      Notation "( x )" := x (in custom p4stmt, x at level 99).
      Notation "x"
        := x (in custom p4stmt at level 0, x constr at level 0).
      Notation "'skip' @ i" := (SSkip i) (in custom p4stmt at level 0).
      Notation "s1 ; s2 @ i"
        := (SSeq s1 s2 i) (in custom p4stmt at level 99,
                            s1 custom p4stmt, s2 custom p4stmt,
                            right associativity).
      Notation "'var' x '::' t @ i"
               := (SVardecl t x i)
                    (in custom p4stmt at level 0, t custom p4type).
      Notation "'asgn' e1 ':=' e2 :: t @ i 'fin'"
              := (SAssign t e1 e2 i)
                    (in custom p4stmt at level 40,
                        e1 custom p4expr, e2 custom p4expr,
                        t custom p4type, no associativity).
      Notation "'if' e '::' t 'then' s1 'else' s2 @ i 'fin'"
              := (SConditional t e s1 s2 i)
                    (in custom p4stmt at level 80,
                        t custom p4type, e custom p4expr,
                        s1 custom p4stmt, s2 custom p4stmt,
                        no associativity).
      Notation "'call' f 'with' args @ i 'fin'"
        := (SCall f (Arrow args None) i)
             (in custom p4stmt at level 30, no associativity).
      Notation "'let' e '::' t ':=' 'call' f 'with' args @ i 'fin'"
               := (SCall f (Arrow args (Some (t,e))) i)
                    (in custom p4stmt at level 30,
                        e custom p4expr, t custom p4stmt, no associativity).
      Notation "'return' e '::' t @ i 'fin'"
               := (SReturnFruit t e i)
                    (in custom p4stmt at level 30,
                        e custom p4expr, t custom p4type, no associativity).
      Notation "'returns' @ i"
               := (SReturnVoid i)
                    (in custom p4stmt at level 0, no associativity).
      Notation "'exit' @ i"
               := (SExit i) (in custom p4stmt at level 0, no associativity).
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
      | DVardecl (typ : E.t tags_t) (x : string tags_t)
                 (i : tags_t)                      (* unitialized variable *)
      | DVarinit (typ : E.t tags_t) (x : string tags_t)
                 (rhs : E.e tags_t) (i : tags_t)   (* initialized variable *)
      | DConst   (typ : E.t tags_t) (x : string tags_t)
                 (rhs : E.e tags_t) (i : tags_t)   (* constant *)
      | DInstantiate (C : name tags_t) (x : string tags_t)
                     (args : F.fs tags_t (E.t tags_t * E.e tags_t))
                     (i : tags_t)                  (* constructor [C]
                                                      with [args] makes [x] *)
      | DSeq (d1 d2 : d) (i : tags_t)              (* sequence of declarations *).
    (**[]*)
    End Declarations.

    Arguments DVardecl {tags_t}.
    Arguments DVarinit {tags_t}.
    Arguments DConst {tags_t}.
    Arguments DInstantiate {tags_t}.
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
      | DAction (a : string tags_t)
                (signature : F.fs tags_t (E.e tags_t))
                (body : S.s tags_t) (i : tags_t) (* action declaration *)
      | DTable (keys : F.fs tags_t (E.t tags_t)) (* field names are matchkinds *)
               (actions : list (string tags_t))  (* action names *)
               (i : tags_t)                      (* table declaration *)
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
                 (params : F.fs tags_t (Dir.d * E.t tags_t))
                 (i : tags_t) (* TODO! *)
      | TPFunction (f : string tags_t) (signature : E.arrowT tags_t)
                   (body : S.s tags_t) (i : tags_t)
                   (* function/method declaration *)
      | TPSeq (d1 d2 : d) (i : tags_t).
      (**[]*)
    End TopDeclarations.
  End TopDecl.
End P4light.
