Require Export P4light.Check.
Require Export P4light.P4Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.NArith.BinNatDef.
Require Import Coq.ZArith.BinIntDef.
Require Import Coq.NArith.BinNat.
Require Import Coq.ZArith.BinInt.

(** Notation entries. *)
Declare Custom Entry p4value.
Declare Custom Entry p4lvalue.
Declare Custom Entry p4evalsignal.

Reserved Notation "⟨ ϵ , e ⟩ ⇓ v"
         (at level 40, e custom p4expr, v custom p4value).

Reserved Notation "⦑ ϵ , e ⦒ ⇓ lv"
         (at level 40, e custom p4expr, lv custom p4lvalue).

Reserved Notation "⟪ fenv , ienv , ϵ1 , s ⟫ ⤋ ⟪ ϵ2 , sig ⟫"
         (at level 40, s custom p4stmt,
          ϵ2 custom p4env, sig custom p4evalsignal).

(** * Values and LValues *)
Module Value.
  Section Values.
    Variable (tags_t : Type).

    (** Values from expression evaluation. *)
    Inductive v : Type :=
    | VBool (b : bool)
    | VInt (w : positive) (n : Z)
    | VBit (w : positive) (n : N)
    | VRecord (fs : Field.fs tags_t v)
    | VHeader (fs : Field.fs tags_t v) (validity : bool)
    | VError (err : option (string tags_t))
    | VMatchKind (mk : P4light.Expr.matchkind).
    (**[]*)

    (** Lvalues. *)
    Inductive lv : Type :=
    | LVVar (x : name tags_t)                 (* Local variables. *)
    | LVMember (arg : lv) (x : string tags_t) (* Member access. *).
    (**[]*)

    (** Evaluated arguments. *)
    Definition argsv : Type := Field.fs tags_t (P4light.paramarg v lv).

    (** A custom induction principle for value. *)
    Section ValueInduction.
      Variable P : v -> Prop.

      Hypothesis HVBool : forall b, P (VBool b).

      Hypothesis HVBit : forall w n, P (VBit w n).

      Hypothesis HVInt : forall w n, P (VInt w n).

      Hypothesis HVRecord : forall fs,
          Field.predfs_data P fs -> P (VRecord fs).

      Hypothesis HVHeader : forall fs b,
          Field.predfs_data P fs -> P (VHeader fs b).

      Hypothesis HVError : forall err, P (VError err).

      Hypothesis HVMatchKind : forall mk, P (VMatchKind mk).

      Definition custom_value_ind : forall v' : v, P v' :=
        fix custom_value_ind (val : v) : P val :=
          let fix fields_ind
                  (flds : Field.fs tags_t v) : Field.predfs_data P flds :=
              match flds as fs return Field.predfs_data P fs with
              | [] => Forall_nil (Field.predf_data P)
              | (_, hfv) as hf :: tf =>
                Forall_cons hf (custom_value_ind hfv) (fields_ind tf)
              end in
          match val as v' return P v' with
          | VBool b  => HVBool b
          | VInt w n => HVInt w n
          | VBit w n => HVBit w n
          | VRecord vs     => HVRecord vs (fields_ind vs)
          | VHeader vs b   => HVHeader vs b (fields_ind vs)
          | VError err     => HVError err
          | VMatchKind mk  => HVMatchKind mk
          end.
    End ValueInduction.

    Section ValueEquality.
      Instance P4StringEquivalence : Equivalence (@P4String.equiv tags_t) :=
        P4String.EquivEquivalence tags_t.
      (**[]*)

      Instance P4StringEqDec : EqDec (string tags_t) (@P4String.equiv tags_t) :=
        P4String.P4StringEqDec tags_t.
      (**[]*)

      (** Computational Value equality *)
      Fixpoint eqbv (v1 v2 : v) : bool :=
        let fix fields_rec (vs1 vs2 : Field.fs tags_t v) : bool :=
            match vs1, vs2 with
            | [],           []           => true
            | (x1, v1)::vs1, (x2, v2)::vs2 => if P4String.equivb x1 x2 then
                                             eqbv v1 v2 && fields_rec vs1 vs2
                                           else false
            | [],            _::_
            | _::_,           []          => false
            end in
        match v1, v2 with
        | VBool b1,       VBool b2       => eqb b1 b2
        | VInt w1 z1,     VInt w2 z2     => (w1 =? w2)%positive &&
                                           (z1 =? z2)%Z
        | VBit w1 n1,     VBit w2 n2     => (w1 =? w2)%positive &&
                                           (n1 =? n2)%N
        | VMatchKind mk1, VMatchKind mk2 => if equiv_dec mk1 mk2
                                           then true
                                           else false
        | VError err1,    VError err2    => if equiv_dec err1 err2
                                           then true
                                           else false
        | VHeader vs1 b1, VHeader vs2 b2 => (eqb b1 b2)%bool && fields_rec vs1 vs2
        | VRecord vs1,    VRecord vs2    => fields_rec vs1 vs2
        | _,              _              => false
        end.
      (**[]*)

      (** Value equivalence relation. *)
      Inductive equivv : v -> v -> Prop :=
      | equivv_bool (b : bool) :
          equivv (VBool b) (VBool b)
      | equivv_int (w : positive) (n : Z) :
          equivv (VInt w n) (VInt w n)
      | equivv_bit (w : positive) (n : N) :
          equivv (VBit w n) (VBit w n)
      | equivv_record (fs1 fs2 : Field.fs tags_t v) :
          Field.relfs equivv fs1 fs2 ->
          equivv (VRecord fs1) (VRecord fs2)
      | equivv_header (fs1 fs2 : Field.fs tags_t v) (b : bool) :
          Field.relfs equivv fs1 fs2 ->
          equivv (VHeader fs1 b) (VHeader fs2 b)
      | equivv_error (err1 err2 : option (string tags_t)) :
          equiv err1 err2 ->
          equivv (VError err1) (VError err2)
      | equivv_matchkind (mk : P4light.Expr.matchkind) :
          equivv (VMatchKind mk) (VMatchKind mk).
      (**[]*)

      (** A custom induction principle for value equivalence. *)
      Section ValueEquivalenceInduction.
        (** An arbitrary predicate. *)
        Variable P : v -> v -> Prop.

        Hypothesis HBool : forall b, P (VBool b) (VBool b).

        Hypothesis HBit : forall w n, P (VBit w n) (VBit w n).

        Hypothesis HInt : forall w z, P (VInt w z) (VInt w z).

        Hypothesis HError : forall err1 err2,
            equiv err1 err2 -> P (VError err1) (VError err2).

        Hypothesis HMatchkind : forall mk, P (VMatchKind mk) (VMatchKind mk).

        Hypothesis HRecord : forall fs1 fs2,
            Field.relfs equivv fs1 fs2 ->
            Field.relfs P fs1 fs2 ->
            P (VRecord fs1) (VRecord fs2).

        Hypothesis HHeader : forall fs1 fs2 b,
            Field.relfs equivv fs1 fs2 ->
            Field.relfs P fs1 fs2 ->
            P (VHeader fs1 b) (VHeader fs2 b).

        (** Custom [eqiuvv] induction principle.
            Do [induction ?H using custom_equivv_ind] *)
        Definition custom_equivv_ind : forall (v1 v2 : v) (H : equivv v1 v2), P v1 v2 :=
          fix vind v1 v2 H :=
            let fix find
                    {vs1 vs2 : Field.fs tags_t v}
                    (HR : Field.relfs equivv vs1 vs2) : Field.relfs P vs1 vs2 :=
                match HR in Forall2 _ v1s v2s return Forall2 (Field.relf P) v1s v2s with
                | Forall2_nil _ => Forall2_nil (Field.relf P)
                | Forall2_cons v1 v2
                               (conj HName Hequivv)
                               Htail => Forall2_cons
                                         v1 v2
                                         (conj
                                            HName
                                            (vind (snd v1) (snd v2) Hequivv))
                                         (find Htail)
                  end in
            match H in (equivv v1' v2') return P v1' v2' with
            | equivv_bool b => HBool b
            | equivv_bit w n => HBit w n
            | equivv_int w z => HInt w z
            | equivv_error err1 err2 H12 => HError err1 err2 H12
            | equivv_matchkind mk => HMatchkind mk
            | equivv_record vs1 vs2 H12 => HRecord vs1 vs2 H12 (find H12)
            | equivv_header vs1 vs2 b H12 => HHeader vs1 vs2 b H12 (find H12)
            end.
        (**[]*)
      End ValueEquivalenceInduction.

      Lemma equivv_reflexive : Reflexive equivv.
      Proof.
        intros v; induction v using custom_value_ind;
          constructor; try reflexivity;
        try (induction fs as [| [x v] vs];
             inversion H; subst; constructor;
             [ unfold Field.predf_data in H2;
               constructor; simpl; try reflexivity; auto
             | apply IHvs; auto]).
      Qed.

      Lemma equivv_symmetric : Symmetric equivv.
      Proof.
        intros v1; induction v1 using custom_value_ind;
          intros [] HEQ; inversion HEQ; clear HEQ; subst;
            constructor; try (symmetry; assumption);
              try (rename fs into fs1; rename fs0 into fs2;
                   generalize dependent fs2;
                   induction fs1 as [| [x1 v1] vs1 IHvs1];
                   intros [| [x2 v2] vs2] HSym;
                   inversion HSym; clear HSym; subst; constructor;
                   inversion H; clear H; subst;
                   [ unfold Field.relf in *; simpl in *;
                     destruct H3; split; try (symmetry; assumption);
                     apply H2; assumption
                   | apply IHvs1; auto ]).
      Qed.

      Lemma equivv_transitive : Transitive equivv.
      Proof.
        intros v1; induction v1 using custom_value_ind; intros v2 v3 H12 H23;
          inversion H12; subst; inversion H23; subst;
            clear H12 H23; constructor;
              try (transitivity err2; auto); try (transitivity mk2; auto);
        try (generalize dependent fs0; generalize dependent fs2;
             rename fs into fs1;
             induction fs1 as [| [x1 v1] vs1 IHvs1];
             intros [| [x2 v2] vs2] H12 [| [x3 v3] vs3] H23;
             inversion H12; subst; inversion H23; subst;
             clear H12 H23; constructor; inversion H; subst; clear H;
             [ unfold Field.relf in *; simpl in *;
               unfold Field.predf_data;
               destruct H3; destruct H4;
               pose proof (H2 v2 v3) as H23; try split; auto;
               transitivity x2; auto
             | apply IHvs1 with vs2; auto]).
      Qed.

      Instance ValueEquivalence : Equivalence equivv.
      Proof.
        constructor; [ apply equivv_reflexive
                     | apply equivv_symmetric
                     | apply equivv_transitive].
      Defined.

      Lemma equivv_eqbv : forall v1 v2 : v, equivv v1 v2 -> eqbv v1 v2 = true.
      Proof.
        intros v1 v2 H.
        induction H using custom_equivv_ind;
          simpl in *; try rewrite eqb_reflx; try rewrite Pos.eqb_refl; simpl; auto.
        - apply N.eqb_refl.
        - apply Z.eqb_refl.
        - unfold equiv in H. inversion H; subst.
          + destruct (equiv_dec None None) as [H' | H'];
              unfold equiv, complement in *; try contradiction; auto.
          + destruct (equiv_dec (Some a1) (Some a2)) as [H' | H'];
              unfold equiv, complement in *; try inversion H';
                try contradiction; auto.
        - destruct (equiv_dec mk mk) as [H' | H'];
            unfold equiv, complement in *; try contradiction; auto.
        - clear H. induction H0; auto.
          destruct x as [x1 v1]; destruct y as [x2 v2];
            inversion H; simpl in *.
          pose proof P4String.equiv_reflect x1 x2 as Hx.
          inversion Hx; subst; try contradiction.
          rewrite H2; auto.
        - clear H. induction H0; auto.
          destruct x as [x1 v1]; destruct y as [x2 v2];
            inversion H; simpl in *.
          pose proof P4String.equiv_reflect x1 x2 as Hx.
          inversion Hx; subst; try contradiction.
          rewrite H2; auto.
      Qed.

      Lemma eqbv_equivv : forall v1 v2 : v, eqbv v1 v2 = true -> equivv v1 v2.
      Proof.
        induction v1 using custom_value_ind; intros [] Heqbv; simpl in *;
          try discriminate.
        - apply eqb_prop in Heqbv; subst; constructor.
        - apply andb_prop in Heqbv as [Hw Hn];
            apply Peqb_true_eq in Hw; apply N.eqb_eq in Hn;
              subst; constructor.
        - apply andb_prop in Heqbv as [Hw Hn];
            apply Peqb_true_eq in Hw; apply Z.eqb_eq in Hn;
              subst; constructor.
        - constructor. generalize dependent fs0.
          induction fs as [| [x1 v1] vs1 IHvs1]; intros [| [x2 v2] vs2] IH;
            inversion IH; subst; inversion H; subst; clear IH H; simpl in *;
              constructor; auto; simpl in *;
                destruct (P4String.equivb x1 x2) eqn:Hx;
                destruct (eqbv v1 v2) eqn:Hv; simpl in *; try discriminate.
          + split; simpl; auto.
            pose proof P4String.equiv_reflect x1 x2 as H';
              inversion H'; subst; auto.
            rewrite Hx in H. discriminate.
          + apply IHvs1; auto.
        - apply andb_true_iff in Heqbv as [Hb Hfs].
          apply eqb_prop in Hb; subst. constructor.
          generalize dependent fs0.
          induction fs as [| [x1 v1] vs1 IHvs1]; intros [| [x2 v2] vs2] IH;
            inversion IH; subst; inversion H; subst; clear IH H; simpl in *;
              constructor; auto; simpl in *;
                destruct (P4String.equivb x1 x2) eqn:Hx;
                destruct (eqbv v1 v2) eqn:Hv; simpl in *; try discriminate.
          + split; simpl; auto.
            pose proof P4String.equiv_reflect x1 x2 as H';
              inversion H'; subst; auto.
            rewrite Hx in H. discriminate.
          + apply IHvs1; auto.
        - destruct (equiv_dec err err0) as [H | H];
            try discriminate; constructor; auto.
        - destruct (equiv_dec mk mk0) as [H | H];
            try discriminate; inversion H; constructor; auto.
      Qed.

      Lemma equivv_eqbv_iff : forall v1 v2 : v, equivv v1 v2 <-> eqbv v1 v2 = true.
      Proof.
        intros v1 v2; split; [apply equivv_eqbv | apply eqbv_equivv].
      Qed.

      Lemma equivv_reflect : forall v1 v2, reflect (equivv v1 v2) (eqbv v1 v2).
      Proof.
        intros v1 v2.
        destruct (eqbv v1 v2) eqn:Heqbv; constructor.
        - apply eqbv_equivv; assumption.
        - intros H. apply equivv_eqbv in H.
          rewrite H in Heqbv. discriminate.
      Qed.

      Lemma equivv_dec : forall v1 v2 : v,
          equivv v1 v2 \/ ~ equivv v1 v2.
      Proof.
        intros v1 v2. pose proof equivv_reflect v1 v2 as H.
        inversion H; subst; auto.
      Qed.
    End ValueEquality.
  End Values.

  Arguments VBool {_}.
  Arguments VInt {_}.
  Arguments VBit {_}.
  Arguments VRecord {_}.
  Arguments VHeader {_}.
  Arguments VError {_}.
  Arguments VMatchKind {_}.
  Arguments LVVar {_}.
  Arguments LVMember {_}.

  Module ValueNotations.
    Notation "'*{' val '}*'" := val (val custom p4value at level 99).
    Notation "( x )" := x (in custom p4value, x at level 99).
    Notation "x" := x (in custom p4value at level 0, x constr at level 0).
    Notation "'TRUE'" := (VBool true) (in custom p4value at level 0).
    Notation "'FALSE'" := (VBool false) (in custom p4value at level 0).
    Notation "'VBOOL' b" := (VBool b) (in custom p4value at level 0).
    Notation "w 'VW' n" := (VBit w n) (in custom p4value at level 0).
    Notation "w 'VS' n" := (VInt w n) (in custom p4value at level 0).
    Notation "'REC' { fs }" := (VRecord fs)
                                 (in custom p4value at level 6,
                                     no associativity).
    Notation "'HDR' { fs } 'VALID' ':=' b" := (VHeader fs b)
                                 (in custom p4value at level 6,
                                     no associativity).
    Notation "'ERROR' x" := (VError x) (in custom p4value at level 0).
    Notation "'MATCHKIND' mk"
      := (VMatchKind mk)
           (in custom p4value at level 0, mk custom p4matchkind).
  End ValueNotations.

  Module LValueNotations.
    Notation "'l{' lval '}l'" := lval (lval custom p4lvalue at level 99).
    Notation "( x )" := x (in custom p4lvalue, x at level 99).
    Notation "x" := x (in custom p4lvalue at level 0, x constr at level 0).
    Notation "'VAR' x" := (LVVar x) (in custom p4lvalue at level 0).
    Notation "lval 'DOT' x"
      := (LVMember lval x) (in custom p4lvalue at level 1,
                               lval custom p4lvalue).
  End LValueNotations.
End Value.

Module Step.
  Module P := P4light.
  Module E := P.Expr.
  Module ST := P.Stmt.
  Module F := P.F.
  Module V := Value.

  Import ST.StmtNotations.
  Import V.ValueNotations.
  Import V.LValueNotations.

  (** Statement signals. *)
  Inductive signal (tags_t : Type) : Type :=
  | SIG_Cont                           (* continue *)
  | SIG_Exit                           (* exit *)
  | SIG_Rtrn (v : option (V.v tags_t)) (* return *).

  Arguments SIG_Cont {_}.
  Arguments SIG_Exit {_}.
  Arguments SIG_Rtrn {_}.

  Notation "x"
    := x (in custom p4evalsignal at level 0, x constr at level 0).
  Notation "'C'" := SIG_Cont (in custom p4evalsignal at level 0).
  Notation "'X'" := SIG_Exit (in custom p4evalsignal at level 0).
  Notation "'R' 'of' v ?"
    := (SIG_Rtrn v) (in custom p4evalsignal at level 0).
  Notation "'Void'" := (SIG_Rtrn None) (in custom p4evalsignal at level 0).
  Notation "'Fruit' v" := (SIG_Rtrn (Some v)) (in custom p4evalsignal at level 0).

  Import Env.EnvNotations.

  Section Step.
    Context {tags_t : Type}.

    (** Unsigned integer binary operations. *)
    Definition eval_bit_binop
               (op : E.bop) (w : positive)
               (n1 n2 : N) : option (V.v tags_t) :=
      match op with
      | E.Plus     => Some (V.VBit w (BitArith.plus_mod w n1 n2))
      | E.PlusSat  => Some (V.VBit w (BitArith.plus_sat w n1 n2))
      | E.Minus    => Some (V.VBit w (BitArith.minus_mod w n1 n2))
      | E.MinusSat => Some (V.VBit w (N.sub n1 n2))
      | E.Shl      => Some (V.VBit w (N.shiftl n1 n2))
      | E.Shr      => Some (V.VBit w (BitArith.shift_right w n1 n2))
      | E.Le       => Some (V.VBool (N.leb n1 n2))
      | E.Ge       => Some (V.VBool (N.leb n2 n1))
      | E.Lt       => Some (V.VBool (N.ltb n1 n2))
      | E.Gt       => Some (V.VBool (N.ltb n2 n1))
      | E.Eq       => Some (V.VBool (N.eqb n1 n2))
      | E.NotEq    => Some (V.VBool (negb (N.eqb n1 n2)))
      | E.BitAnd   => Some (V.VBit w (BitArith.bit_and w n1 n2))
      | E.BitXor   => Some (V.VBit w (BitArith.bit_xor w n1 n2))
      | E.BitOr    => Some (V.VBit w (BitArith.bit_or  w n1 n2))
      | E.PlusPlus
      | E.And
      | E.Or       => None
      end.
    (**[]*)

    (** Signed integer binary operations. *)
    Definition eval_int_binop
               (op : E.bop) (w : positive)
               (z1 z2 : Z) : option (V.v tags_t) :=
      match op with
      | E.Plus     => Some (V.VInt w (IntArith.plus_mod w z1 z2))
      | E.PlusSat  => Some (V.VInt w (IntArith.plus_sat w z1 z2))
      | E.Minus    => Some (V.VInt w (IntArith.minus_mod w z1 z2))
      | E.MinusSat => Some (V.VInt w (IntArith.minus_sat w z1 z2))
      | E.Shl      => Some (V.VInt w (IntArith.shift_left w z1 z2))
      | E.Shr      => Some (V.VInt w (IntArith.shift_right w z1 z2))
      | E.Le       => Some (V.VBool (Z.leb z1 z2))
      | E.Ge       => Some (V.VBool (Z.leb z2 z1))
      | E.Lt       => Some (V.VBool (Z.ltb z1 z2))
      | E.Gt       => Some (V.VBool (Z.ltb z2 z1))
      | E.Eq       => Some (V.VBool (Z.eqb z1 z2))
      | E.NotEq    => Some (V.VBool (negb (Z.eqb z1 z2)))
      | E.BitAnd   => Some (V.VInt w (IntArith.bit_and w z1 z2))
      | E.BitXor   => Some (V.VInt w (IntArith.bit_xor w z1 z2))
      | E.BitOr    => Some (V.VInt w (IntArith.bit_or  w z1 z2))
      | E.PlusPlus
      | E.And
      | E.Or       => None
      end.
    (**[]*)

    (** Boolean binary operations. *)
    Definition eval_bool_binop (op : E.bop) (b1 b2 : bool) : option bool :=
      match op with
      | E.Eq    => Some (eqb b1 b2)
      | E.NotEq => Some (negb (eqb b1 b2))
      | E.And   => Some (b1 && b2)
      | E.Or    => Some (b1 || b2)
      | _       => None
      end.

    (** Header operations. *)
    Definition eval_hdr_op
               (op : E.hdr_op) (vs : F.fs tags_t (V.v tags_t))
               (b : bool) : V.v tags_t :=
      match op with
      | E.HOIsValid => *{ VBOOL b }*
      | E.HOSetValid => *{ HDR { vs } VALID:=true }*
      | E.HOSetInValid => *{ HDR { vs } VALID:=false }*
      end.
    (**[]*)

    (** Variable to Value mappings. *)
    Definition epsilon : Type := Env.t (name tags_t) (V.v tags_t).

    (* TODO: Handle Errors! *)
    Inductive expr_big_step (ϵ : epsilon) : E.e tags_t -> V.v tags_t -> Prop :=
    (* Literals. *)
    | ebs_bool (b : bool) (i : tags_t) :
        ⟨ ϵ, BOOL b @ i ⟩ ⇓ VBOOL b
    | ebs_bit (w : positive) (n : N) (i : tags_t) :
        ⟨ ϵ, w W n @ i ⟩ ⇓ w VW n
    | ebs_int (w : positive) (z : Z) (i : tags_t) :
        ⟨ ϵ, w S z @ i ⟩ ⇓ w VS z
    | ebs_var (x : name tags_t) (τ : E.t tags_t) (i : tags_t) (v : V.v tags_t) :
        ϵ x = Some v ->
        ⟨ ϵ, Var x:τ @ i ⟩ ⇓ v
    | ebs_error (err : option (string tags_t)) (i : tags_t) :
        ⟨ ϵ, Error err @ i ⟩ ⇓ ERROR err
    | ebs_matchkind (mk : E.matchkind) (i : tags_t) :
        ⟨ ϵ, Matchkind mk @ i ⟩ ⇓ MATCHKIND mk
    (* Unary Operations. *)
    | ebs_not (e : E.e tags_t) (i : tags_t) (b b' : bool) :
        negb b = b' ->
        ⟨ ϵ, e ⟩ ⇓ VBOOL b ->
        ⟨ ϵ, UOP ! e:Bool @ i ⟩ ⇓ VBOOL b'
    | ebs_bitnot (e : E.e tags_t) (i : tags_t)
                 (w : positive) (n n' : N) :
        BitArith.neg w n = n' ->
        ⟨ ϵ, e ⟩ ⇓ w VW n ->
        ⟨ ϵ, UOP ~ e:bit<w> @ i ⟩ ⇓ w VW n'
    | ebs_uminus (e : E.e tags_t) (i : tags_t)
                 (w : positive) (z z' : Z) :
        IntArith.neg w z = z' ->
        ⟨ ϵ, e ⟩ ⇓ w VS z ->
        ⟨ ϵ, UOP - e:int<w> @ i ⟩ ⇓ w VS z'
    (* Binary Operations. *)
    | ebs_bop_bit (e1 e2 : E.e tags_t) (op : E.bop) (v : V.v tags_t)
                  (i : tags_t) (w : positive) (n1 n2 : N) :
        eval_bit_binop op w n1 n2 = Some v ->
        ⟨ ϵ, e1 ⟩ ⇓ w VW n1 ->
        ⟨ ϵ, e2 ⟩ ⇓ w VW n2 ->
        ⟨ ϵ, BOP e1:bit<w> op e2:bit<w> @ i ⟩ ⇓ v
    | ebs_plusplus (e1 e2 : E.e tags_t) (i : tags_t)
                   (w w1 w2 : positive) (n n1 n2 : N) :
        (w1 + w2)%positive = w ->
        BitArith.bit_concat w2 n1 n2 = n ->
        ⟨ ϵ, e1 ⟩ ⇓ w1 VW n1 ->
        ⟨ ϵ, e2 ⟩ ⇓ w2 VW n2 ->
        ⟨ ϵ, BOP e1:bit<w1> ++ e2:bit<w2> @ i ⟩ ⇓ w VW n
    | ebs_bop_int (e1 e2 : E.e tags_t) (op : E.bop) (v : V.v tags_t)
                  (i : tags_t) (w : positive) (z1 z2 : Z) :
        eval_int_binop op w z1 z2 = Some v ->
        ⟨ ϵ, e1 ⟩ ⇓ w VS z1 ->
        ⟨ ϵ, e2 ⟩ ⇓ w VS z2 ->
        ⟨ ϵ, BOP e1:int<w> op e2:int <w> @ i ⟩ ⇓ v
    | ebs_bop_bool (e1 e2 : E.e tags_t) (op : E.bop)
                   (i : tags_t) (b b1 b2 : bool) :
        eval_bool_binop op b1 b2 = Some b ->
        ⟨ ϵ, e1 ⟩ ⇓ VBOOL b1 ->
        ⟨ ϵ, e2 ⟩ ⇓ VBOOL b2 ->
        ⟨ ϵ, BOP e1:Bool op e2:Bool @ i⟩ ⇓ VBOOL b
    | ebs_eq (e1 e2 : E.e tags_t) (τ1 τ2 : E.t tags_t)
                  (i : tags_t) (v1 v2 : V.v tags_t) (b : bool) :
        V.eqbv tags_t v1 v2 = b ->
        ⟨ ϵ, e1 ⟩ ⇓ v1 ->
        ⟨ ϵ, e2 ⟩ ⇓ v2 ->
        ⟨ ϵ, BOP e1:τ1 == e2:τ2 @ i ⟩ ⇓ VBOOL b
    | ebs_neq (e1 e2 : E.e tags_t) (τ1 τ2 : E.t tags_t)
              (i : tags_t) (v1 v2 : V.v tags_t) (b : bool) :
        negb (V.eqbv tags_t v1 v2) = b ->
        ⟨ ϵ, e1 ⟩ ⇓ v1 ->
        ⟨ ϵ, e2 ⟩ ⇓ v2 ->
        ⟨ ϵ, BOP e1:τ1 != e2:τ2 @ i ⟩ ⇓ VBOOL b
    (* Structs *)
    | ebs_rec_mem (e : E.e tags_t) (x : string tags_t) (i : tags_t)
                  (tfs : F.fs tags_t (E.t tags_t))
                  (vfs : F.fs tags_t (V.v tags_t)) (v : V.v tags_t) :
        F.get x vfs = Some v ->
        ⟨ ϵ, e ⟩ ⇓ REC { vfs } ->
        ⟨ ϵ, Mem e:rec { tfs } dot x @ i ⟩ ⇓ v
    | ebs_hdr_mem (e : E.e tags_t) (x : string tags_t) (i : tags_t)
                  (tfs : F.fs tags_t (E.t tags_t)) (b : bool)
                  (vfs : F.fs tags_t (V.v tags_t)) (v : V.v tags_t) :
        F.get x vfs = Some v ->
        ⟨ ϵ, e ⟩ ⇓ HDR { vfs } VALID:=b ->
        ⟨ ϵ, Mem e:hdr { tfs } dot x @ i ⟩ ⇓ v
    | ebs_rec_lit (efs : F.fs tags_t (E.t tags_t * E.e tags_t))
                  (i : tags_t) (vfs : F.fs tags_t (V.v tags_t)) :
        F.relfs
          (fun te v =>
             let e := snd te in ⟨ ϵ, e ⟩ ⇓ v) efs vfs ->
        ⟨ ϵ, rec { efs } @ i ⟩ ⇓ REC { vfs }
    | ebs_hdr_lit (efs : F.fs tags_t (E.t tags_t * E.e tags_t))
                  (e : E.e tags_t) (i : tags_t) (b : bool)
                  (vfs : F.fs tags_t (V.v tags_t)) :
        F.relfs
          (fun te v =>
             let e := snd te in ⟨ ϵ, e ⟩ ⇓ v) efs vfs ->
        ⟨ ϵ, e ⟩ ⇓ VBOOL b ->
        ⟨ ϵ, hdr { efs } valid:=e @ i ⟩ ⇓ HDR { vfs } VALID:=b
    | ebs_hdr_op  (op : E.hdr_op) (e : E.e tags_t) (i : tags_t)
                  (v : V.v tags_t) (vs : F.fs tags_t (V.v tags_t)) (b : bool) :
        eval_hdr_op op vs b = v ->
        ⟨ ϵ, e ⟩ ⇓ HDR { vs } VALID:=b ->
        ⟨ ϵ, H op e @ i ⟩ ⇓ v
    where "⟨ ϵ , e ⟩ ⇓ v" := (expr_big_step ϵ e v).
    (**[]*)

    (** A custom induction principle for
        the expression big-step relation. *)
    Section ExprEvalInduction.
      Variable P : epsilon -> E.e tags_t -> V.v tags_t -> Prop.

      Hypothesis HBool : forall ϵ b i, P ϵ <{ BOOL b @ i }> *{ VBOOL b }*.

      Hypothesis HBit : forall ϵ w n i, P ϵ <{ w W n @ i }> *{ w VW n }*.

      Hypothesis HInt : forall ϵ w z i, P ϵ <{ w S z @ i }> *{ w VS z }*.

      Hypothesis HVar : forall ϵ x τ i v,
          ϵ x = Some v ->
          P ϵ <{ Var x:τ @ i }> v.

      Hypothesis HError : forall ϵ err i,
          P ϵ <{ Error err @ i }> *{ ERROR err }*.

      Hypothesis HMatchkind : forall ϵ mk i,
          P ϵ <{ Matchkind mk @ i }> *{ MATCHKIND mk }*.

      Hypothesis HNot : forall ϵ e i b b',
          negb b = b' ->
          ⟨ ϵ, e ⟩ ⇓ VBOOL b ->
          P ϵ e *{ VBOOL b }* ->
          P ϵ <{ UOP ! e:Bool @ i }> *{ VBOOL b'}*.

      Hypothesis HBitNot : forall ϵ e i w n n',
          BitArith.neg w n = n' ->
          ⟨ ϵ, e ⟩ ⇓ w VW n ->
          P ϵ e *{ w VW n }* ->
          P ϵ <{ UOP ~ e:bit<w> @ i }> *{ w VW n' }*.

      Hypothesis HUMinus : forall ϵ e i w z z',
          IntArith.neg w z = z' ->
          ⟨ ϵ, e ⟩ ⇓ w VS z ->
          P ϵ e *{ w VS z }* ->
          P ϵ <{ UOP - e:int<w> @ i }> *{ w VS z' }*.

      Hypothesis HBOPBit : forall ϵ e1 e2 op v i w n1 n2,
          eval_bit_binop op w n1 n2 = Some v ->
          ⟨ ϵ, e1 ⟩ ⇓ w VW n1 ->
          P ϵ e1 *{ w VW n1 }* ->
          ⟨ ϵ, e2 ⟩ ⇓ w VW n2 ->
          P ϵ e2 *{ w VW n2 }* ->
          P ϵ <{ BOP e1:bit<w> op e2:bit<w> @ i }> v.

      Hypothesis HPlusPlus : forall ϵ e1 e2 i w w1 w2 n n1 n2,
        (w1 + w2)%positive = w ->
        BitArith.bit_concat w2 n1 n2 = n ->
        ⟨ ϵ, e1 ⟩ ⇓ w1 VW n1 ->
        P ϵ e1 *{ w1 VW n1 }* ->
        ⟨ ϵ, e2 ⟩ ⇓ w2 VW n2 ->
        P ϵ e2 *{ w2 VW n2 }* ->
        P ϵ <{ BOP e1:bit<w1> ++ e2:bit<w2> @ i }> *{ w VW n }*.

      Hypothesis HBOPInt : forall ϵ e1 e2 op v i w z1 z2,
        eval_int_binop op w z1 z2 = Some v ->
        ⟨ ϵ, e1 ⟩ ⇓ w VS z1 ->
        P ϵ e1 *{ w VS z1 }* ->
        ⟨ ϵ, e2 ⟩ ⇓ w VS z2 ->
        P ϵ e2 *{ w VS z2 }* ->
        P ϵ <{ BOP e1:int<w> op e2:int<w> @ i }> v.

      Hypothesis HBOPBool : forall ϵ e1 e2 op i b b1 b2,
        eval_bool_binop op b1 b2 = Some b ->
        ⟨ ϵ, e1 ⟩ ⇓ VBOOL b1 ->
        P ϵ e1 *{ VBOOL b1 }* ->
        ⟨ ϵ, e2 ⟩ ⇓ VBOOL b2 ->
        P ϵ e2 *{ VBOOL b2 }* ->
        P ϵ <{ BOP e1:Bool op e2:Bool @ i }> *{VBOOL b}*.

      Hypothesis HEq : forall ϵ e1 e2 τ1 τ2 i v1 v2 b,
          V.eqbv tags_t v1 v2 = b ->
          ⟨ ϵ, e1 ⟩ ⇓ v1 ->
          P ϵ e1 v1 ->
          ⟨ ϵ, e2 ⟩ ⇓ v2 ->
          P ϵ e2 v2 ->
          P ϵ <{ BOP e1:τ1 == e2:τ2 @ i }> *{ VBOOL b }*.

      Hypothesis HNeq : forall ϵ e1 e2 τ1 τ2 i v1 v2 b,
          negb (V.eqbv tags_t v1 v2) = b ->
          ⟨ ϵ, e1 ⟩ ⇓ v1 ->
          P ϵ e1 v1 ->
          ⟨ ϵ, e2 ⟩ ⇓ v2 ->
          P ϵ e2 v2 ->
          P ϵ <{ BOP e1:τ1 != e2:τ2 @ i }> *{ VBOOL b }*.

      Hypothesis HRecMem : forall ϵ e x i ts vs v,
          F.get x vs = Some v ->
          ⟨ ϵ, e ⟩ ⇓ REC { vs } ->
          P ϵ e *{ REC { vs } }* ->
          P ϵ <{ Mem e:rec { ts } dot x @ i }> v.

      Hypothesis HHdrMem : forall ϵ e x i ts b vs v,
          F.get x vs = Some v ->
          ⟨ ϵ, e ⟩ ⇓ HDR { vs } VALID:=b ->
          P ϵ e *{ HDR { vs } VALID:=b }* ->
          P ϵ <{ Mem e:hdr { ts } dot x @ i }> v.

      Hypothesis HRecLit : forall ϵ efs i vfs,
          F.relfs
            (fun te v =>
               let e := snd te in ⟨ ϵ, e ⟩ ⇓ v) efs vfs ->
          F.relfs (fun te v => let e := snd te in P ϵ e v) efs vfs ->
          P ϵ <{ rec { efs } @ i }> *{ REC { vfs } }*.

      Hypothesis HHdrLit : forall ϵ efs e i b vfs,
          F.relfs
            (fun te v =>
               let e := snd te in ⟨ ϵ, e ⟩ ⇓ v) efs vfs ->
          F.relfs (fun te v => let e := snd te in P ϵ e v) efs vfs ->
          ⟨ ϵ, e ⟩ ⇓ VBOOL b ->
          P ϵ e *{ VBOOL b }* ->
          P ϵ <{ hdr { efs } valid:=e @ i }> *{ HDR { vfs } VALID:=b }*.

      Hypothesis HHdrOp : forall ϵ op e i v vs b,
          eval_hdr_op op vs b = v ->
          ⟨ ϵ, e ⟩ ⇓ HDR { vs } VALID:=b ->
          P ϵ e *{ HDR { vs } VALID:=b }* ->
          P ϵ <{ H op e @ i }> v.

      (** Custom induction principle for
          the expression big-step relation.
          [Do induction ?H using custom_expr_big_step_ind]. *)
      Definition custom_expr_big_step :
        forall (ϵ : epsilon) (e : E.e tags_t)
          (v : V.v tags_t) (Hy : ⟨ ϵ, e ⟩ ⇓ v), P ϵ e v :=
        fix ebsind ϵ e v Hy :=
          let fix fsind
                  {efs : F.fs tags_t (E.t tags_t * E.e tags_t)}
                  {vfs : F.fs tags_t (V.v tags_t)}
                  (HRs : F.relfs
                           (fun te v =>
                              let e := snd te in
                              ⟨ ϵ , e ⟩ ⇓ v) efs vfs)
                  : F.relfs
                      (fun te v => let e := snd te in P ϵ e v)
                      efs vfs :=
                  match HRs
                        in (Forall2 _ es vs)
                        return
                        (Forall2
                           (F.relf (fun te v => let e := snd te in P ϵ e v))
                           es vs) with
                  | Forall2_nil _ => Forall2_nil
                                      (F.relf (fun te v => let e := snd te in P ϵ e v))
                  | Forall2_cons te v
                                 (conj Hname Hhead)
                                 Htail => Forall2_cons
                                           te v
                                           (conj Hname (ebsind ϵ _ _ Hhead))
                                           (fsind Htail)
                  end in
          match Hy in (⟨ _, e' ⟩ ⇓ v') return P ϵ e' v' with
          | ebs_bool _ b i => HBool ϵ b i
          | ebs_bit _ w n i => HBit ϵ w n i
          | ebs_int _ w z i => HInt ϵ w z i
          | ebs_var _ x τ i v Hx => HVar ϵ x τ i v Hx
          | ebs_error _ err i => HError ϵ err i
          | ebs_matchkind _ mk i => HMatchkind ϵ mk i
          | ebs_not _ e i b b' Hnot He => HNot ϵ e i b b' Hnot
                                              He (ebsind ϵ e *{ VBOOL b }* He)
          | ebs_bitnot _ e i w n n'
                       Hnot He => HBitNot ϵ e i w n n' Hnot
                                         He (ebsind ϵ e *{ w VW n }* He)
          | ebs_uminus _ e i w z z'
                       Hneg He => HUMinus ϵ e i w z z' Hneg
                                         He (ebsind ϵ e *{ w VS z }* He)
          | ebs_bop_bit _ e1 e2 op v i w n1 n2
                        Hv He1 He2 => HBOPBit ϵ e1 e2 op v i w n1 n2 Hv
                                             He1 (ebsind ϵ e1 *{ w VW n1 }* He1)
                                             He2 (ebsind ϵ e2 *{ w VW n2 }* He2)
          | ebs_plusplus _ e1 e2 i w w1 w2 n n1 n2
                         Hw Hconcat He1 He2 => HPlusPlus ϵ e1 e2 i w w1 w2 n n1 n2
                                                        Hw Hconcat
                                                        He1 (ebsind ϵ e1 *{ w1 VW n1 }* He1)
                                                        He2 (ebsind ϵ e2 *{ w2 VW n2 }* He2)
          | ebs_bop_int _ e1 e2 op v i w z1 z2
                        Hv He1 He2 => HBOPInt ϵ e1 e2 op v i w z1 z2 Hv
                                             He1 (ebsind ϵ e1 *{ w VS z1 }* He1)
                                             He2 (ebsind ϵ e2 *{ w VS z2 }* He2)
          | ebs_bop_bool _ e1 e2 op i b b1 b2
                        Hb He1 He2 => HBOPBool ϵ e1 e2 op i b b1 b2 Hb
                                             He1 (ebsind ϵ e1 *{ VBOOL b1 }* He1)
                                             He2 (ebsind ϵ e2 *{ VBOOL b2 }* He2)
          | ebs_eq _ e1 e2 τ1 τ2 i v1 v2 b
                   Hb He1 He2 => HEq ϵ e1 e2 τ1 τ2 i v1 v2 b Hb
                                    He1 (ebsind ϵ e1 v1 He1)
                                    He2 (ebsind ϵ e2 v2 He2)
          | ebs_neq _ e1 e2 τ1 τ2 i v1 v2 b
                    Hb He1 He2 => HNeq ϵ e1 e2 τ1 τ2 i v1 v2 b Hb
                                     He1 (ebsind ϵ e1 v1 He1)
                                     He2 (ebsind ϵ e2 v2 He2)
          | ebs_hdr_mem _ e x i ts b vs v
                        Hget He => HHdrMem ϵ e x i ts b vs v Hget
                                          He (ebsind ϵ e *{ HDR { vs } VALID:=b }* He)
          | ebs_rec_mem _ e x i ts vs v
                        Hget He => HRecMem ϵ e x i ts vs v Hget
                                          He (ebsind ϵ e *{ REC { vs } }* He)
          | ebs_hdr_op _ op e i v vs b
                       Hv He => HHdrOp ϵ op e i v vs b Hv
                                      He (ebsind ϵ e *{ HDR { vs } VALID:=b }* He)
          | ebs_rec_lit _ es i vs HR => HRecLit ϵ es i vs HR (fsind HR)
          | ebs_hdr_lit _ es e i b vs
                        HR He => HHdrLit ϵ es e i b vs
                                        HR (fsind HR)
                                        He (ebsind ϵ e *{ VBOOL b }* He)
          end.
      (**[]*)
    End ExprEvalInduction.

    Inductive lvalue_big_step (ϵ : epsilon) : E.e tags_t -> V.lv tags_t -> Prop :=
    | lvbs_var (x : name tags_t) (τ : E.t tags_t) (i : tags_t) :
        ⦑ ϵ, Var x:τ @ i ⦒ ⇓ VAR x
    | lvbs_rec_member (e : E.e tags_t) (x : string tags_t)
                  (tfs : F.fs tags_t (E.t tags_t))
                  (i : tags_t) (lv : V.lv tags_t) :
        ⦑ ϵ, e ⦒ ⇓ lv ->
        ⦑ ϵ, Mem e:rec { tfs } dot x @ i ⦒ ⇓ lv DOT x
    | lvbs_hdr_member (e : E.e tags_t) (x : string tags_t)
                      (tfs : F.fs tags_t (E.t tags_t))
                      (i : tags_t) (lv : V.lv tags_t):
        ⦑ ϵ, e ⦒ ⇓ lv ->
        ⦑ ϵ, Mem e:hdr { tfs } dot x @ i ⦒ ⇓ lv DOT x
    where "⦑ ϵ , e ⦒ ⇓ lv" := (lvalue_big_step ϵ e lv).
    (**[]*)

    Instance P4NameEquivalence : Equivalence (equivn tags_t) :=
      NameEquivalence tags_t.
    (**[]*)

    Instance P4NameEqDec : EqDec (name tags_t) (equivn tags_t) :=
      NameEqDec tags_t.
    (**[]*)

    Definition bare (x : string tags_t) : name tags_t :=
      Typed.BareName x.
    (**[]*)

    (** Function declarations and closures. *)
    Inductive fdecl : Type :=
    | FDecl (closure : epsilon) (fs : fenv) (ins : ienv)
            (signature : E.arrowT tags_t) (body : ST.s tags_t)
    with fenv : Type :=
    | FEnv (fs : Env.t (name tags_t) fdecl)
    (** Instances and Environment. *)
    with inst : Type :=
    | CInst (closure : epsilon) (fs : fenv) (ins : ienv)
            (params : E.params tags_t) (* apply block parameters *)
            (apply_blk : ST.s tags_t)  (* control apply block *)
    with ienv : Type :=
    | IEnv (ins : Env.t (name tags_t) inst).
    (**[]*)

    (* tables can only be applied in a control apply block.
       apply for tables takes "keys" as an argument,
       but there are no syntactic keys in table invocation.
       need control plane configuration for table invocation.
       control plane config: maps table names to match-action tables.
       match-action tables are a mapping from key-values "p4 values" wink wink
       to an action call *)

    (** Function lookup. *)
    Definition lookup '(FEnv fs : fenv) : name tags_t -> option fdecl := fs.

    (** Bind a function declaration to an environment. *)
    Definition update '(FEnv fs : fenv) (x : name tags_t) (d : fdecl) : fenv :=
      FEnv !{ x ↦ d ;; fs }!.
    (**[]*)

    (** Instance lookup. *)
    Definition ilookup '(IEnv fs : ienv) : name tags_t -> option inst := fs.

    (** Bind a function declaration to an environment. *)
    Definition iupdate '(IEnv fs : ienv) (x : name tags_t) (d : inst) : ienv :=
      IEnv !{ x ↦ d ;; fs }!.
    (**[]*)

    (** Lookup an lvalue. *)
    Fixpoint lv_lookup (ϵ : epsilon) (lv : V.lv tags_t) : option (V.v tags_t) :=
      match lv with
      | l{ VAR x }l => ϵ x
      | l{ lv DOT x }l =>
        (* TODO: use monadic bind. *)
        match lv_lookup ϵ lv with
        | None => None
        | Some *{ REC { fs } }*
        | Some *{ HDR { fs } VALID:=_ }* => F.get x fs
        | Some _ => None
        end
      end.
    (**[]*)

    (** Updating an lvalue in an environment. *)
    Fixpoint lv_update (lv : V.lv tags_t) (v : V.v tags_t) (ϵ : epsilon) : epsilon :=
      match lv with
      | l{ VAR x }l    => !{ x ↦ v ;; ϵ }!
      | l{ lv DOT x }l =>
        match lv_lookup ϵ lv with
        | Some *{ REC { vs } }* => lv_update lv (V.VRecord (F.update x v vs)) ϵ
        | Some *{ HDR { vs } VALID:=b }* =>
          lv_update lv (V.VHeader (F.update x v vs) b) ϵ
        | Some _ => ϵ
        | None => ϵ
        end
      end.
    (**[]*)

    (** Create a new environment
        from a closure environment where
        values of [In] args are substituted
        into the function parameters. *)
    Definition copy_in
               (argsv : V.argsv tags_t)
               (ϵcall : epsilon) : epsilon -> epsilon :=
      F.fold (fun x arg ϵ =>
                let x' := bare x in
                match arg with
                | P.PAIn v     => !{ x' ↦ v ;; ϵ }!
                | P.PAInOut lv => match lv_lookup ϵcall lv with
                                 | None   => ϵ
                                 | Some v => !{ x' ↦ v ;; ϵ }!
                                end
                | P.PAOut _    => ϵ
                end) argsv.
    (**[]*)

    (** Update call-site environment with
        out variables from function call evaluation. *)
    Definition copy_out
               (argsv : V.argsv tags_t)
               (ϵf : epsilon) : epsilon -> epsilon :=
      F.fold (fun x arg ϵ =>
                let x' := bare x in
                match arg with
                | P.PAIn _ => ϵ
                | P.PAOut lv
                | P.PAInOut lv =>
                  match ϵf x' with
                  | None   => ϵ
                  | Some v => lv_update lv v ϵ
                  end
                end) argsv.
    (**[]*)

    (** Evidence that control-flow
        is interrupted by an exit or return statement. *)
    Inductive interrupt : signal tags_t -> Prop :=
    | interrupt_exit : interrupt SIG_Exit
    | interrupt_rtrn (vo : option (V.v tags_t)) : interrupt (SIG_Rtrn vo).
    (**[]*)

    (** Intial/Default value from a type. *)
    Fixpoint vdefault (τ : E.t tags_t) : V.v tags_t :=
      let fix fields_rec
              (ts : F.fs tags_t (E.t tags_t)) : F.fs tags_t (V.v tags_t) :=
          match ts with
          | [] => []
          | (x, τ) :: ts => (x, vdefault τ) :: fields_rec ts
          end in
      match τ with
      | {{ error }}      => V.VError None
      | {{ matchkind }}  => *{ MATCHKIND exact }*
      | {{ Bool }}       => *{ FALSE }*
      | {{ bit<w> }}     => *{ w VW N0 }*
      | {{ int<w> }}     => *{ w VS Z0 }*
      | {{ rec { ts } }} => V.VRecord (fields_rec ts)
      | {{ hdr { ts } }} => V.VHeader (fields_rec ts) false
      end.

    Inductive stmt_big_step (fs : fenv) (ins : ienv) (ϵ : epsilon) :
      ST.s tags_t -> epsilon -> signal tags_t -> Prop :=
    | sbs_skip (i : tags_t) :
        ⟪ fs, ins, ϵ, skip @ i ⟫ ⤋ ⟪ ϵ, C ⟫
    | sbs_seq_cont (s1 s2 : ST.s tags_t) (i : tags_t)
                   (ϵ' ϵ'' : epsilon) (sig : signal tags_t) :
        ⟪ fs, ins, ϵ,  s1 ⟫ ⤋ ⟪ ϵ',  C ⟫ ->
        ⟪ fs, ins, ϵ', s2 ⟫ ⤋ ⟪ ϵ'', sig ⟫ ->
        ⟪ fs, ins, ϵ,  s1 ; s2 @ i ⟫ ⤋ ⟪ ϵ'', sig ⟫
    | sbs_seq_interrupt (s1 s2 : ST.s tags_t) (i : tags_t)
                           (ϵ' : epsilon) (sig : signal tags_t) :
        interrupt sig ->
        ⟪ fs, ins, ϵ, s1 ⟫ ⤋ ⟪ ϵ', sig ⟫ ->
        ⟪ fs, ins, ϵ, s1 ; s2 @ i ⟫ ⤋ ⟪ ϵ', sig ⟫
    | sbs_vardecl (τ : E.t tags_t) (x : string tags_t)
                  (i : tags_t) (v : V.v tags_t) :
        vdefault τ = v ->
        let x' := bare x in
        ⟪ fs, ins, ϵ, var x : τ @ i ⟫ ⤋ ⟪ x' ↦ v ;; ϵ, C ⟫
    | sbs_assign (τ : E.t tags_t) (e1 e2 : E.e tags_t) (i : tags_t)
                 (lv : V.lv tags_t) (v : V.v tags_t) (ϵ' : epsilon) :
        lv_update lv v ϵ = ϵ' ->
        ⦑ ϵ, e1 ⦒ ⇓ lv ->
        ⟨ ϵ, e2 ⟩ ⇓ v ->
        ⟪ fs, ins, ϵ, asgn e1 := e2 : τ @ i ⟫ ⤋ ⟪ ϵ', C ⟫
    | sbs_exit (i : tags_t) :
        ⟪ fs, ins, ϵ, exit @ i ⟫ ⤋ ⟪ ϵ, X ⟫
    | sbs_retvoid (i : tags_t) :
        ⟪ fs, ins, ϵ, returns @ i ⟫ ⤋ ⟪ ϵ, Void ⟫
    | sbs_retfruit (τ : E.t tags_t) (e : E.e tags_t)
                   (i : tags_t) (v : V.v tags_t) :
        ⟨ ϵ, e ⟩ ⇓ v ->
        ⟪ fs, ins, ϵ, return e:τ @ i ⟫ ⤋ ⟪ ϵ, Fruit v ⟫
    | sbs_cond_true (guard : E.e tags_t)
                    (tru fls : ST.s tags_t) (i : tags_t)
                    (ϵ' : epsilon) (sig : signal tags_t) :
        ⟨ ϵ, guard ⟩ ⇓ TRUE ->
        ⟪ fs, ins, ϵ, tru ⟫ ⤋ ⟪ ϵ', sig ⟫ ->
        ⟪ fs, ins, ϵ, if guard:Bool then tru else fls @ i ⟫
          ⤋ ⟪ ϵ', sig ⟫
    | sbs_cond_false (guard : E.e tags_t)
                     (tru fls : ST.s tags_t) (i : tags_t)
                     (ϵ' : epsilon) (sig : signal tags_t) :
        ⟨ ϵ, guard ⟩ ⇓ FALSE ->
        ⟪ fs, ins, ϵ, fls ⟫ ⤋ ⟪ ϵ', sig ⟫ ->
        ⟪ fs, ins, ϵ, if guard:Bool then tru else fls @ i ⟫
          ⤋ ⟪ ϵ', sig ⟫
    | sbs_methodcall (params : E.params tags_t)
                     (args : E.args tags_t)
                     (argsv : V.argsv tags_t)
                     (f : name tags_t) (i : tags_t)
                     (body : ST.s tags_t) (fclosure : fenv) (fins : ienv)
                     (closure ϵ' ϵ'' ϵ''' : epsilon) :
        (* Looking up function. *)
        lookup fs f = Some (FDecl closure fclosure fins (P.Arrow params None) body) ->
        (* Argument evaluation. *)
        F.relfs
          (P.rel_paramarg
             (fun '(_,e) v  => ⟨ ϵ, e ⟩ ⇓ v)
             (fun '(_,e) lv => ⦑ ϵ, e ⦒ ⇓ lv))
          args argsv ->
        (* Copy-in. *)
        copy_in argsv ϵ closure = ϵ' ->
        (* Function evaluation *)
        ⟪ fclosure, fins, ϵ', body ⟫ ⤋ ⟪ ϵ'', Void ⟫ ->
        (* Copy-out *)
        copy_out argsv ϵ'' ϵ = ϵ''' ->
        ⟪ fs, ins, ϵ, call f with args @ i ⟫ ⤋ ⟪ ϵ''', C ⟫
    | sbs_fruitcall (params : E.params tags_t)
                    (args : E.args tags_t)
                    (argsv : V.argsv tags_t)
                    (f : name tags_t)
                    (e : E.e tags_t) (τ : E.t tags_t)
                    (i : tags_t)
                    (v : V.v tags_t) (lv : V.lv tags_t)
                    (body : ST.s tags_t) (fclosure : fenv) (fins : ienv)
                    (closure ϵ' ϵ'' ϵ''' ϵ'''' : epsilon) :
        (* Looking up function. *)
        lookup fs f = Some (FDecl closure fclosure fins (P.Arrow params (Some τ)) body) ->
        (* Argument evaluation. *)
        F.relfs
          (P.rel_paramarg
             (fun '(_,e) v => ⟨ ϵ, e ⟩ ⇓ v)
             (fun '(_,e) lv => ⦑ ϵ, e ⦒ ⇓ lv))
          args argsv ->
        (* Copy-in. *)
        copy_in argsv ϵ closure = ϵ' ->
        (* Lvalue Evaluation. *)
        ⦑ ϵ, e ⦒ ⇓ lv ->
        (* Function evaluation. *)
        ⟪ fclosure, fins, ϵ', body ⟫ ⤋ ⟪ ϵ'', Fruit v ⟫ ->
        (* Copy-out. *)
        copy_out argsv ϵ'' ϵ = ϵ''' ->
        (* Assignment to lvalue. *)
        lv_update lv v ϵ''' = ϵ'''' ->
        ⟪ fs, ins, ϵ, let e:τ := call f with args @ i ⟫ ⤋ ⟪ ϵ'''', C ⟫
    | sbs_apply (params : E.params tags_t)
                    (args : E.args tags_t)
                    (argsv : V.argsv tags_t)
                    (x : name tags_t)
                    (i : tags_t)
                    (body : ST.s tags_t) (fclosure : fenv) (iins : ienv)
                    (closure ϵ' ϵ'' ϵ''' ϵ'''' : epsilon) :
        (* Instance lookup. *)
        ilookup ins x = Some (CInst closure fclosure iins params body) ->
        (* Argument evaluation. *)
        F.relfs
          (P.rel_paramarg
             (fun '(_,e) v => ⟨ ϵ, e ⟩ ⇓ v)
             (fun '(_,e) lv => ⦑ ϵ, e ⦒ ⇓ lv))
          args argsv ->
        (* Copy-in. *)
        copy_in argsv ϵ closure = ϵ' ->
        (* Apply block evaluation. *)
        ⟪ fclosure, iins, ϵ', body ⟫ ⤋ ⟪ ϵ'', Void ⟫ ->
        (* Copy-out. *)
        copy_out argsv ϵ'' ϵ = ϵ''' ->
        ⟪ fs, ins, ϵ, apply x with args @ i ⟫ ⤋ ⟪ ϵ'''', C ⟫
    where "⟪ fs , ins , ϵ , s ⟫ ⤋ ⟪ ϵ' , sig ⟫" := (stmt_big_step fs ins ϵ s ϵ' sig).
  End Step.
End Step.
