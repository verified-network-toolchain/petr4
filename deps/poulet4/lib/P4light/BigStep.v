Require Export P4light.Check.

Section Values.
  Variable (tags_t : Type).

  (** Values from expression evaluation. *)
  Inductive value : Type :=
  | VBool (b : bool) (i : tags_t)
  | VInt (w : positive) (n : Z) (i : tags_t)
  | VBit (w : positive) (n : N) (i : tags_t)
  | VRecord (fs : Field.fs tags_t value) (i : tags_t)
  | VError (err : string tags_t) (i : tags_t)
  | VMatchKind (mk : string tags_t) (i : tags_t).

  (** A custom induction principle for value. *)
  Section ValueInduction.
    Variable P : value -> Prop.

    Hypothesis HVBool : forall b i, P (VBool b i).

    Hypothesis HVBit : forall w n i, P (VBit w n i).

    Hypothesis HVInt : forall w n i, P (VInt w n i).

    Hypothesis HVRecord : forall fs i,
        Field.predfs_data P fs -> P (VRecord fs i).

    Hypothesis HVError : forall err i, P (VError err i).

    Hypothesis HVMatchKind : forall mk i, P (VMatchKind mk i).

    Definition custom_value_ind : forall v : value, P v :=
      fix custom_value_ind (val : value) : P val :=
          let fix fields_ind
                  (flds : Field.fs tags_t value) : Field.predfs_data P flds :=
              match flds as fs return Field.predfs_data P fs with
              | [] => Forall_nil (Field.predf_data P)
              | (_, hfv) as hf :: tf =>
                Forall_cons hf (custom_value_ind hfv) (fields_ind tf)
              end in
          match val as v return P v with
          | VBool b i  => HVBool b i
          | VInt w n i => HVInt w n i
          | VBit w n i => HVBit w n i
          | VRecord vs i     => HVRecord vs i (fields_ind vs)
          | VError err i     => HVError err i
          | VMatchKind mk i  => HVMatchKind mk i
          end.
  End ValueInduction.
(*
  Section ValueRect.
    Variable P : value -> Prop.

    Hypothesis HVBool : forall b i, P (VBool b i).

    Hypothesis HVInt : forall n i, P (VInt n i).

    Hypothesis HVBitString : forall w n i, P (VBitString w n i).

    Hypothesis HVRecord : forall fs i,
        Field.predfs_data P fs -> P (VRecord fs i).

    Hypothesis HVError : forall err i, P (VError err i).

    Hypothesis HVMatchKind : forall mk i, P (VMatchKind mk i).

    Definition custom_value_rect : forall v : value, P v :=
      fix custom_value_rect (val : value) : P val :=
          let fix fields_rect
                  (flds : Field.fs tags_t value) : Field.predfs_data P flds :=
              match flds as fs return Field.predfs_data P fs with
              | [] => Forall_nil (Field.predf_data P)
              | (_, hfv) as hf :: tf =>
                Forall_cons hf (custom_value_ind hfv) (fields_ind tf)
              end in
          match val as v return P v with
          | VBool b i => HVBool b i
          | VInt n i  => HVInt n i
          | VBitString w n i => HVBitString w n i
          | VRecord vs i     => HVRecord vs i (fields_ind vs)
          | VError err i     => HVError err i
          | VMatchKind mk i  => HVMatchKind mk i
          end.
  End ValueRect.
*)
  Section ValueEquality.
    (** Value equivalence relation. *)
    Inductive equivv : value -> value -> Prop :=
    | equivv_bool (b : bool) (i1 i2 : tags_t) :
        equivv (VBool b i1) (VBool b i2)
    | equivv_int (w : positive) (n : Z) (i1 i2 : tags_t) :
        equivv (VInt w n i1) (VInt w n i2)
    | equivv_bit (w : positive) (n : N) (i1 i2 : tags_t) :
        equivv (VBit w n i1) (VBit w n i2)
    | equivv_record (fs1 fs2 : Field.fs tags_t value) (i1 i2 : tags_t) :
        Field.relfs equivv fs1 fs2 ->
        equivv (VRecord fs1 i1) (VRecord fs2 i2)
    | equivv_error (err1 err2 : string tags_t) (i1 i2 : tags_t) :
        P4String.equiv err1 err2 ->
        equivv (VError err1 i1) (VError err2 i2)
    | equivv_matchkind (mk1 mk2 : string tags_t) (i1 i2 : tags_t) :
        P4String.equiv mk1 mk2 ->
        equivv (VMatchKind mk1 i1) (VMatchKind mk2 i2).
    (**[]*)

    Lemma equivv_reflexive : Reflexive equivv.
    Proof.
      intros v; induction v using custom_value_ind;
        constructor; try reflexivity.
      induction fs as [| [x v] vs];
        inversion H; clear H; subst; constructor.
      - unfold Field.predf_data in H2.
        unfold Field.relf; simpl; split; auto. reflexivity.
      - apply IHvs; auto.
    Qed.

    Lemma equivv_symmetric : Symmetric equivv.
    Proof.
      intros v1; induction v1 using custom_value_ind;
        intros [] HEQ; inversion HEQ; clear HEQ; subst;
          constructor; try (symmetry; assumption).
      rename fs into fs1; rename fs0 into fs2;
        rename i into i1; rename i0 into i2.
      generalize dependent fs2;
        induction fs1 as [| [x1 v1] vs1 IHvs1];
        intros [| [x2 v2] vs2] HSym;
        inversion HSym; clear HSym; subst; constructor;
          inversion H; clear H; subst.
      - unfold Field.relf in *; simpl in *;
          destruct H3; split; try (symmetry; assumption).
        apply H2; assumption.
      - apply IHvs1; auto.
    Qed.

    Lemma equivv_transitive : Transitive equivv.
    Proof.
      intros v1; induction v1 using custom_value_ind; intros v2 v3 H12 H23;
        inversion H12; subst; inversion H23; subst;
          clear H12 H23; constructor.
      - generalize dependent fs0; generalize dependent fs2.
        rename i into i1; rename i0 into i3;
          rename fs into fs1.
        induction fs1 as [| [x1 v1] vs1 IHvs1];
          intros [| [x2 v2] vs2] H12 [| [x3 v3] vs3] H23;
          inversion H12; subst; inversion H23; subst;
            clear H12 H23; constructor; inversion H; subst; clear H.
        + unfold Field.relf in *; simpl in *;
            unfold Field.predf_data;
              destruct H3; destruct H4;
                pose proof (H2 v2 v3) as H23; try split; auto.
          transitivity x2; auto.
        + apply IHvs1 with vs2; auto.
      - transitivity err2; auto.
      - transitivity mk2; auto.
    Qed.

    Instance ValueEquivalence : Equivalence equivv.
    Proof.
      constructor; [ apply equivv_reflexive
                   | apply equivv_symmetric
                   | apply equivv_transitive].
    Defined.

    Lemma equivv_dec : forall v1 v2 : value,
        equivv v1 v2 \/ ~ equivv v1 v2.
    Proof.
      induction v1 using custom_value_ind; intros [];
        try (right; intros H'; inversion H'; contradiction).
      - destruct (equiv_dec b b0) as [Hb | Hb];
          unfold equiv in *; unfold complement in *; subst;
            [ left; constructor
            | right; intros H'; inversion H'; contradiction ].
    Abort.
(*
    Lemma value_eqdec : forall v1 v2 : value,
        {equivv v1 v2} + {~ equivv v1 v2}.
    Proof.
      intros v1. induction v1 using value_rect.
      induction v1 using custom_value_ind with
          (P := fun v1 : value => {equiv v1 v2} + {~ equiv v1 v2}).
*)
  End ValueEquality.
End Values.
