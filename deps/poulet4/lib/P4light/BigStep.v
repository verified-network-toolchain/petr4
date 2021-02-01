Require Export P4light.Check.

Module Value.
  Section Values.
    Variable (tags_t : Type).

    (** Values from expression evaluation. *)
    Inductive v : Type :=
    | VBool (b : bool)
    | VInt (w : positive) (n : Z)
    | VBit (w : positive) (n : N)
    | VRecord (fs : Field.fs tags_t v)
    | VError (err : string tags_t)
    | VMatchKind (mk : string tags_t).

    (** A custom induction principle for value. *)
    Section ValueInduction.
      Variable P : v -> Prop.

      Hypothesis HVBool : forall b, P (VBool b).

      Hypothesis HVBit : forall w n, P (VBit w n).

      Hypothesis HVInt : forall w n, P (VInt w n).

      Hypothesis HVRecord : forall fs,
          Field.predfs_data P fs -> P (VRecord fs).

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
          | VError err     => HVError err
          | VMatchKind mk  => HVMatchKind mk
          end.
    End ValueInduction.

    Section ValueEquality.
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
      | equivv_error (err1 err2 : string tags_t) :
          P4String.equiv err1 err2 ->
          equivv (VError err1) (VError err2)
      | equivv_matchkind (mk1 mk2 : string tags_t) :
          P4String.equiv mk1 mk2 ->
          equivv (VMatchKind mk1) (VMatchKind mk2).
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
        rename fs into fs1; rename fs0 into fs2.
          (* rename i into i1; rename i0 into i2. *)
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
          (* rename i into i1; rename i0 into i3; *)
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

      Lemma equivv_dec : forall v1 v2 : v,
          equivv v1 v2 \/ ~ equivv v1 v2.
      Proof.
        induction v1 using custom_value_ind; intros [];
          try (right; intros H'; inversion H'; contradiction).
        - destruct (equiv_dec b b0) as [Hb | Hb];
            unfold equiv in *; unfold complement in *; subst;
              [ left; constructor
              | right; intros H'; inversion H'; contradiction ].
      Abort.
    End ValueEquality.
  End Values.

  Arguments VBool {_}.
  Arguments VInt {_}.
  Arguments VBit {_}.
  Arguments VRecord {_}.
  Arguments VError {_}.
  Arguments VMatchKind {_}.

  Module ValueNotations.
    Declare Custom Entry p4value.

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
    Notation "'ERROR' x" := (VError x) (in custom p4value at level 0).
    Notation "'MATCHKIND' x" := (VMatchKind x) (in custom p4value at level 0).
  End ValueNotations.
End Value.

Module Step.
  Module P := P4light.
  Module E := P.Expr.
  Module F := P.F.
  Module V := Value.

  Import E.ExprNotations.
  Import V.ValueNotations.

  Reserved Notation "⟨ ϵ , e ⟩ ⇓ v"
           (at level 40, e custom p4expr, v custom p4value).
  (**[]*)

  Section Step.
    Context {tags_t : Type}.

    (** Variable to Value mappings. *)
    Definition epsilon : Type := Env.t (name tags_t) (V.v tags_t).

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
        ⟨ ϵ, Var x :: τ @ i end ⟩ ⇓ v
    where "⟨ ϵ , e ⟩ ⇓ v" := (expr_big_step ϵ e v).
  End Step.
End Step.
