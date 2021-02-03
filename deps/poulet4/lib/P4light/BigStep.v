Require Export P4light.Check.
Require Export P4light.P4Arith.
Require Import Coq.NArith.BinNatDef.
Require Import Coq.ZArith.BinIntDef.
Require Import Coq.NArith.BinNat.
Require Import Coq.ZArith.BinInt.

Module Value.
  Section Values.
    Variable (tags_t : Type).

    (** Values from expression evaluation. *)
    Inductive v : Type :=
    | VBool (b : bool)
    | VInt (w : positive) (n : Z)
    | VBit (w : positive) (n : N)
    | VRecord (fs : Field.fs tags_t v)
    | VHeader (fs : Field.fs tags_t v)
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

      Hypothesis HVHeader : forall fs,
          Field.predfs_data P fs -> P (VHeader fs).

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
          | VHeader vs     => HVHeader vs (fields_ind vs)
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
      | equivv_header (fs1 fs2 : Field.fs tags_t v) :
          Field.relfs equivv fs1 fs2 ->
          equivv (VHeader fs1) (VHeader fs2)
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
  Arguments VHeader {_}.
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
    Notation "'HDR' { fs }" := (VHeader fs)
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

  Import E.TypeNotations.
  Import E.ExprNotations.
  Import V.ValueNotations.

  Reserved Notation "⟨ ϵ , e ⟩ ⇓ v"
           (at level 40, e custom p4expr, v custom p4value).
  (**[]*)

  Section Step.
    Context {tags_t : Type}.

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
        ⟨ ϵ, Var x :: τ @ i end ⟩ ⇓ v
    | ebs_error (err : string tags_t) (i : tags_t) :
        ⟨ ϵ, Error err @ i ⟩ ⇓ ERROR err
    | ebs_matchkind (mk : string tags_t) (i : tags_t) :
        ⟨ ϵ, Matchkind mk @ i ⟩ ⇓ MATCHKIND mk
    (* Unary Operations. *)
    | ebs_not (e : E.e tags_t) (i : tags_t) (b b' : bool) :
        negb b = b' ->
        ⟨ ϵ, e ⟩ ⇓ VBOOL b ->
        ⟨ ϵ, ! e :: Bool @ i end ⟩ ⇓ VBOOL b'
    (* TODO: bitnot case is incorrect,
       need to define negation for [N]. *)
    | ebs_bitnot (e : E.e tags_t) (i : tags_t)
                 (w : positive) (n n' : N) :
        ⟨ ϵ, e ⟩ ⇓ w VW n ->
        ⟨ ϵ, ~ e :: bit<w> @ i end ⟩ ⇓ w VW n
    (* TODO: uminus case is incorrect,
       need to define proper negation for [Z]. *)
    | ebs_uminus (e : E.e tags_t) (i : tags_t)
                 (w : positive) (z z' : Z) :
        Z.opp z = z' ->
        ⟨ ϵ, e ⟩ ⇓ w VS z ->
        ⟨ ϵ, ~ e :: int<w> @ i end ⟩ ⇓ w VS z'
    (* Binary Operations. *)
    | ebs_plus_bit (e1 e2 : E.e tags_t) (i : tags_t)
                   (w : positive) (n n1 n2 : N) :
        BitArith.plus_mod w n1 n2 = n ->
        ⟨ ϵ, e1 ⟩ ⇓ w VW n1 ->
        ⟨ ϵ, e2 ⟩ ⇓ w VW n2 ->
        ⟨ ϵ, + e1 :: bit<w> e2 :: bit<w> @ i end ⟩ ⇓ w VW n
    | ebs_plus_int (e1 e2 : E.e tags_t) (i : tags_t)
                   (w : positive) (z z1 z2 : Z) :
        IntArith.plus_mod w z1 z2 = z ->
        ⟨ ϵ, e1 ⟩ ⇓ w VS z1 ->
        ⟨ ϵ, e2 ⟩ ⇓ w VS z2 ->
        ⟨ ϵ, + e1 :: int<w> e2 :: int<w> @ i end ⟩ ⇓ w VS z
    | ebs_minus_bit (e1 e2 : E.e tags_t) (i : tags_t)
                    (w : positive) (n n1 n2 : N) :
        BitArith.minus_mod w n1 n2 = n ->
        ⟨ ϵ, e1 ⟩ ⇓ w VW n1 ->
        ⟨ ϵ, e2 ⟩ ⇓ w VW n2 ->
        ⟨ ϵ, -- e1 :: bit<w> e2 :: bit<w> @ i end ⟩ ⇓ w VW n
    | ebs_minus_int (e1 e2 : E.e tags_t) (i : tags_t)
                    (w : positive) (z z1 z2 : Z) :
        IntArith.minus_mod w z1 z2 = z ->
        ⟨ ϵ, e1 ⟩ ⇓ w VS z1 ->
        ⟨ ϵ, e2 ⟩ ⇓ w VS z2 ->
        ⟨ ϵ, -- e1 :: int<w> e2 :: int<w> @ i end ⟩ ⇓ w VS z
    | ebs_plussat_bit (e1 e2 : E.e tags_t) (i : tags_t)
                      (w : positive) (n n1 n2 : N) :
        BitArith.plus_sat w n1 n2 = n ->
        ⟨ ϵ, e1 ⟩ ⇓ w VW n1 ->
        ⟨ ϵ, e2 ⟩ ⇓ w VW n2 ->
        ⟨ ϵ, |+| e1 :: bit<w> e2 :: bit<w> @ i end ⟩ ⇓ w VW n
    | ebs_plussat_int (e1 e2 : E.e tags_t) (i : tags_t)
                      (w : positive) (z z1 z2 : Z) :
        IntArith.plus_sat w z1 z2 = z ->
        ⟨ ϵ, e1 ⟩ ⇓ w VS z1 ->
        ⟨ ϵ, e2 ⟩ ⇓ w VS z2 ->
        ⟨ ϵ, |+| e1 :: int<w> e2 :: int<w> @ i end ⟩ ⇓ w VS z
    | ebs_minussat_bit (e1 e2 : E.e tags_t) (i : tags_t)
                       (w : positive) (n n1 n2 : N) :
        N.sub n1 n2 = n ->
        ⟨ ϵ, e1 ⟩ ⇓ w VW n1 ->
        ⟨ ϵ, e2 ⟩ ⇓ w VW n2 ->
        ⟨ ϵ, |-| e1 :: bit<w> e2 :: bit<w> @ i end ⟩ ⇓ w VW n
    | ebs_minussat_int (e1 e2 : E.e tags_t) (i : tags_t)
                       (w : positive) (z z1 z2 : Z) :
        IntArith.minus_sat w z1 z2 = z ->
        ⟨ ϵ, e1 ⟩ ⇓ w VS z1 ->
        ⟨ ϵ, e2 ⟩ ⇓ w VS z2 ->
        ⟨ ϵ, |-| e1 :: int<w> e2 :: int<w> @ i end ⟩ ⇓ w VS z
    | ebs_bitand_bit (e1 e2 : E.e tags_t) (i : tags_t)
                     (w : positive) (n n1 n2 : N) :
        BitArith.bit_and w n1 n2 = n ->
        ⟨ ϵ, e1 ⟩ ⇓ w VW n1 ->
        ⟨ ϵ, e2 ⟩ ⇓ w VW n2 ->
        ⟨ ϵ, & e1 :: bit<w> e2 :: bit<w> @ i end ⟩ ⇓ w VW n
    | ebs_bitand_int (e1 e2 : E.e tags_t) (i : tags_t)
                     (w : positive) (z z1 z2 : Z) :
        IntArith.bit_and w z1 z2 = z ->
        ⟨ ϵ, e1 ⟩ ⇓ w VS z1 ->
        ⟨ ϵ, e2 ⟩ ⇓ w VS z2 ->
        ⟨ ϵ, & e1 :: int<w> e2 :: int<w> @ i end ⟩ ⇓ w VS z
    | ebs_bitor_bit (e1 e2 : E.e tags_t) (i : tags_t)
                    (w : positive) (n n1 n2 : N) :
        BitArith.bit_or w n1 n2 = n ->
        ⟨ ϵ, e1 ⟩ ⇓ w VW n1 ->
        ⟨ ϵ, e2 ⟩ ⇓ w VW n2 ->
        ⟨ ϵ, | e1 :: bit<w> e2 :: bit<w> @ i end ⟩ ⇓ w VW n
    | ebs_bitor_int (e1 e2 : E.e tags_t) (i : tags_t)
                   (w : positive) (z z1 z2 : Z) :
        IntArith.bit_or w z1 z2 = z ->
        ⟨ ϵ, e1 ⟩ ⇓ w VS z1 ->
        ⟨ ϵ, e2 ⟩ ⇓ w VS z2 ->
        ⟨ ϵ, | e1 :: int<w> e2 :: int<w> @ i end ⟩ ⇓ w VS z
    | ebs_bitxor_bit (e1 e2 : E.e tags_t) (i : tags_t)
                     (w : positive) (n n1 n2 : N) :
        BitArith.bit_xor w n1 n2 = n ->
        ⟨ ϵ, e1 ⟩ ⇓ w VW n1 ->
        ⟨ ϵ, e2 ⟩ ⇓ w VW n2 ->
        ⟨ ϵ, ^ e1 :: bit<w> e2 :: bit<w> @ i end ⟩ ⇓ w VW n
    | ebs_bitxor_int (e1 e2 : E.e tags_t) (i : tags_t)
                     (w : positive) (z z1 z2 : Z) :
        IntArith.bit_xor w z1 z2 = z ->
        ⟨ ϵ, e1 ⟩ ⇓ w VS z1 ->
        ⟨ ϵ, e2 ⟩ ⇓ w VS z2 ->
        ⟨ ϵ, ^ e1 :: int<w> e2 :: int<w> @ i end ⟩ ⇓ w VS z
    | ebs_and (e1 e2 : E.e tags_t) (i : tags_t) (b b1 b2 : bool) :
        andb b1 b2 = b ->
        ⟨ ϵ, e1 ⟩ ⇓ VBOOL b1 ->
        ⟨ ϵ, e2 ⟩ ⇓ VBOOL b2 ->
        ⟨ ϵ, && e1 :: Bool e2 :: Bool @ i end ⟩ ⇓ VBOOL b
    | ebs_or (e1 e2 : E.e tags_t) (i : tags_t) (b b1 b2 : bool) :
        orb b1 b2 = b ->
        ⟨ ϵ, e1 ⟩ ⇓ VBOOL b1 ->
        ⟨ ϵ, e2 ⟩ ⇓ VBOOL b2 ->
        ⟨ ϵ, || e1 :: Bool e2 :: Bool @ i end ⟩ ⇓ VBOOL b
    | ebs_le_bit (e1 e2 : E.e tags_t) (i : tags_t)
                 (w : positive) (n1 n2 : N) (b : bool) :
        N.leb n1 n2 = b ->
        ⟨ ϵ, e1 ⟩ ⇓ w VW n1 ->
        ⟨ ϵ, e2 ⟩ ⇓ w VW n2 ->
        ⟨ ϵ, <= e1 :: bit<w> e2 :: bit<w> @ i end ⟩ ⇓ VBOOL b
    | ebs_le_int (e1 e2 : E.e tags_t) (i : tags_t)
                 (w : positive) (z1 z2 : Z) (b : bool) :
        Z.leb z1 z2 = b ->
        ⟨ ϵ, e1 ⟩ ⇓ w VS z1 ->
        ⟨ ϵ, e2 ⟩ ⇓ w VS z2 ->
        ⟨ ϵ, <= e1 :: int<w> e2 :: int<w> @ i end ⟩ ⇓ VBOOL b
    | ebs_ge_bit (e1 e2 : E.e tags_t) (i : tags_t)
                 (w : positive) (n1 n2 : N) (b : bool) :
        N.leb n2 n1 = b ->
        ⟨ ϵ, e1 ⟩ ⇓ w VW n1 ->
        ⟨ ϵ, e2 ⟩ ⇓ w VW n2 ->
        ⟨ ϵ, >= e1 :: bit<w> e2 :: bit<w> @ i end ⟩ ⇓ VBOOL b
    | ebs_ge_int (e1 e2 : E.e tags_t) (i : tags_t)
                 (w : positive) (z1 z2 : Z) (b : bool) :
        Z.leb z2 z1 = b ->
        ⟨ ϵ, e1 ⟩ ⇓ w VS z1 ->
        ⟨ ϵ, e2 ⟩ ⇓ w VS z2 ->
        ⟨ ϵ, >= e1 :: int<w> e2 :: int<w> @ i end ⟩ ⇓ VBOOL b
    | ebs_lt_bit (e1 e2 : E.e tags_t) (i : tags_t)
                 (w : positive) (n1 n2 : N) (b : bool) :
        N.ltb n1 n2 = b ->
        ⟨ ϵ, e1 ⟩ ⇓ w VW n1 ->
        ⟨ ϵ, e2 ⟩ ⇓ w VW n2 ->
        ⟨ ϵ, < e1 :: bit<w> e2 :: bit<w> @ i end ⟩ ⇓ VBOOL b
    | ebs_lt_int (e1 e2 : E.e tags_t) (i : tags_t)
                 (w : positive) (z1 z2 : Z) (b : bool) :
        Z.ltb z1 z2 = b ->
        ⟨ ϵ, e1 ⟩ ⇓ w VS z1 ->
        ⟨ ϵ, e2 ⟩ ⇓ w VS z2 ->
        ⟨ ϵ, < e1 :: int<w> e2 :: int<w> @ i end ⟩ ⇓ VBOOL b
    | ebs_gt_bit (e1 e2 : E.e tags_t) (i : tags_t)
                 (w : positive) (n1 n2 : N) (b : bool) :
        N.ltb n2 n1 = b ->
        ⟨ ϵ, e1 ⟩ ⇓ w VW n1 ->
        ⟨ ϵ, e2 ⟩ ⇓ w VW n2 ->
        ⟨ ϵ, > e1 :: bit<w> e2 :: bit<w> @ i end ⟩ ⇓ VBOOL b
    | ebs_gt_int (e1 e2 : E.e tags_t) (i : tags_t)
                 (w : positive) (z1 z2 : Z) (b : bool) :
        Z.ltb z2 z1 = b ->
        ⟨ ϵ, e1 ⟩ ⇓ w VS z1 ->
        ⟨ ϵ, e2 ⟩ ⇓ w VS z2 ->
        ⟨ ϵ, > e1 :: int<w> e2 :: int<w> @ i end ⟩ ⇓ VBOOL b
    | ebs_eq_true (e1 e2 : E.e tags_t) (τ1 τ2 : E.t tags_t)
                  (i : tags_t) (v1 v2 : V.v tags_t) :
        V.equivv tags_t v1 v2 ->
        ⟨ ϵ, e1 ⟩ ⇓ v1 ->
        ⟨ ϵ, e2 ⟩ ⇓ v2 ->
        ⟨ ϵ, == e1 :: τ1 e2 :: τ2 @ i end ⟩ ⇓ TRUE
    | ebs_eq_false (e1 e2 : E.e tags_t) (τ1 τ2 : E.t tags_t)
                   (i : tags_t) (v1 v2 : V.v tags_t) :
        ~ V.equivv tags_t v1 v2 ->
        ⟨ ϵ, e1 ⟩ ⇓ v1 ->
        ⟨ ϵ, e2 ⟩ ⇓ v2 ->
        ⟨ ϵ, == e1 :: τ1 e2 :: τ2 @ i end ⟩ ⇓ FALSE
    | ebs_neq_true (e1 e2 : E.e tags_t) (τ1 τ2 : E.t tags_t)
                   (i : tags_t) (v1 v2 : V.v tags_t) :
        ~ V.equivv tags_t v1 v2 ->
        ⟨ ϵ, e1 ⟩ ⇓ v1 ->
        ⟨ ϵ, e2 ⟩ ⇓ v2 ->
        ⟨ ϵ, != e1 :: τ1 e2 :: τ2 @ i end ⟩ ⇓ TRUE
    | ebs_neq_false (e1 e2 : E.e tags_t) (τ1 τ2 : E.t tags_t)
                    (i : tags_t) (v1 v2 : V.v tags_t) :
        V.equivv tags_t v1 v2 ->
        ⟨ ϵ, e1 ⟩ ⇓ v1 ->
        ⟨ ϵ, e2 ⟩ ⇓ v2 ->
        ⟨ ϵ, != e1 :: τ1 e2 :: τ2 @ i end ⟩ ⇓ FALSE
    | ebs_shl_bit (e1 e2 : E.e tags_t) (i : tags_t)
                  (w : positive) (n n1 n2 : N) :
        N.shiftl n1 n2 = n ->
        ⟨ ϵ, e1 ⟩ ⇓ w VW n1 ->
        ⟨ ϵ, e2 ⟩ ⇓ w VW n2 ->
        ⟨ ϵ, << e1 :: bit<w> e2 :: bit<w> @ i end ⟩ ⇓ w VW n
    | ebs_shl_int (e1 e2 : E.e tags_t) (i : tags_t)
                  (w : positive) (z z1 z2 : Z) :
        IntArith.shift_left w z1 z2 = z ->
        ⟨ ϵ, e1 ⟩ ⇓ w VS z1 ->
        ⟨ ϵ, e2 ⟩ ⇓ w VS z2 ->
        ⟨ ϵ, << e1 :: int<w> e2 :: int<w> @ i end ⟩ ⇓ w VS z
    | ebs_shr_bit (e1 e2 : E.e tags_t) (i : tags_t)
                  (w : positive) (n n1 n2 : N) :
        BitArith.shift_right w n1 n2 = n ->
        ⟨ ϵ, e1 ⟩ ⇓ w VW n1 ->
        ⟨ ϵ, e2 ⟩ ⇓ w VW n2 ->
        ⟨ ϵ, >> e1 :: bit<w> e2 :: bit<w> @ i end ⟩ ⇓ w VW n
    | ebs_shr_int (e1 e2 : E.e tags_t) (i : tags_t)
                  (w : positive) (z z1 z2 : Z) :
        IntArith.shift_right w z1 z2 = z ->
        ⟨ ϵ, e1 ⟩ ⇓ w VS z1 ->
        ⟨ ϵ, e2 ⟩ ⇓ w VS z2 ->
        ⟨ ϵ, >> e1 :: int<w> e2 :: int<w> @ i end ⟩ ⇓ w VS z
    | ebs_plusplus (e1 e2 : E.e tags_t) (i : tags_t)
                   (w w1 w2 : positive) (n n1 n2 : N) :
        (w1 + w2)%positive = w ->
        BitArith.bit_concat w2 n1 n2 = n ->
        ⟨ ϵ, e1 ⟩ ⇓ w1 VW n1 ->
        ⟨ ϵ, e2 ⟩ ⇓ w2 VW n2 ->
        ⟨ ϵ, ++ e1 :: bit<w1> e2 :: bit<w2> @ i end ⟩ ⇓ w VW n
    (* Structs *)
    | ebs_rec_mem (e : E.e tags_t) (x : string tags_t) (i : tags_t)
                  (tfs : F.fs tags_t (E.t tags_t))
                  (vfs : F.fs tags_t (V.v tags_t)) (v : V.v tags_t) :
        F.get x vfs = Some v ->
        ⟨ ϵ, e ⟩ ⇓ REC { vfs } ->
        ⟨ ϵ, Mem e :: rec { tfs } dot x @ i end ⟩ ⇓ v
    | ebs_hdr_mem (e : E.e tags_t) (x : string tags_t) (i : tags_t)
                  (tfs : F.fs tags_t (E.t tags_t))
                  (vfs : F.fs tags_t (V.v tags_t)) (v : V.v tags_t) :
        F.get x vfs = Some v ->
        ⟨ ϵ, e ⟩ ⇓ HDR { vfs } ->
        ⟨ ϵ, Mem e :: hdr { tfs } dot x @ i end ⟩ ⇓ v
    | ebs_rec_lit (efs : F.fs tags_t (E.t tags_t * E.e tags_t))
                  (i : tags_t) (vfs : F.fs tags_t (V.v tags_t)) :
        F.relfs
          (fun te v =>
             let e := snd te in ⟨ ϵ, e ⟩ ⇓ v) efs vfs ->
        ⟨ ϵ, rec { efs } @ i ⟩ ⇓ REC { vfs }
    | ebs_hdr_lit (efs : F.fs tags_t (E.t tags_t * E.e tags_t))
                  (i : tags_t) (vfs : F.fs tags_t (V.v tags_t)) :
        F.relfs
          (fun te v =>
             let e := snd te in ⟨ ϵ, e ⟩ ⇓ v) efs vfs ->
        ⟨ ϵ, hdr { efs } @ i ⟩ ⇓ HDR { vfs }
    where "⟨ ϵ , e ⟩ ⇓ v" := (expr_big_step ϵ e v).
  End Step.
End Step.
