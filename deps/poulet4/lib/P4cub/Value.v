Require Import Coq.Bool.Bool.
Require Import Coq.NArith.BinNatDef.
Require Import Coq.ZArith.BinIntDef.
Require Import Coq.NArith.BinNat.
Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Lia.

Require Import Poulet4.P4cub.AST.
Require Import Poulet4.P4cub.Envn.
Require Import Poulet4.P4cub.P4Arith.

Import Poulet4.P4cub.AST.P4cub.P4cubNotations.

Module E := Poulet4.P4cub.AST.P4cub.Expr.
Module F := Poulet4.P4cub.AST.P4cub.F.

Module TE := E.TypeEquivalence.
Module PT := E.ProperType.

(** Notation entries. *)
Declare Custom Entry p4value.
Declare Custom Entry p4lvalue.

Module Val.
Section Values.

  (** Values from expression evaluation. *)
  Inductive v : Type :=
  | VBool (b : bool)
  | VInt (w : positive) (n : Z)
  | VBit (w : positive) (n : N)
  | VTuple (vs : list v)
  | VRecord (fs : F.fs string v)
  | VHeader (fs : F.fs string v) (validity : bool)
  | VError (err : option string)
  | VMatchKind (mk : P4cub.Expr.matchkind)
  | VHeaderStack (ts : F.fs string E.t)
                 (headers : list (bool * F.fs string v))
                 (size : positive) (nextIndex : N).
  (**[]*)

  (** Lvalues. *)
  Inductive lv : Type :=
  | LVVar (x : string)                 (* Local variables. *)
  | LVMember (arg : lv) (x : string) (* Member access. *)
  | LVAccess (stk : lv) (index : N)       (* Header stack indexing. *).
  (**[]*)

  (** Evaluated arguments. *)
  Definition argsv : Type := F.fs string (P4cub.paramarg v lv).

  (** Intial/Default value from a type. *)
  Fixpoint vdefault (τ : E.t) : v :=
      let fix lrec (ts : list E.t) : list v :=
          match ts with
          | [] => []
          | τ :: ts => vdefault τ :: lrec ts
          end in
      let fix fields_rec
              (ts : F.fs string E.t) : F.fs string v :=
          match ts with
          | [] => []
          | (x, τ) :: ts => (x, vdefault τ) :: fields_rec ts
          end in
      match τ with
      | {{ error }}      => VError None
      | {{ matchkind }}  => VMatchKind E.MKExact
      | {{ Bool }}       => VBool false
      | {{ bit<w> }}     => VBit w 0%N
      | {{ int<w> }}     => VInt w 0%Z
      | {{ tuple ts }}   => VTuple (lrec ts)
      | {{ rec { ts } }} => VRecord (fields_rec ts)
      | {{ hdr { ts } }} => VHeader (fields_rec ts) false
      | {{ stack fs[n] }} => VHeaderStack
                              fs (repeat (false, fields_rec fs)
                                         (Pos.to_nat n)) n 0
      end.
    (**[]*)

  (** A custom induction principle for value. *)
  Section ValueInduction.
    Variable P : v -> Prop.

    Hypothesis HVBool : forall b, P (VBool b).

    Hypothesis HVBit : forall w n, P (VBit w n).

    Hypothesis HVInt : forall w n, P (VInt w n).

    Hypothesis HVTuple : forall vs,
        Forall P vs -> P (VTuple vs).

    Hypothesis HVRecord : forall fs,
        Field.predfs_data P fs -> P (VRecord fs).

    Hypothesis HVHeader : forall fs b,
        Field.predfs_data P fs -> P (VHeader fs b).

    Hypothesis HVError : forall err, P (VError err).

    Hypothesis HVMatchKind : forall mk, P (VMatchKind mk).

    Hypothesis HVHeaderStack : forall ts hs size ni,
        Forall (Field.predfs_data P ∘ snd) hs -> P (VHeaderStack ts hs size ni).

    Definition custom_value_ind : forall v' : v, P v' :=
      fix custom_value_ind (val : v) : P val :=
        let fix lind (vs : list v) : Forall P vs :=
            match vs with
            | [] => Forall_nil _
            | hv :: vs => Forall_cons _ (custom_value_ind hv) (lind vs)
            end in
        let fix fields_ind
                (flds : F.fs string v) : Field.predfs_data P flds :=
            match flds as fs return Field.predfs_data P fs with
            | [] => Forall_nil (Field.predf_data P)
            | (_, hfv) as hf :: tf =>
              Forall_cons hf (custom_value_ind hfv) (fields_ind tf)
            end in
        let fix ffind
                (fflds : list (bool * Field.fs string v))
            : Forall (Field.predfs_data P ∘ snd) fflds :=
            match fflds as ffs
                  return Forall (Field.predfs_data P ∘ snd) ffs with
            | [] => Forall_nil (Field.predfs_data P ∘ snd)
            | (_, vs) as bv :: ffs => Forall_cons bv (fields_ind vs) (ffind ffs)
            end in
        match val as v' return P v' with
        | VBool b  => HVBool b
        | VInt w n => HVInt w n
        | VBit w n => HVBit w n
        | VTuple vs      => HVTuple vs (lind vs)
        | VRecord vs     => HVRecord vs (fields_ind vs)
        | VHeader vs b   => HVHeader vs b (fields_ind vs)
        | VError err     => HVError err
        | VMatchKind mk  => HVMatchKind mk
        | VHeaderStack ts hs size ni => HVHeaderStack ts hs size ni (ffind hs)
        end.
  End ValueInduction.

  Section ValueEquality.
    Import Field.FieldTactics.

    (** Computational Value equality *)
    Fixpoint eqbv (v1 v2 : v) : bool :=
      let fix lrec (vs1 vs2 : list v) : bool :=
          match vs1, vs2 with
          | [], [] => true
          | v1::vs1, v2::vs2 => eqbv v1 v2 && lrec vs1 vs2
          | [], _::_ | _::_, [] => false
          end in
      let fix fields_rec (vs1 vs2 : Field.fs string v) : bool :=
          match vs1, vs2 with
          | [],           []           => true
          | (x1, v1)::vs1, (x2, v2)::vs2
            => equiv_dec x1 x2 &&&& eqbv v1 v2 && fields_rec vs1 vs2
          | [],            _::_
          | _::_,           []          => false
          end in
      (*let fix frec {A : Type} (feqb : A -> A -> bool)
              (as1 as2 : Field.fs string A) : bool :=
          match as1, as2 with
          | [],           []           => true
          | (x1, a1)::as1, (x2, a2)::as2
            => equiv_dec x1 x2 &&&& feqb a1 a2 && frec feqb as1 as2
          | [],            _::_
          | _::_,           []          => false
          end in *)
      let fix ffrec (v1ss v2ss : list (bool * Field.fs string v)) : bool :=
          match v1ss, v2ss with
          | [], _::_ | _::_, [] => false
          | [], [] => true
          | (b1,vs1) :: v1ss, (b2, vs2) :: v2ss => (eqb b1 b2)%bool &&
                                                fields_rec vs1 vs2 &&
                                                ffrec v1ss v2ss
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
      | VTuple vs1, VTuple vs2         => lrec vs1 vs2
      | VHeader vs1 b1, VHeader vs2 b2 => (eqb b1 b2)%bool && fields_rec vs1 vs2
      | VRecord vs1,    VRecord vs2    => fields_rec vs1 vs2
      | VHeaderStack ts1 vss1 n1 ni1,
        VHeaderStack ts2 vss2 n2 ni2   => F.eqb_fs TE.eqbt ts1 ts2 &&
                                         (n1 =? n2)%positive && (ni1 =? ni2)%N &&
                                         ffrec vss1 vss2
      | _,              _              => false
      end.
    (**[]*)

    (* No tags_t -> eq is sufficient.
    (** Value equivalence relation. *)
    Inductive equivv : v -> v -> Prop :=
    | equivv_bool (b : bool) :
        equivv (VBool b) (VBool b)
    | equivv_int (w : positive) (n : Z) :
        equivv (VInt w n) (VInt w n)
    | equivv_bit (w : positive) (n : N) :
        equivv (VBit w n) (VBit w n)
    | equivv_tuple (vs1 vs2 : list v) :
        Forall2 equivv vs1 vs2 ->
        equivv (VTuple vs1) (VTuple vs2)
    | equivv_record (fs1 fs2 : Field.fs tags_t v) :
        Field.relfs equivv fs1 fs2 ->
        equivv (VRecord fs1) (VRecord fs2)
    | equivv_header (fs1 fs2 : Field.fs tags_t v) (b : bool) :
        Field.relfs equivv fs1 fs2 ->
        equivv (VHeader fs1 b) (VHeader fs2 b)
    | equivv_error (err1 err2 : option (string tags_t)) :
        equiv err1 err2 ->
        equivv (VError err1) (VError err2)
    | equivv_matchkind (mk : P4cub.Expr.matchkind) :
        equivv (VMatchKind mk) (VMatchKind mk)
    | equivv_stack (n : positive) (ni : N)
                   (ts1 ts2 : Field.fs tags_t (P4cub.Expr.t tags_t))
                   (vss1 vss2 : list (bool * Field.fs tags_t v)) :
        Field.relfs TE.equivt ts1 ts2 ->
        Forall2 (fun bv1 bv2 =>
                   fst bv1 = fst bv2 /\
                   Field.relfs equivv (snd bv1) (snd bv2))
                vss1 vss2 ->
        equivv (VHeaderStack ts1 vss1 n ni) (VHeaderStack ts2 vss2 n ni).
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

      Hypothesis HTuple : forall vs1 vs2,
          Forall2 equivv vs1 vs2 ->
          Forall2 P vs1 vs2 ->
          P (VTuple vs1) (VTuple vs2).

      Hypothesis HRecord : forall fs1 fs2,
          Field.relfs equivv fs1 fs2 ->
          Field.relfs P fs1 fs2 ->
          P (VRecord fs1) (VRecord fs2).

      Hypothesis HHeader : forall fs1 fs2 b,
          Field.relfs equivv fs1 fs2 ->
          Field.relfs P fs1 fs2 ->
          P (VHeader fs1 b) (VHeader fs2 b).

      Hypothesis HStack : forall n ni ts1 ts2 vss1 vss2,
          Field.relfs TE.equivt ts1 ts2 ->
          Forall2 (fun bv1 bv2 =>
                     fst bv1 = fst bv2 /\
                     Field.relfs equivv (snd bv1) (snd bv2))
                  vss1 vss2 ->
          Forall2 (fun vss1 vss2 => Field.relfs P (snd vss1) (snd vss2)) vss1 vss2 ->
          P (VHeaderStack ts1 vss1 n ni) (VHeaderStack ts2 vss2 n ni).

      (** Custom [eqiuvv] induction principle.
          Do [induction ?H using custom_equivv_ind] *)
      Definition custom_equivv_ind : forall (v1 v2 : v) (H : equivv v1 v2), P v1 v2 :=
        fix vind v1 v2 H :=
          let fix lind
                  {vs1 vs2 : list v}
                  (HR : Forall2 equivv vs1 vs2) : Forall2 P vs1 vs2 :=
              match HR with
              | Forall2_nil _ => Forall2_nil _
              | Forall2_cons _ _
                             HE HTail => Forall2_cons
                                          _ _
                                          (vind _ _ HE)
                                          (lind HTail)
              end in
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
                                          (vind _ _ Hequivv))
                                       (find Htail)
                end in
          let fix ffind
                  {vss1 vss2 : list (bool * Field.fs tags_t v)}
                  (HR : Forall2
                          (fun bv1 bv2 =>
                             fst bv1 = fst bv2 /\
                             Field.relfs equivv (snd bv1) (snd bv2))
                          vss1 vss2)
              : Forall2
                  (fun vss1 vss2 =>
                     Field.relfs P (snd vss1) (snd vss2)) vss1 vss2 :=
              match HR
                    in Forall2 _ v1ss v2ss
                    return Forall2
                             (fun vss1 vss2 => Field.relfs P (snd vss1) (snd vss2))
                             v1ss v2ss with
              | Forall2_nil _ => Forall2_nil _
              | Forall2_cons head _ (conj _ Hhead)
                             Htail => Forall2_cons
                                       head _
                                       (find Hhead)
                                       (ffind Htail)
                end in
          match H in (equivv v1' v2') return P v1' v2' with
          | equivv_bool b => HBool b
          | equivv_bit w n => HBit w n
          | equivv_int w z => HInt w z
          | equivv_error err1 err2 H12 => HError err1 err2 H12
          | equivv_matchkind mk => HMatchkind mk
          | equivv_tuple _ _ H12 => HTuple _ _ H12 (lind H12)
          | equivv_record _ _ H12 => HRecord _ _ H12 (find H12)
          | equivv_header _ _ b H12 => HHeader _ _ b H12 (find H12)
          | equivv_stack n ni _ _ _ _ Ht Hvs => HStack n ni _ _ _ _ Ht
                                                      Hvs (ffind Hvs)
          end.
      (**[]*)
    End ValueEquivalenceInduction.

    Import F.RelfEquiv.

    Lemma equivv_reflexive : Reflexive equivv.
    Proof.
      intros v; induction v using custom_value_ind;
        constructor; try reflexivity;
      try (induction fs as [| [x v] vs];
           inversion H; subst; constructor;
           [ unfold Field.predf_data in H2;
             constructor; simpl; try reflexivity; auto
           | apply IHvs; auto]).
      - induction H; constructor; auto.
      - induction hs as [| [b vs] hs IHhs];
          inv H; constructor; auto; simpl; split; auto.
        unfold Basics.compose in H2; simpl in H2.
        rename H2 into H. clear b hs IHhs H3 ni size.
        induction vs as [| [x v] vs IHvs];
          constructor; invert_cons_predfs; simpl in *;
        [ split; simpl; auto; reflexivity
        | apply IHvs; auto ].
    Qed.

    Lemma equivv_symmetric : Symmetric equivv.
    Proof.
      unfold Symmetric.
      intros v1 v2 Hv;
        induction Hv using custom_equivv_ind;
        constructor; try (symmetry; assumption);
      try (induction H; inv H0; constructor;
          destruct x as [x1 v1]; destruct y as [x2 v2];
            unfold Field.relf in *; simpl in *;
        [ destruct H5; split; try symmetry; auto
        | apply IHForall2; auto ]; assumption).
      - induction H; inv H0; constructor; eauto.
      - clear H ts1 ts2. rename H0 into H; rename H1 into H0.
        induction H; inv H0; constructor;
          destruct x as [b1 vs1];
          destruct y as [b2 vs2]; auto; simpl in *.
        destruct H as [Hb H]; subst; split; auto.
        clear b2 l l' H1 IHForall2 H7 n ni.
        induction H; inv H5; constructor;
          destruct x as [x1 v1]; destruct y as [x2 v2].
            unfold Field.relf in *; simpl in *.
            + destruct H4; split; try symmetry; auto.
            + apply IHForall2; auto.
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
      - rename vs into vs1; rename vs0 into vs3.
        generalize dependent vs3; generalize dependent vs2.
        induction vs1 as [| v1 vs1 IHvs1];
          intros [| v2 vs2] H12 [| v3 vs3] H23;
          inv H; inv H12; inv H23; constructor; eauto.
      - clear vss0 vss2 hs H H6 H8 size ni.
        rename ts into ts1; rename ts0 into ts3.
        generalize dependent ts3; generalize dependent ts2.
        induction ts1 as [| [x1 t1] ts1 IHts1];
          intros [| [x2 t2] ts2] H12 [| [x3 t3] ts3] H23;
          inv H12; inv H23; simpl in *; constructor; auto.
        + destruct H2 as [Hx12 Ht12]; destruct H3 as [Hx23 Ht23];
            split; simpl in *; try (etransitivity; eauto).
        + eapply IHts1; eauto.
      - clear ts ts0 ts2 H5 H7 ni size.
        rename hs into vss1; rename vss0 into vss3.
        generalize dependent vss3;
          generalize dependent vss2.
        induction vss1 as [| [b1 vs1] vss1 IHvss1];
          intros [| [b2 vs2] vss2] H12ss [| [b3 vs3] vss3] H23ss;
          inv H; inv H12ss; inv H23ss;
            constructor; eauto; simpl in *.
        destruct H4; destruct H5; subst; split; auto.
        unfold Basics.compose in H2; simpl in H2.
        clear b3 IHvss1 vss1 vss2 vss3 H3 H6 H8.
        generalize dependent vs3; generalize dependent vs2.
        induction vs1 as [| [x1 v1] vs1 IHvs1];
          intros [| [x2 v2] vs2] H12s [| [x3 v3] vs3] H23s;
          inv H2; inv H12s; inv H23s; constructor.
        + unfold Field.relf in *; simpl in *.
          destruct H4; destruct H5; split;
            try (etransitivity; eassumption).
          eapply H1; eauto.
        + eapply IHvs1; eauto.
    Qed.

    Instance ValueEquivalence : Equivalence equivv.
    Proof.
      constructor; [ apply equivv_reflexive
                   | apply equivv_symmetric
                   | apply equivv_transitive].
    Defined. *)

    Lemma eqbv_refl : forall vl : v, eqbv vl vl = true.
    Proof.
      Hint Rewrite eqb_reflx.
      Hint Rewrite Pos.eqb_refl.
      Hint Rewrite equiv_dec_refl.
      Hint Rewrite N.eqb_refl.
      Hint Rewrite Z.eqb_refl.
      Hint Rewrite TE.eqbt_refl.
      Hint Rewrite (@F.eqb_fs_reflx string E.t).
      Hint Rewrite andb_true_r.
      induction vl using custom_value_ind; simpl in *;
      autorewrite with core; simpl; auto;
      try match goal with
        | hs: list (bool * F.fs string v),
          H: Forall _ ?hs
          |- _ => induction hs as [| [? ?] ? ?];
                try inv_Forall_cons;
                autorewrite with core;
                unfold "∘" in *; simpl in *; intuition;
                repeat (rewrite_true; simpl);
                autorewrite with core;
                match goal with
                | H: Forall _ ?hs |- _ => clear H hs
                end
        end;
      try ind_list_Forall; try ind_list_predfs;
      intuition; autorewrite with core; simpl;
      repeat (rewrite_true; simpl); auto.
    Qed.

    Import F.RelfEquiv.

    Ltac eq_true_terms :=
      match goal with
      | H: eqb _ _ = true |- _
        => apply eqb_prop in H; subst
      | H: (_ =? _)%positive = true |- _
        => apply Peqb_true_eq in H; subst
      | H: (_ =? _)%N = true |- _
        => apply N.eqb_eq in H; subst
      | H: (_ =? _)%Z = true |- _
        => apply Z.eqb_eq in H; subst
      | H: context [equiv_dec ?x1 ?x2 &&&& _] |- _
        => destruct (equiv_dec x1 x2) as [? | ?];
          simpl in H; try discriminate
      | H: context [if equiv_dec ?t1 ?t2 then _ else _] |- _
        => destruct (equiv_dec t1 t2) as [? | ?];
          simpl in H; try discriminate
      (*| H: context [if eqbt ?t1 ?t2 then _ else _] |- _
        => destruct (eqbt t1 t2) eqn:?;
                   simpl in H; try discriminate
      | H: context [eqbt ?t1 ?t2 && _] |- _
        => destruct (eqbt t1 t2) eqn:?;
                   simpl in H; try discriminate
      | H: context [eqbe ?e1 ?e2 && _] |- _
        => destruct (eqbe e1 e2) eqn:?;
                   simpl in H; try discriminate
      | H: eqbt _ _ = true |- _
        => apply eqbt_eq_iff in H
      | H: context [if eqbe ?e1 ?e2 then _ else _] |- _
        => destruct (eqbe e1 e2) eqn:?;
                   simpl in H; try discriminate
      | H: eqbe ?e1 _ = true,
           IH: forall e2, eqbe ?e1 e2 = true -> ∮ ?e1 ≡ e2 |- _
        => apply IH in H
      | H: _ === _ |- _ => unfold equiv in H;
                         match goal with
                         | H: _ = _ |- _ => subst
                         end
      | H: equiv _ _ |- _ => unfold equiv in H;
                           match goal with
                           | H: _ = _ |- _ => subst
                           end
      | H: Forall _ (_ :: _) |- _ => inv H
      | H: ?P, IH: ?P -> ?Q |- _ => apply IH in H as ?
      | H: (if ?trm then true else false) = true |- _
        => destruct trm eqn:?; simpl in H; try discriminate *)
      | H: relop _ _ _ |- _ => inv H
      | H: F.eqb_fs TE.eqbt _ _ = true
        |- _ => pose proof eqb_fs_equiv _ _ TE.eqbt_reflect _ _ H as ?; clear H
      | H: F.relfs eq _ _ |- _ => apply eq_relfs in H; subst
      end.
    (**[]*)

    Ltac eauto_too_dumb :=
      match goal with
      | H: ?f ?x ?y = ?z,
           IH: (forall y, ?f ?x y = ?z -> _)
        |- _ => apply IH in H; clear IH
      end.

    Lemma eqbv_eq : forall v1 v2 : v, eqbv v1 v2 = true -> v1 = v2.
    Proof.
      induction v1 using custom_value_ind; intros []; intros;
      simpl in *; try discriminate;
      repeat destruct_andb;
      repeat (eq_true_terms); unfold equiv in *; auto; f_equal;
      repeat (eq_true_terms); auto;
      try match goal with
          | hs1: list (bool * F.fs string v),
            IH: Forall _ ?hs1,
            H: _ ?hs1 ?hs2 = true
            |- ?hs1 = ?hs2 => generalize dependent hs2;
                            induction hs1 as [| [? ?] ? ?];
                            intros [| [? ?] ?]; intros; simpl in *;
                            try discriminate; auto;
                            repeat destruct_andb; inv_Forall_cons;
                            repeat eq_true_terms; unfold "∘" in *;
                            simpl in *; intuition;
                            eauto_too_dumb; subst; repeat f_equal;
                            match goal with
                            | H: Forall _ ?l |- _ => clear H l
                            end
          end;
      try match goal with
        | IH: Forall _ ?vs1,
          H: _ ?vs1 ?vs2 = true
          |- ?vs1 = ?vs2 => generalize dependent vs2;
                          induction vs1; intros []; intros;
                          try discriminate; try inv_Forall_cons;
                          repeat destruct_andb; intuition;
                          repeat eauto_too_dumb; subst; auto
        end;
      try match goal with
        | IH: F.predfs_data _ ?fs1,
          H: _ ?fs1 ?fs2 = true
          |- ?fs1 = ?fs2 => generalize dependent fs2;
                          induction fs1; intros [| [? ?] ?]; intros;
                          try discriminate; try invert_cons_predfs;
                          try destruct_lifted_andb;
                          repeat destruct_andb; intuition;
                          unfold equiv in *; subst;
                          repeat eauto_too_dumb; subst; auto
        end.
    Qed.

    Lemma eqbv_eq_iff : forall v1 v2 : v, eqbv v1 v2 = true <-> v1 = v2.
    Proof.
      Hint Resolve eqbv_refl : core.
      Hint Resolve eqbv_eq : core.
      intros; split; intros; subst; auto.
    Qed.

    Lemma eqbv_reflect : forall v1 v2, reflect (v1 = v2) (eqbv v1 v2).
    Proof.
      Hint Resolve eqbv_eq_iff : core.
      intros; reflect_split; auto; subst.
      rewrite eqbv_refl in Heqb; discriminate.
    Qed.

(*
    Lemma equivv_dec : forall v1 v2 : v,
        equivv v1 v2 \/ ~ equivv v1 v2.
    Proof.
      intros v1 v2. pose proof equivv_reflect v1 v2 as H.
      inversion H; subst; auto.
    Qed.
*)
  End ValueEquality.
End Values.

(* No tags_t
Arguments VBool {_}.
Arguments VInt {_}.
Arguments VBit {_}.
Arguments VTuple {_}.
Arguments VRecord {_}.
Arguments VHeader {_}.
Arguments VError {_}.
Arguments VMatchKind {_}.
Arguments VHeaderStack {_}.
Arguments LVVar {_}.
Arguments LVMember {_}.
Arguments LVAccess {_}.
Arguments vdefault {_}.
*)

Module ValueNotations.
  Notation "'~{' val '}~'" := val (val custom p4value at level 99).
  Notation "( x )" := x (in custom p4value, x at level 99).
  Notation "x" := x (in custom p4value at level 0, x constr at level 0).
  Notation "'TRUE'" := (VBool true) (in custom p4value at level 0).
  Notation "'FALSE'" := (VBool false) (in custom p4value at level 0).
  Notation "'VBOOL' b" := (VBool b) (in custom p4value at level 0).
  Notation "w 'VW' n" := (VBit w n) (in custom p4value at level 0).
  Notation "w 'VS' n" := (VInt w n) (in custom p4value at level 0).
  Notation "'TUPLE' vs" := (VTuple vs) (in custom p4value at level 0).
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
  Notation "'STACK' vs : ts [ n ] 'NEXT' ':=' ni"
           := (VHeaderStack ts vs n ni)
                (in custom p4value at level 0, no associativity).
End ValueNotations.

Module LValueNotations.
  Notation "'l{' lval '}l'" := lval (lval custom p4lvalue at level 99).
  Notation "( x )" := x (in custom p4lvalue, x at level 99).
  Notation "x" := x (in custom p4lvalue at level 0, x constr at level 0).
  Notation "'VAR' x" := (LVVar x) (in custom p4lvalue at level 0).
  Notation "lval 'DOT' x"
    := (LVMember lval x) (in custom p4lvalue at level 1,
                             lval custom p4lvalue).
  Notation "lval [ n ]"
           := (LVAccess lval n) (in custom p4lvalue at level 1,
                                   lval custom p4lvalue).
End LValueNotations.

Module ValueUtil.
  Import ValueNotations.

  Section Util.
    Context {tags_t : Type}.

    (* TODO: uhhh... *)
    Fail Fixpoint expr_of_value (i : tags_t) (V : v) : E.e tags_t :=
      let fix lrec (vs : list v) : list (E.e tags_t) :=
          match vs with
          | []      => []
          | hv :: tv => expr_of_value i hv :: lrec tv
          end in
      let fix frec (vs : F.fs string v)
          : F.fs string (E.t * E.e tags_t) :=
          match vs with
          | [] => []
          | (x, hv) :: vs => (x, (_, expr_of_value i hv)) :: frec vs (* TODO *)
          end in
      let fix stkrec (hs : list (bool * F.fs string v))
          : list (E.e tags_t) :=
          match hs with
          | [] => []
          | (b, vs) :: hs
            => E.EHeader (frec vs) <{ BOOL b @ i }> i :: stkrec hs
          end in
      match V with
      | ~{ VBOOL b }~ => <{ BOOL b @ i }>
      | ~{ w VW n }~ => <{ w W n @ i }>
      | ~{ w VS z }~ => <{ w S z @ i }>
      | ~{ ERROR err }~ => <{ Error err @ i }>
      | ~{ MATCHKIND mk }~ => <{ Matchkind mk @ i }>
      | ~{ TUPLE vs }~ => E.ETuple (lrec vs) i
      | ~{ REC { vs } }~ => E.ERecord (frec vs) i
      | ~{ HDR { vs } VALID:=b }~
        => E.EHeader (frec vs) <{ BOOL b @ i }> i
      | ~{ STACK vs:ts[n] NEXT:=ni }~
        => E.EHeaderStack ts (stkrec vs) n ni
      end.
  End Util.
End ValueUtil.

Module ValueTyping.
  Import ValueNotations.

  Definition errors : Type := Env.t string unit.

  Reserved Notation "∇ errs ⊢ v ∈ τ"
           (at level 40, v custom p4value, τ custom p4type).

  Inductive type_value (errs : errors) : v -> E.t -> Prop :=
  | typ_bool (b : bool) : ∇ errs ⊢ VBOOL b ∈ Bool
  | typ_bit (w : positive) (n : N) :
      BitArith.bound w n ->
      ∇ errs ⊢ w VW n ∈ bit<w>
  | typ_int (w : positive) (z : Z) :
      IntArith.bound w z ->
      ∇ errs ⊢ w VS z ∈ int<w>
  | typ_tuple (vs : list v)
              (ts : list E.t) :
      Forall2 (fun v τ => ∇ errs ⊢ v ∈ τ) vs ts ->
      ∇ errs ⊢ TUPLE vs ∈ tuple ts
  | typ_rec (vs : Field.fs string v)
            (ts : Field.fs string E.t) :
      Field.relfs (fun vl τ => ∇ errs ⊢ vl ∈ τ) vs ts ->
      ∇ errs ⊢ REC { vs } ∈ rec { ts }
  | typ_hdr (vs : Field.fs string v) (b : bool)
            (ts : Field.fs string E.t) :
      PT.proper_nesting {{ hdr { ts } }} ->
      Field.relfs (fun vl τ => ∇ errs ⊢ vl ∈ τ) vs ts ->
      ∇ errs ⊢ HDR { vs } VALID:=b ∈ hdr { ts }
  | typ_error (err : option string) :
      match err with
      | None => True
      | Some err => errs err = Some tt
      end ->
      ∇ errs ⊢ ERROR err ∈ error
  | typ_matchkind (mk : E.matchkind) :
      ∇ errs ⊢ MATCHKIND mk ∈ matchkind
  | typ_headerstack (ts : Field.fs string E.t)
                    (hs : list (bool * Field.fs string v))
                    (n : positive) (ni : N) :
      BitArith.bound 32%positive (Npos n) -> N.lt ni (Npos n) ->
      Pos.to_nat n = length hs ->
      PT.proper_nesting {{ stack ts[n] }} ->
      Forall
        (fun bvs =>
           let b := fst bvs in
           let vs := snd bvs in
           ∇ errs ⊢ HDR { vs } VALID:=b ∈ hdr { ts }) hs ->
      ∇ errs ⊢ STACK hs:ts[n] NEXT:=ni ∈ stack ts[n]
  where "∇ errs ⊢ vl ∈ τ" := (type_value errs vl τ) : type_scope.

  (** Custom induction for value typing. *)
  Section ValueTypingInduction.
    (** Arbitrary predicate. *)
    Variable P : errors -> v -> E.t -> Prop.

    Hypothesis HBool : forall errs b, P errs ~{ VBOOL b }~ {{ Bool }}.

    Hypothesis HBit : forall errs w n,
        BitArith.bound w n ->
        P errs ~{ w VW n }~ {{ bit<w> }}.

    Hypothesis HInt : forall errs w z,
        IntArith.bound w z ->
        P errs ~{ w VS z }~ {{ int<w> }}.

    Hypothesis HMatchkind : forall errs mk, P errs ~{ MATCHKIND mk }~ {{ matchkind }}.

    Hypothesis HError : forall errs err,
        match err with
        | None => True
        | Some err => errs err = Some tt
        end ->
        P errs ~{ ERROR err }~ {{ error }}.

    Hypothesis HTuple : forall errs vs ts,
        Forall2 (fun v τ => ∇ errs ⊢ v ∈ τ) vs ts ->
        Forall2 (P errs) vs ts ->
        P errs ~{ TUPLE vs }~ {{ tuple ts }}.

    Hypothesis HRecord : forall errs vs ts,
        Field.relfs (fun vl τ => ∇ errs ⊢ vl ∈ τ) vs ts ->
        Field.relfs (fun vl τ => P errs vl τ) vs ts ->
        P errs ~{ REC { vs } }~ {{ rec { ts } }}.

    Hypothesis HHeader : forall errs vs b ts,
        PT.proper_nesting {{ hdr { ts } }} ->
        Field.relfs (fun vl τ => ∇ errs ⊢ vl ∈ τ) vs ts ->
        Field.relfs (fun vl τ => P errs vl τ) vs ts ->
        P errs ~{ HDR { vs } VALID:=b }~ {{ hdr { ts } }}.

    Hypothesis HStack : forall errs ts hs n ni,
        BitArith.bound 32%positive (Npos n) -> N.lt ni (Npos n) ->
        Pos.to_nat n = length hs ->
        PT.proper_nesting {{ stack ts[n] }} ->
        Forall
          (fun bvs =>
             let b := fst bvs in
             let vs := snd bvs in
             ∇ errs ⊢ HDR { vs } VALID:=b ∈ hdr { ts }) hs ->
        Forall
          (fun bvs =>
             let b := fst bvs in
             let vs := snd bvs in
             P errs ~{ HDR { vs } VALID:=b }~ {{ hdr { ts } }}) hs ->
        P errs ~{ STACK hs:ts[n] NEXT:=ni }~ {{ stack ts[n] }}.

    (** Custom induction principle.
        Do [induction ?H using custom_type_value_ind]. *)
    Definition custom_type_value_ind :
      forall (errs : errors) (vl : v) (τ : E.t)
        (Hy : ∇ errs ⊢ vl ∈ τ), P errs vl τ :=
          fix tvind errs vl τ Hy :=
            let fix lind {vs : list v}
                    {ts : list E.t}
                    (HR : Forall2 (fun v τ => ∇ errs ⊢ v ∈ τ) vs ts)
                : Forall2 (P errs) vs ts :=
                match HR with
                | Forall2_nil _ => Forall2_nil _
                | Forall2_cons _ _ Hh Ht => Forall2_cons
                                             _ _
                                             (tvind _ _ _ Hh)
                                             (lind Ht)
                end in
            let fix fsind {vs : Field.fs string v}
                    {ts : Field.fs string E.t}
                    (HR : Field.relfs (fun vl τ => ∇ errs ⊢ vl ∈ τ) vs ts)
                : Field.relfs (fun vl τ => P errs vl τ) vs ts :=
                match HR with
                | Forall2_nil _ => Forall2_nil _
                | Forall2_cons _ _ (conj Hname Hvt)
                               Htail => Forall2_cons
                                         _ _
                                         (conj Hname (tvind _ _ _ Hvt))
                                         (fsind Htail)
                end in
            let fix hsind {hs : list (bool * Field.fs string v)}
                    {ts : Field.fs string E.t}
                    (HR :
                       Forall
                         (fun bvs =>
                            let b := fst bvs in
                            let vs := snd bvs in
                            ∇ errs ⊢ HDR { vs } VALID:=b ∈ hdr { ts }) hs)
                : Forall
                    (fun bvs =>
                       let b := fst bvs in
                       let vs := snd bvs in
                       P errs ~{ HDR { vs } VALID:=b }~ {{ hdr { ts } }}) hs :=
                match HR with
                | Forall_nil _ => Forall_nil _
                | Forall_cons _ Hhead Htail => Forall_cons
                                                _ (tvind _ _ _ Hhead)
                                                (hsind Htail)
                end in
            match Hy with
            | typ_bool _ b => HBool _ b
            | typ_bit _ _ _ Hwn => HBit _ _ _ Hwn
            | typ_int _ _ _ Hwz => HInt _ _ _ Hwz
            | typ_matchkind _ mk => HMatchkind _ mk
            | typ_error _ _ Herr => HError _ _ Herr
            | typ_tuple _ _ _ Hvs => HTuple _ _ _ Hvs (lind Hvs)
            | typ_rec _ _ _ Hfs => HRecord _ _ _ Hfs (fsind Hfs)
            | typ_hdr _ _ b _ HP Hfs => HHeader _ _ b _ HP Hfs (fsind Hfs)
            | typ_headerstack _ _ _ _ _ Hbound Hni Hlen HP
                              Hhs => HStack _ _ _ _ _
                                           Hbound Hni Hlen HP
                                           Hhs (hsind Hhs)
            end.
  End ValueTypingInduction.

  Import F.FieldTactics.

  Lemma vdefault_types :
    forall (errs : errors) (τ : E.t),
      PT.proper_nesting τ ->
      let val := vdefault τ in
      ∇ errs ⊢ val ∈ τ.
  Proof.
    intros errs τ HPN; simpl.
    induction τ using E.custom_t_ind; simpl; constructor; auto.
    - unfold BitArith.bound.
      pose proof BitArith.upper_bound_ge_1 w; lia.
    - unfold IntArith.bound, IntArith.minZ, IntArith.maxZ.
      pose proof IntArith.upper_bound_ge_1 w; lia.
    - inv HPN; try match goal with
                   | H: PT.base_type (E.TTuple _) |- _ => inv H
                   end.
      induction ts as [| t ts IHts]; constructor;
        repeat inv_Forall_cons; intuition.
    - inv HPN; try match goal with
                   | H: PT.base_type {{ rec { _ } }} |- _ => inv H
                   end.
      induction fields as [| [x t] fs IHfs];
      repeat constructor; repeat invert_cons_predfs;
      unfold F.predf_data,"∘", equiv in *; simpl in *; intuition.
    - inv HPN; try match goal with
                   | H: PT.base_type {{ hdr { _ } }} |- _ => inv H
                   end.
      induction fields as [| [x t] fs IHfs];
      repeat constructor; repeat invert_cons_predfs;
      unfold F.predf_data,"∘", equiv in *; simpl in *; intuition.
      apply PT.proper_inside_header_nesting in H3; auto.
    - inv HPN;
        try match goal with
            | H: PT.base_type {{ stack _[_] }} |- _ => inv H
            end; auto.
    - lia.
    - rewrite repeat_length; reflexivity.
    - inv HPN; try match goal with
                   | H: PT.base_type {{ stack _[_] }} |- _ => inv H
                   end.
      apply repeat_Forall; simpl; constructor.
      + apply PT.pn_header; auto.
      + induction fields as [| [x t] fs IHfs];
        repeat constructor; repeat invert_cons_predfs;
        unfold F.predf_data,"∘", equiv in *; simpl in *; intuition.
        apply PT.proper_inside_header_nesting in H4; auto.
  Qed.
End ValueTyping.
End Val.
