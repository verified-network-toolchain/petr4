Require Import Poulet4.Semantics Poulet4.Typed
        Poulet4.Syntax Coq.NArith.BinNat Coq.Lists.List
        Poulet4.Value Coq.micromega.Lia Poulet4.Utils.
Import ListNotations.
Require Poulet4.P4String.

Section ValueTyping.
  Context {tags_t : Type}.

  Notation typ := (@P4Type tags_t).

  Section Val.
    Context {A : Type}.
    Notation V := (@ValueBase tags_t A).
    Notation senum_env := (@IdentMap.t tags_t (P4String.AList tags_t V)).
    
    (* TODO:
       What constraints do we need on:
       - fixed-width numeric types?
       - headers (unions & stacks)?
       - senum values: see comments below.
       - needs to be parameterized by bit type. *)

    Variable (gsenum : senum_env).

    Inductive val_typ : V -> typ -> Prop :=
    | typ_null :
        val_typ ValBaseNull TypVoid
    | typ_bool : forall b,
        val_typ (ValBaseBool b) TypBool
    | typ_integer : forall v,
        val_typ (ValBaseInteger v) TypInteger
    | typ_bit : forall v,
        val_typ (ValBaseBit v) (TypBit (N.of_nat (length v)))
    | typ_int : forall v,
        val_typ (ValBaseInt v) (TypInt (N.of_nat (length v)))
    | typ_varbit : forall n v,
        N.to_nat n < length v ->
        val_typ (ValBaseVarbit n v) (TypVarBit n)
    | typ_string : forall s,
        val_typ (ValBaseString s) TypString
    | typ_tuple : forall vs ts,
        Forall2 val_typ vs ts ->
        val_typ (ValBaseTuple vs) (TypTuple ts)
    | typ_record : forall vs ts,
        AList.all_values val_typ vs ts ->
        val_typ (ValBaseRecord vs) (TypRecord ts)
    | typ_error : forall err,
        val_typ (ValBaseError err) TypError
    | typ_matchkind : forall mk,
        val_typ (ValBaseMatchKind mk) TypMatchKind
    | typ_struct : forall vs ts,
        AList.all_values val_typ vs ts ->
        val_typ (ValBaseStruct vs) (TypStruct ts)
    | typ_header : forall b vs ts,
        AList.all_values val_typ vs ts ->
        val_typ (ValBaseHeader vs b) (TypHeader ts)
    | typ_union : forall vs ts,
        AList.all_values val_typ vs ts ->
        val_typ (ValBaseUnion vs) (TypHeaderUnion ts)
    | typ_stack : forall s n vs ts,
        length vs = N.to_nat s ->
        Forall (fun v => val_typ v (TypHeader ts)) vs ->
        val_typ (ValBaseStack vs s n) (TypArray (TypHeader ts) n)
    | typ_enumfield : forall ename member members,
        In member members ->
        val_typ
          (ValBaseEnumField ename member)
          (TypEnum ename None members)
    | typ_senumfield : forall ename member v t fields,
        IdentMap.get ename gsenum = Some fields ->
        AList.get fields member = Some v ->
        val_typ v t ->
        val_typ
          (ValBaseSenumField ename member v)
          (TypEnum ename (Some t) (List.map fst fields))
    (* TODO: what is a [ValBaseSenum _], and what is its type?
       It seems to be something in [gsenum],
       but should it be a value? *)
    (*| typ_senum : forall fields ename t,
        IdentMap.get ename gsenum = Some fields ->
        Forall (fun xv => val_typ gsenum (snd xv) t) fields ->
        val_typ
          gsenum (ValBaseSenum fields)
          (TypEnum ename (Some t) (List.map fst fields))*).

    Section ValTypInd.
      Variable P : V -> typ -> Prop.

      Hypothesis HNull : P ValBaseNull TypVoid.
      Hypothesis HBool : forall b, P (ValBaseBool b) TypBool.
      Hypothesis HInteger : forall z, P (ValBaseInteger z) TypInteger.
      Hypothesis HBit : forall bits,
          P (ValBaseBit bits) (TypBit (N.of_nat (length bits))).
      Hypothesis HInt : forall bits,
          P (ValBaseInt bits) (TypInt (N.of_nat (length bits))).
      Hypothesis HVarbit : forall n bits,
          N.to_nat n < length bits ->
          P (ValBaseVarbit n bits) (TypVarBit n).
      Hypothesis HString : forall s,
          P (ValBaseString s) TypString.
      Hypothesis HTuple : forall vs ts,
          Forall2 val_typ vs ts ->
          Forall2 P vs ts ->
          P (ValBaseTuple vs) (TypTuple ts).
      Hypothesis HRecord : forall vs ts,
          AList.all_values val_typ vs ts ->
          AList.all_values P vs ts ->
          P (ValBaseRecord vs) (TypRecord ts).
      Hypothesis HError : forall err,
          P (ValBaseError err) TypError.
      Hypothesis HMatchkind : forall mk,
          P (ValBaseMatchKind mk) TypMatchKind.
      Hypothesis HStruct : forall vs ts,
          AList.all_values val_typ vs ts ->
          AList.all_values P vs ts ->
          P (ValBaseStruct vs) (TypStruct ts).
      Hypothesis HHeader : forall b vs ts,
          AList.all_values val_typ vs ts ->
          AList.all_values P vs ts ->
          P (ValBaseHeader vs b) (TypHeader ts).
      Hypothesis HUnion : forall vs ts,
          AList.all_values val_typ vs ts ->
          AList.all_values P vs ts ->
          P (ValBaseUnion vs) (TypHeaderUnion ts).
      Hypothesis HStack : forall s n vs ts,
          length vs = N.to_nat s ->
          Forall (fun v => val_typ v (TypHeader ts)) vs ->
          Forall (fun v => P v (TypHeader ts)) vs ->
          P (ValBaseStack vs s n) (TypArray (TypHeader ts) n).
      Hypothesis HEnum : forall ename member members,
          In member members ->
          P
            (ValBaseEnumField ename member)
            (TypEnum ename None members).
      Hypothesis HSenum : forall ename member v t fields,
          IdentMap.get ename gsenum = Some fields ->
          AList.get fields member = Some v ->
          val_typ v t ->
          P v t ->
          P
            (ValBaseSenumField ename member v)
            (TypEnum ename (Some t) (List.map fst fields)).

      Definition custom_val_typ_ind :
        forall (v : V) (t : typ), val_typ v t -> P v t :=
        fix vtind (v : V) (t : typ) (H : val_typ v t) : P v t :=
          let fix lind {vs : list V} {ts : list typ}
                  (H : Forall2 val_typ vs ts)
              : Forall2 P vs ts :=
              match H with
              | Forall2_nil _ => Forall2_nil _
              | Forall2_cons _ _ Hh Ht =>
                Forall2_cons _ _ (vtind _ _ Hh) (lind Ht)
              end in
          let fix alind
                  {vs : AList.AList (P4String.t _) V _}
                  {ts : AList.AList (P4String.t _) typ _}
                  (H : AList.all_values val_typ vs ts)
              : AList.all_values P vs ts :=
              match H with
              | Forall2_nil _ => Forall2_nil _
              | Forall2_cons _ _ (conj Hx Hh) Ht =>
                Forall2_cons _ _ (conj Hx (vtind _ _ Hh)) (alind Ht)
              end in
          let fix same_typ_ind {vs : list V} {t : typ}
                  (H : Forall (fun v => val_typ v t) vs)
              : Forall (fun v => P v t) vs :=
              match H with
              | Forall_nil _ => Forall_nil _
              | Forall_cons _ Hh Ht =>
                Forall_cons _ (vtind _ _ Hh) (same_typ_ind Ht)
              end in
          match H with
          | typ_null => HNull
          | typ_bool b => HBool b
          | typ_integer z => HInteger z
          | typ_bit bits => HBit bits
          | typ_int bits => HInt bits
          | typ_varbit _ _ H => HVarbit _ _ H
          | typ_string s => HString s
          | typ_tuple _ _ H => HTuple _ _ H (lind H)
          | typ_record _ _ H => HRecord _ _ H (alind H)
          | typ_error err => HError err
          | typ_matchkind mk => HMatchkind mk
          | typ_struct _ _ H => HStruct _ _ H (alind H)
          | typ_header b _ _ H => HHeader b _ _ H (alind H)
          | typ_union _ _ H => HUnion _ _ H (alind H)
          | typ_stack _ n _ _ Hl H => HStack _ n _ _ Hl H (same_typ_ind H)
          | typ_enumfield x _ _ H => HEnum x _ _ H
          | typ_senumfield _ _ _ _ _ H1 H2 Hv =>
            HSenum _ _ _ _ _ H1 H2 Hv (vtind _ _ Hv)
          end.
    End ValTypInd.
  End Val.

  Section RelTyp.
    Context {A B : Type}.
    Notation VA := (@ValueBase tags_t A).
    Notation VB := (@ValueBase tags_t B).

    Local Hint Constructors val_typ : core.
    
    Section Map.
      Variable (f : A -> B).
      
      Lemma ValueBaseMap_preserves_type : forall gs v t,
          val_typ gs v t ->
          val_typ
            (FuncAsMap.map_map (AList.map_values (ValueBaseMap f)) gs)
            (ValueBaseMap f v) t.
      Proof.
        intros gs v t Hv;
          induction Hv using @custom_val_typ_ind;
          simpl in *; auto.
        - replace (length bits)
            with (length (map f bits))
            by (rewrite map_length; reflexivity); auto.
        - replace (length bits)
            with (length (map f bits))
            by (rewrite map_length; reflexivity); auto.
        - constructor; rewrite map_length; auto.
        - rewrite Forall2_map_l in H0; auto.
        - constructor.
          unfold AList.all_values in *.
          rewrite Forall2_conj in *;
            destruct H0 as [Hnames Hvts]; split.
          + clear Hvts.
            rewrite Forall2_map_both in *.
            rewrite map_fst_map, map_id.
            assumption.
          + clear Hnames.
            rewrite Forall2_map_both, map_snd_map,
            map_map, <- Forall2_map_both.
            assumption.
        - constructor.
          unfold AList.all_values in *.
          rewrite Forall2_conj in *;
            destruct H0 as [Hnames Hvts]; split.
          + clear Hvts.
            rewrite Forall2_map_both in *.
            rewrite map_fst_map, map_id.
            assumption.
          + clear Hnames.
            rewrite Forall2_map_both, map_snd_map,
            map_map, <- Forall2_map_both.
            assumption.
        - constructor.
          unfold AList.all_values in *.
          rewrite Forall2_conj in *;
            destruct H0 as [Hnames Hvts]; split.
          + clear Hvts.
            rewrite Forall2_map_both in *.
            rewrite map_fst_map, map_id.
            assumption.
          + clear Hnames.
            rewrite Forall2_map_both, map_snd_map,
            map_map, <- Forall2_map_both.
            assumption.
        - constructor.
          unfold AList.all_values in *.
          rewrite Forall2_conj in *;
            destruct H0 as [Hnames Hvts]; split.
          + clear Hvts.
            rewrite Forall2_map_both in *.
            rewrite map_fst_map, map_id.
            assumption.
          + clear Hnames.
            rewrite Forall2_map_both, map_snd_map,
            map_map, <- Forall2_map_both.
            assumption.
        - constructor.
          + rewrite map_length; assumption.
          + rewrite Forall_map.
            unfold Basics.compose.
            assumption.
        - replace (map fst fields) with
              (map fst (AList.map_values (ValueBaseMap f) fields)).
          constructor; auto.
          + unfold IdentMap.get,
            FuncAsMap.get, FuncAsMap.map_map in *.
            rewrite H; reflexivity.
          + rewrite AList.get_map_values, H0; reflexivity.
          + unfold AList.map_values.
            rewrite map_fst_map, map_id; reflexivity.
      Qed.
    End Map.

    Section Rel.
      Variable (R : A -> B -> Prop).
      
      Lemma exec_val_preserves_typ : forall va vb,
          exec_val R va vb ->
          forall gsa gsb t,
            FuncAsMap.related
              (AList.all_values (exec_val R))
              gsa gsb ->
            val_typ gsa va t -> val_typ gsb vb t.
      Proof.
        (* TODO: need induction principle for [exec_val]. *)
      Admitted.
    End Rel.
  End RelTyp.
End ValueTyping.
    
Section TypingDefs.
  Context {tags_t : Type} {dummy : Inhabitant tags_t}.

  Notation typ := (@P4Type tags_t).
  Notation expr := (@Expression tags_t).
  Notation stmt := (@Statement tags_t).
  Notation signal := (@signal tags_t).
  Notation ident := (P4String.t tags_t).
  Notation path := (list ident).
  Notation Sval := (@ValueBase tags_t (option bool)).

  (** Typing context. *)
  Definition gamma : Type := @PathMap.t tags_t typ.

  (** TODO: is this correct? *)
  Definition typ_of_loc (l : Locator) (g : gamma) : option typ :=
    match l with
    | LInstance p => PathMap.get p g
    | LGlobal   p => PathMap.get p g
    end.

  Context `{T : @Target tags_t expr}.

  Notation run_expr := (@exec_expr tags_t dummy T).
  Notation run_stmt := (@exec_stmt tags_t dummy T).

  Definition envs_same (g : gamma) (st : state) : Prop :=
    forall p : path, PathMap.get p g = None <-> PathMap.get p (fst st) = None.

  Lemma envs_same_some_l : forall g st p t,
      envs_same g st -> PathMap.get p g = Some t ->
      exists v, PathMap.get p (fst st) = Some v.
  Proof.
    intros g st p t H Hgt; unfold envs_same in H.
    destruct (PathMap.get p (fst st)) as [v |] eqn:Heq; eauto.
    rewrite <- H, Hgt in Heq; discriminate.
  Qed.

  Lemma envs_same_some_r : forall g st p v,
      envs_same g st -> PathMap.get p (fst st) = Some v ->
      exists t, PathMap.get p g = Some t.
  Proof.
    intros g st p v H Hgt; unfold envs_same in H.
    destruct (PathMap.get p g) as [? |] eqn:Heq; eauto.
    rewrite H,Hgt in Heq; discriminate.
  Qed.
  
  Definition envs_type (gsenum : genv_senum) (g : gamma) (st : state) : Prop :=
    forall (p : path) (t : typ) (v : Sval),
      PathMap.get p g = Some t ->
      PathMap.get p (fst st) = Some v -> val_typ gsenum v t.

  Definition typ_of_expr (e : expr) : typ :=
    match e with
    | MkExpression _ _ t _ => t
    end.
  (**[]*)
  
  (** Expression typing. *)
  Definition expr_types (g : gamma) (e : expr) : Prop :=
    forall (read_one_bit : option bool -> bool -> Prop)
      (ge : genv) (p : path) (st : state),
      envs_same g st -> envs_type ge g st ->
      (exists v, run_expr ge read_one_bit p st e v) /\
      forall v, run_expr ge read_one_bit p st e v ->
           val_typ (ge_senum ge) v (typ_of_expr e).
  (**[]*)

  (** Statement typing. *)
  Definition stmt_types (g g' : gamma) (s : stmt) : Prop :=
    forall (read_one_bit : option bool -> bool -> Prop)
      (ge : genv) (p : path) (st : state),
      envs_same g st -> envs_type ge g st ->
      (exists st' sig, run_stmt ge read_one_bit p st s st' sig) /\
      forall st' sig, run_stmt ge read_one_bit p st s st' sig ->
                 envs_same g' st' /\ envs_type ge g' st'.
End TypingDefs.

Notation "Γ '⊢e' e"
  := (expr_types Γ e) (at level 80, no associativity) : type_scope.
Notation "Γ1 '⊢s' s ⊣ Γ2"
  := (stmt_types Γ1 Γ2 s) (at level 80, no associativity) : type_scope.

(* TODO. *)
Section Soundness.
  Context {tags_t : Type} {dummy : Inhabitant tags_t}.

  Notation typ := (@P4Type tags_t).
  Notation expr := (@Expression tags_t).
  Notation stmt := (@Statement tags_t).
  Notation signal := (@signal tags_t).
  Notation ident := (P4String.t tags_t).
  Notation path := (list ident).
  Notation Sval := (@ValueBase tags_t (option bool)).

  Context `{T : @Target tags_t expr}.

  Notation run_expr := (@exec_expr tags_t dummy T).
  Notation run_stmt := (@exec_stmt tags_t dummy T).

  Variable (Γ : @gamma tags_t).

  Local Hint Unfold expr_types : core.
  Local Hint Constructors exec_expr : core.
  Local Hint Constructors val_typ : core.
  
  Ltac soundtac :=
    autounfold with *;
    intros rob ge p st Henvs Henvt;
    split; eauto;
    try (intros v Hrn; inversion Hrn; subst; cbn; eauto).
  
  Lemma bool_sound : forall tag b dir,
      Γ ⊢e MkExpression tag (ExpBool b) TypBool dir.
  Proof.
    intros; soundtac.
  Qed.
  
  Lemma arbitrary_int_sound : forall tag i z dir,
      Γ ⊢e
        MkExpression
        tag (ExpInt (P4Int.Build_t _ i z None)) TypInteger dir.
  Proof.
    intros; soundtac.
  Qed.

  Lemma unsigned_int_sound : forall tag i z w dir,
      Γ ⊢e
        MkExpression
        tag (ExpInt (P4Int.Build_t _ i z (Some (w,false)))) (TypBit w) dir.
  Proof.
    intros tag i z dir; soundtac.
    (* TODO: need some result about [P4Arith.to_loptbool]. *)
  Admitted.

  Lemma signed_int_sound : forall tag i z w dir,
      Γ ⊢e
        MkExpression
        tag (ExpInt (P4Int.Build_t _ i z (Some (w,true)))) (TypInt w) dir.
  Proof.
    intros tag i z dir; soundtac.
    (* TODO: need some result about [P4Arith.to_loptbool]. *)
  Admitted.

  Lemma string_sound : forall tag s dir,
      Γ ⊢e MkExpression tag (ExpString s) TypString dir.
  Proof.
    intros; soundtac.
  Qed.

  Lemma name_sound : forall tag x loc t dir,
      typ_of_loc loc Γ = Some t ->
      Γ ⊢e MkExpression tag (ExpName x loc) t dir.
  Proof.
    intros i x l t d Hgt; soundtac.
    - destruct l as [lp | lp]; simpl in Hgt;
        eapply envs_same_some_l in Hgt as [v Hv]; eauto.
      exists v. constructor; simpl.
      (** TODO:
          1. Need type preservation to [eval_val_to_sval].
          2. Perhaps [envs_same] needs to include [genv]. *)
      admit.
    - destruct l as [lp | lp]; simpl in Hgt;
        simpl in *; eauto.
  Abort.

  Lemma array_access_sound : forall tag arry idx ts dir n,
      typ_of_expr arry = TypArray (TypHeader ts) n ->
      typ_of_expr idx  = TypBit n ->
      Γ ⊢e arry ->
      Γ ⊢e idx ->
      Γ ⊢e MkExpression tag (ExpArrayAccess arry idx) (TypHeader ts) dir.
  Proof.
    intros i e1 e2 ts d n Ht1 Ht2 He1 He2;
      autounfold with * in *.
    intros rob ge p st Henvs Henvt.
    pose proof He1 rob ge p st Henvs Henvt as [[v1 Hev1] He1']; clear He1.
    pose proof He2 rob ge p st Henvs Henvt as [[v2 Hev2] He2']; clear He2.
    split.
    - pose proof He1' v1 Hev1 as Hv1.
      pose proof He2' v2 Hev2 as Hv2.
      rewrite Ht1 in Hv1; rewrite Ht2 in Hv2.
      inversion Hv1; inversion Hv2; subst.
      (* Need to know [N_of_value idx < n]. *) admit.
    - intros v' Haa; inversion Haa; clear Haa; subst; simpl.
      rename H4 into He2; rename H10 into He1;
        rename H7 into Hsval; rename H9 into Haa;
          rename H11 into Huninit.
      pose proof He1' _ He1 as Hv1.
      pose proof He2' _ He2 as Hv2.
      rewrite Ht1 in Hv1; rewrite Ht2 in Hv2.
      inversion Hv1; inversion Hv2; subst.
      (* Need result about [Znth_def]. *)
  Abort.

  Lemma bigstring_access_sound : forall tag bits lo hi dir w,
      (lo <= hi < w)%N ->
      typ_of_expr bits = TypBit w ->
      Γ ⊢e bits ->
      Γ ⊢e MkExpression
        tag (ExpBitStringAccess bits lo hi)
        (TypBit (hi - lo + 1)%N) dir.
  Proof.
    intros i e lo hi d w Hlwh Ht He.
    autounfold with * in *.
    intros rob ge p st Henvs Henvt.
    pose proof He rob ge p st Henvs Henvt as [[v Hev] He']; clear He.
    split.
    - apply He' in Hev as Hv; rewrite Ht in Hv;
        inversion Hv; subst; rename v0 into bits.
      exists (ValBaseBit (bitstring_slice bits (N.to_nat lo) (N.to_nat hi))).
      eapply exec_expr_bitstring_access with (wn := length bits); eauto; lia.
    - clear v Hev. intros v Hrn; inversion Hrn; subst; simpl.
      rename H8 into He; rename H9 into Hsval; rename H12 into Hlhw.
      (* Need result about [bitstring_slice]. *) admit.
  Admitted.
  
  Lemma list_sound : forall tag es dir,
      Forall (fun e => Γ ⊢e e) es ->
      Γ ⊢e MkExpression tag (ExpList es)
        (TypTuple (map typ_of_expr es)) dir.
  Proof.
    intros i es d Hes. autounfold with * in *.
    intros rob ge p st Henvs Henvt.
    rewrite Forall_forall in Hes.
      specialize Hes with
          (read_one_bit:=rob) (ge:=ge) (p:=p) (st:=st).
      pose proof reduce_inner_impl _ _ _ _ Hes Henvs as Hes';
        simpl in Hes'; clear Hes.
      pose proof reduce_inner_impl _ _ _ _ Hes' Henvt as Hes;
        simpl in Hes; clear Hes'.
      rewrite split_impl_conj in Hes.
      destruct Hes as [Hrnes Htyps]. split.
    - clear Htyps; rewrite <- Forall_forall in Hrnes.
      rewrite Forall_exists_factor in Hrnes.
      destruct Hrnes as [vs Hvs]; eauto.
    - clear Hrnes; intros v Hrn; simpl.
      inversion Hrn; subst; clear Hrn.
      rename H6 into Hesvs.
      apply forall_Forall2 with (bs := vs) in Htyps;
        eauto using Forall2_length.
      apply Forall2_impl with
          (R := run_expr ge rob p st)
          (Q := fun e v => val_typ (ge_senum ge) v (typ_of_expr e)) in Htyps; auto.
      rewrite Forall2_flip, Forall2_map_r in Htyps; auto.
  Qed.
  
  Lemma record_sound : forall tag es dir,
      Forall (fun e => Γ ⊢e e) (map snd es) ->
      Γ ⊢e
        MkExpression
        tag (ExpRecord es)
        (TypRecord (map (fun '(x,e) => (x,typ_of_expr e)) es)) dir.
  Proof.
    intros i es d Hes.
    autounfold with * in *.
    intros rob ge p st Henvs Henvt.
    rewrite Forall_forall in Hes.
    specialize Hes with
        (read_one_bit:=rob) (ge:=ge) (p:=p) (st:=st).
    pose proof reduce_inner_impl _ _ _ _ Hes Henvs as Hes';
      simpl in Hes'; clear Hes.
    pose proof reduce_inner_impl _ _ _ _ Hes' Henvt as Hes;
      simpl in Hes; clear Hes'.
    rewrite split_impl_conj in Hes.
    destruct Hes as [Hrns Htyps]. split.
    - clear Htyps. rewrite <- Forall_forall in Hrns.
      rewrite Forall_exists_factor in Hrns.
      destruct Hrns as [vs Hvs].
      rewrite AList.Forall2_all_values
        with (ks := map fst es) in Hvs.
      + rewrite combine_map_fst_snd in Hvs; eauto.
      + repeat rewrite map_length; reflexivity.
      + rewrite map_length, <- map_length with (f := snd).
        eauto using Forall2_length.
    - clear Hrns; intros v Hrns.
      inversion Hrns; subst.
      rename H6 into Heskvs.
      rewrite <- combine_map_fst_snd with (l := es)   in Heskvs.
      rewrite <- combine_map_fst_snd with (l := kvs') in Heskvs.
      apply AList.all_values_keys_eq in Heskvs as Hmf.
      repeat rewrite combine_map_fst_snd in Hmf.
      rewrite <- Hmf in Heskvs.
      rewrite <- AList.Forall2_all_values in Heskvs.
      + constructor; unfold AList.all_values;
          rewrite Forall2_conj; split.
        * rewrite Forall2_map_both, Forall2_eq,
          map_fst_map, map_id; auto.
        * rewrite Forall2_map_both.
          rewrite map_snd_map.
          assert (Hl : length es = length kvs').
          { rewrite <- map_length with (f := fst) (l := es).
            rewrite <- map_length with (f := fst) (l := kvs'), Hmf.
            reflexivity. }
          rewrite <- map_length with (f := snd) (l := es) in Hl.
          rewrite <- map_length with (f := snd) (l := kvs') in Hl.
          pose proof forall_Forall2 _ _ _ _ Htyps (map snd kvs') Hl as Hff2.
          apply Forall2_impl with
              (R := run_expr ge rob p st)
              (Q := fun e v => val_typ (ge_senum ge) v (typ_of_expr e)) in Hff2; auto.
          rewrite Forall2_flip,Forall2_map_r in Hff2; assumption.
      + repeat rewrite map_length; reflexivity.
      + rewrite Hmf; repeat rewrite map_length; reflexivity.
  Qed.

  (** Evidence for a type being a numeric of a given width. *)
  Inductive numeric_width (w : N) : typ -> Prop :=
  | numeric_width_bit : numeric_width w (TypBit w)
  | numeric_width_int : numeric_width w (TypInt w).

  Ltac inv_numeric_width :=
    match goal with
    | H: numeric_width _ _ |- _ => inversion H; subst
    end.
  
  (** Evidence for a type being numeric. *)
  Inductive numeric : typ -> Prop :=
  | NumericFixed (w : N) τ :
      numeric_width w τ -> numeric τ
  | NumericArbitrary :
      numeric TypInteger.

  Ltac inv_numeric :=
    match goal with
    | H: numeric _ |- _ => inversion H; subst; try inv_numeric_width
    end.

  (** Evidence a unary operation is valid for a type. *)
  Inductive unary_type : OpUni -> typ -> typ -> Prop :=
  | UTBool :
      unary_type Not TypBool TypBool
  | UTBitNot w τ :
      numeric_width w τ -> unary_type BitNot τ τ
  | UTUMinus τ :
      numeric τ -> unary_type UMinus τ τ.

  Local Hint Constructors exec_val : core.
  Local Hint Unfold read_detbit : core.
  Local Hint Unfold sval_to_val : core.
  Local Hint Unfold val_to_sval : core.
  
  Lemma val_to_sval_ex : forall v,
      @val_to_sval tags_t v (ValueBaseMap Some v).
  Proof.
    autounfold with *; intro v.
    induction v using (custom_ValueBase_ind bool); simpl; eauto.
    - constructor.
      rewrite <- Forall2_map_r, Forall2_Forall, Forall_forall.
      reflexivity.
    - constructor.
      rewrite <- Forall2_map_r, Forall2_Forall, Forall_forall.
      reflexivity.
    - constructor.
      rewrite <- Forall2_map_r, Forall2_Forall, Forall_forall.
      reflexivity.
    - constructor.
      rewrite <- Forall2_map_r, Forall2_Forall.
      assumption.
    - constructor. unfold AList.all_values.
      rewrite <- Forall2_map_r, Forall2_Forall.
      rewrite Forall_snd in H.
      apply Forall_and; rewrite Forall_forall in *;
        intros [? ?]; firstorder.
    - constructor. unfold AList.all_values.
      rewrite <- Forall2_map_r, Forall2_Forall.
      rewrite Forall_snd in H.
      apply Forall_and; rewrite Forall_forall in *;
        intros [? ?]; firstorder.
    - constructor; auto. unfold AList.all_values.
      rewrite <- Forall2_map_r, Forall2_Forall.
      rewrite Forall_snd in H.
      apply Forall_and; rewrite Forall_forall in *;
        intros [? ?]; firstorder.
    - constructor. unfold AList.all_values.
      rewrite <- Forall2_map_r, Forall2_Forall.
      rewrite Forall_snd in H.
      apply Forall_and; rewrite Forall_forall in *;
        intros [? ?]; firstorder.
    - constructor.
      rewrite <- Forall2_map_r, Forall2_Forall.
      assumption.
  Qed.

  Local Hint Resolve val_to_sval_ex : core.

  Lemma unary_type_eq : forall o t t', unary_type o t t' -> t = t'.
  Proof.
    intros ? ? ? H; inversion H; subst; auto.
  Qed.
  
  Lemma unary_op_sound : forall tag o e t dir,
      unary_type o (typ_of_expr e) t ->
      Γ ⊢e e ->
      Γ ⊢e MkExpression tag (ExpUnaryOp o e) t dir.
  Proof.
    intros i o e t d Hut He.
    autounfold with * in *;
      intros rob ge p st Henvs Henvt.
    specialize He with rob ge p st.
    pose proof He Henvs Henvt as [[v Hev] Hvt]; clear He; split.
    - apply Hvt in Hev as Hv; clear Hvt.
      assert (exists v', sval_to_val rob v v').
      { admit. }
      (* Need predicate that [rob v v'] holds in [expr_types]... *)
      destruct H as [v' Hv'].
      destruct (Ops.Ops.eval_unary_op o v') as [v'' |] eqn:Heqop; eauto.
      inversion Hut; subst; try inv_numeric; try inv_numeric_width;
        match goal with
        | H: _ = typ_of_expr ?e,
             Hv: val_typ _ ?v (typ_of_expr ?e),
                 Hv': sval_to_val _ ?v _
          |- _ => rewrite <- H in *; inversion Hv; inversion Hv'; subst
        end; simpl in *; try discriminate.
    - clear v Hev; intros v Hev.
      inversion Hev; subst; simpl in *.
      pose proof Hvt _ H7 as Hargsv.
      (* Need to know:
         - [forall o t t', unary_type o t t' -> t = t']
         - [forall f g t v v', exec_val f v v' -> val_typ g v t -> val_typ g v' t]
         - [forall o v v' g t, eval_unary_op o v = Some v' -> val_typ g v t -> val_typ g v' t].
         Requires a parameterized [val_typ]. *)
  Abort.
End Soundness.
