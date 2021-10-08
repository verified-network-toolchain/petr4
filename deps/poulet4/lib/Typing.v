Require Import Poulet4.Semantics Poulet4.Typed
        Poulet4.Syntax Coq.NArith.BinNat Coq.Lists.List
        Poulet4.Value Coq.micromega.Lia.
Import ListNotations.
Require Poulet4.P4String.

(* TODO: move to utility module. *)
Lemma combine_map_fst_snd : forall (U V : Type) (l : list (U * V)),
    combine (map fst l) (map snd l) = l.
Proof.
  intros U V l; induction l as [| [u v] l IHl];
    simpl; f_equal; auto.
Qed.

Lemma map_fst_combine : forall (U V : Type) (us : list U) (vs : list V),
    length us = length vs ->
    map fst (combine us vs) = us.
Proof.
  intros U V us; induction us as [| u us IHus];
    intros [| v vs] Hl; simpl in *;
      inversion Hl; subst; f_equal; auto.
Qed.

Lemma map_snd_combine : forall (U V : Type) (us : list U) (vs : list V),
    length us = length vs ->
    map snd (combine us vs) = vs.
Proof.
  intros U V us; induction us as [| u us IHus];
    intros [| v vs] Hl; simpl in *;
      inversion Hl; subst; f_equal; auto.
Qed.

Lemma reduce_inner_impl : forall (A : Type) (Q : Prop) (P R : A -> Prop),
    (forall a, P a -> Q -> R a) -> Q -> forall a, P a -> R a.
Proof.
  intuition.
Qed.

Lemma split_impl_conj : forall (A : Type) (P Q R : A -> Prop),
    (forall a, P a -> Q a /\ R a) <->
    (forall a, P a -> Q a) /\ forall a, P a -> R a.
Proof.
  firstorder.
Qed.

Lemma Forall_exists_factor : forall (A B : Type) (R : A -> B -> Prop) (l : list A),
    Forall (fun a => exists b, R a b) l <-> exists bs, Forall2 R l bs.
Proof.
  intros A B R l; split.
  - intro H; induction H; eauto.
    destruct H as [b HRb];
      destruct IHForall as [bs HRbs]; eauto.
  - intros [bs HRlbs].
    induction HRlbs; eauto.
Qed.

Lemma forall_Forall2 : forall (A B : Type) (R : A -> B -> Prop) (l : list A),
    (forall a, In a l -> forall b, R a b) ->
    forall bs, length l = length bs -> Forall2 R l bs.
Proof.
  intros A B R l;
    induction l as [| a l IHl];
    intros H [| b bs] Hbs; simpl in *; try discriminate; auto.
Qed.

Lemma Forall2_length : forall (A B : Type) (R : A -> B -> Prop) la lb,
    Forall2 R la lb -> length la = length lb.
Proof.
  intros A B R la lb H; induction H;
    simpl; f_equal; auto.
Qed.

Lemma Forall2_impl : forall (A B : Type) (R Q : A -> B -> Prop) la lb,
    Forall2 (fun a b => R a b -> Q a b) la lb ->
    Forall2 R la lb -> Forall2 Q la lb.
Proof.
  intros A B R Q la lb HRQ HR;
    induction HRQ; inversion HR; subst; auto.
Qed.

Lemma Forall2_flip : forall (A B : Type) (R : A -> B -> Prop) la lb,
    Forall2 (fun b a => R a b) lb la <-> Forall2 R la lb.
Proof.
  intros A B R la lb; split; intros H;
    induction H; auto.
Qed.

Lemma Forall2_conj : forall (U V : Type) (R Q : U -> V -> Prop) us vs,
    Forall2 (fun u v => R u v /\ Q u v) us vs <->
    Forall2 R us vs /\ Forall2 Q us vs.
Proof.
  intros U V R Q us vs; split.
  - intros H; induction H; simpl in *; intuition.
  - intros [HR HQ]; induction HR; inversion HQ;
      simpl in *; auto.
Qed.

Lemma Forall2_map_l : forall (A B C : Type) (R : A -> B -> Prop) (f : C -> A) lc lb,
    Forall2 (fun c b => R (f c) b) lc lb <-> Forall2 R (map f lc) lb.
Proof.
  intros A B C R f lc lb; split; intros H.
  - induction H; simpl in *; auto.
  - remember (map f lc) as la eqn:Heqla;
      generalize dependent lc.
    induction H; intros [| ? ?] Heqla;
      simpl in *; inversion Heqla; subst; auto.
Qed.

Lemma Forall2_map_r : forall (A B C : Type) (R : A -> B -> Prop) (f : C -> B) la lc,
    Forall2 (fun a c => R a (f c)) la lc <-> Forall2 R la (map f lc).
Proof.
  intros A B C R f la lc; split; intros H.
  - induction H; simpl in *; auto.
  - remember (map f lc) as mflc eqn:Hmflc.
    generalize dependent lc.
    induction H; intros lc Hmflc.
    + symmetry in Hmflc; apply map_eq_nil in Hmflc; subst; auto.
    + destruct lc as [| c lc]; simpl in *;
        inversion Hmflc; subst; auto.
Qed.

Lemma Forall2_map_both :
  forall (T U V W : Type) (R : V -> W -> Prop) (f : T -> V) (g : U -> W) ts us,
    Forall2 (fun t u => R (f t) (g u)) ts us <-> Forall2 R (map f ts) (map g us).
Proof.
  intros; rewrite <- Forall2_map_l, <- Forall2_map_r; reflexivity.
Qed.

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

  (* TODO:
     What constraints do we need on:
     - fixed-width numeric types?
     - headers (unions & stacks)?
     - senum values: see comments below.
   *)
  Inductive val_typ (gsenum : genv_senum) : Sval -> typ -> Prop :=
  | typ_null : val_typ gsenum ValBaseNull TypVoid
  | typ_bool : forall b, val_typ gsenum (ValBaseBool b) TypBool
  | typ_integer : forall v, val_typ gsenum (ValBaseInteger v) TypInteger
  | typ_bit : forall v,
      val_typ gsenum (ValBaseBit v) (TypBit (N.of_nat (length v)))
  | typ_int : forall v,
      val_typ gsenum (ValBaseInt v) (TypInt (N.of_nat (length v)))
  | typ_varbit : forall n v,
      N.to_nat n < length v ->
      val_typ gsenum (ValBaseVarbit n v) (TypVarBit n)
  | typ_string : forall s,
      val_typ gsenum (ValBaseString s) TypString
  | typ_tuple : forall vs ts,
      Forall2 (val_typ gsenum) vs ts ->
      val_typ gsenum (ValBaseTuple vs) (TypTuple ts)
  | typ_record : forall vs ts,
      Forall2
        (fun xv xt =>
           P4String.equiv (fst xv) (fst xt) /\ val_typ gsenum (snd xv) (snd xt))
        vs ts ->
      val_typ gsenum (ValBaseRecord vs) (TypRecord ts)
  | typ_error : forall err,
      val_typ gsenum (ValBaseError err) TypError
  | typ_matchkind : forall mk,
      val_typ gsenum (ValBaseMatchKind mk) TypMatchKind
  | typ_struct : forall vs ts,
      Forall2
        (fun xv xt =>
           P4String.equiv (fst xv) (fst xt) /\ val_typ gsenum (snd xv) (snd xt))
        vs ts ->
      val_typ gsenum (ValBaseStruct vs) (TypStruct ts)
  | typ_header : forall b vs ts,
      Forall2
        (fun xv xt =>
           P4String.equiv (fst xv) (fst xt) /\ val_typ gsenum (snd xv) (snd xt))
        vs ts ->
      val_typ gsenum (ValBaseHeader vs b) (TypHeader ts)
  | typ_union : forall vs ts,
      Forall2
        (fun xv xt =>
           P4String.equiv (fst xv) (fst xt) /\ val_typ gsenum (snd xv) (snd xt))
        vs ts ->
      val_typ gsenum (ValBaseUnion vs) (TypHeaderUnion ts)
  | typ_stack : forall s n vs ts,
      length vs = N.to_nat s ->
      Forall (fun v => val_typ gsenum v (TypHeader ts)) vs ->
      val_typ gsenum (ValBaseStack vs s n) (TypArray (TypHeader ts) n)
  | typ_enumfield : forall ename member members,
      In member members ->
      val_typ gsenum
              (ValBaseEnumField ename member)
              (TypEnum ename None members)
  | typ_senumfield : forall ename member v t fields,
      IdentMap.get ename gsenum = Some (ValBaseSenum fields) ->
      AList.get fields member = Some v ->
      val_typ gsenum v t ->
      val_typ gsenum
              (ValBaseSenumField ename member v)
              (TypEnum ename (Some t) (List.map fst fields))
  (* TODO: what is a [ValBaseSenum _], and what is its type?
     It seems to be something in [gsenum],
     but should it be a value? *)
  | typ_senum : forall fields ename t,
      IdentMap.get ename gsenum = Some (ValBaseSenum fields) ->
      Forall (fun xv => val_typ gsenum (snd xv) t) fields ->
      val_typ
        gsenum (ValBaseSenum fields)
        (TypEnum ename (Some t) (List.map fst fields)).

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

  (*
  Lemma eval_p4int_sval_not_null : forall i,
      @eval_p4int_sval tags_t i <> ValBaseNull.
  Proof.
    destruct i as [tg z [[? [|]] |]]; cbn; discriminate.
  Qed.
  
  Lemma exec_expr_null : forall ge rob p st e,
      run_expr rob ge p st e ValBaseNull ->
      exists tag t dir, e = MkExpression tag ExpDontCare t dir.
  Proof.
    intros rob ge p st e Hrun.
    inversion Hrun; subst; eauto.
    - exfalso. pose proof eval_p4int_sval_not_null i as Hnn.
      rewrite <- H in Hnn; contradiction.
    - (* [exec_expr_name] problematic:
         need restructions on [st] and [ge]. *)
      admit.
    - Print array_access_idx_to_z.
  Abort. *)
  
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

  Local Hint Constructors exec_exprs : core.
  
  Lemma exec_exprs_iff : forall ge rob p st es vs,
      exec_exprs ge rob p st es vs <-> Forall2 (run_expr ge rob p st) es vs.
  Proof.
    intros ge rob p st es vs; split;
      intros H; induction H; auto.
  Qed.
  
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
      destruct Hrnes as [vs Hvs].
      rewrite <- exec_exprs_iff in Hvs; eauto.
    - clear Hrnes; intros v Hrn; simpl.
      inversion Hrn; subst; clear Hrn.
      rename H6 into Hesvs.
      rewrite exec_exprs_iff in Hesvs.
      apply forall_Forall2 with (bs := vs) in Htyps;
        eauto using Forall2_length.
      apply Forall2_impl with
          (R := run_expr ge rob p st)
          (Q := fun e v => val_typ ge v (typ_of_expr e)) in Htyps; auto.
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
      constructor; rewrite Forall2_conj; split.
      + pose proof Forall2_map_l
             ident (ident * Sval) (ident * typ)
             (fun u v => @P4String.equiv tags_t u (fst v)) fst
             (map (fun '(x, e) => (x, typ_of_expr e)) es) as Hmfl.
        simpl in Hmfl.
        (*rewrite Hmfl.*)
        (*rewrite exec_exprs_iff in Heskvs.*)
  Admitted.
End Soundness.
