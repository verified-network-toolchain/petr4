Require Export Poulet4.ValueTyping.
Require Poulet4.P4String Poulet4.P4cub.Util.EquivUtil.

(* TODO: need to parameterize
   typing definitions by [path]. 
   Or remove [path] parameters from [Semantics.v]. *)
    
Section TypingDefs.
  Context {tags_t : Type} {dummy : Inhabitant tags_t}.

  Notation typ := (@P4Type tags_t).
  Notation expr := (@Expression tags_t).
  Notation stmt := (@Statement tags_t).
  Notation signal := (@signal tags_t).
  Notation ident := (P4String.t tags_t).
  Notation path := (list ident).
  Notation Sval := (@ValueBase (option bool)).

  (* Local variable typing environment. *)
  Definition gamma_local := PathMap.t typ.

  (* Constant & global variable typing environment. *)
  Definition gamma_const := PathMap.t typ.

  (* Function definition typing environment. TODO! *)
  Definition gamma_func := PathMap.t unit.

  (* Instance typing environment. TODO. *)
  Definition gamma_inst := PathMap.t unit.

  (* Extern instance typing environment. TODO. *)
  Definition gamma_ext := PathMap.t unit.
  
  (* Expression typing environment. *)
  Record gamma_expr := {
    local_gamma :> gamma_local;
    const_gamma :> gamma_const }.
    
  (* Statement typing Environment. *)
  Record gamma_stmt : Type := {
    expr_gamma :> gamma_expr;
    func_gamma :> gamma_func;
    inst_gamma :> gamma_inst;
    ext_gamma :> gamma_ext }.

  Definition p2l (p: path): list string := map (@P4String.str tags_t) p.
  
  (** TODO: is this correct?
      Typing analogue to [loc_to_sval].
      How will [this] be used...? *)
  Definition typ_of_loc (this : path) (l : Locator) (g : gamma_expr) : option typ :=
    match l with
    | LInstance p => PathMap.get (p2l p) (local_gamma g)
    | LGlobal   p => PathMap.get (p2l p) (const_gamma g)
    end.

  (** TODO: is search correct?
      TODO: Function type is a stub.
      TODO: incomplete case elimination.
      Typing analogue to [lookup_func]. *)
  Definition lookup_func_typ
             (this : path) (gf : gamma_func) (gi : gamma_inst) (func : expr) : option (path * unit) :=
    match func with
    | MkExpression _ (ExpName _ (LGlobal p)) _ _ =>
      option_map (fun funt => (nil, funt)) (PathMap.get (p2l p) gf)
    | MkExpression _ (ExpName _ (LInstance p)) _ _ =>
      match PathMap.get (p2l this) gi with
      | Some _ (* class name? *) =>
        option_map (fun funt => (this, funt)) (PathMap.get (p2l (nil (* todo: class name? *) ++ p)) gf)
      | None => None
      end
    | _ => None
    end.
  
  Context `{T : @Target tags_t expr}.
  
  Definition gamma_expr_domain
             (p : path) (g : gamma_expr) (st : state) (ge : genv) : Prop :=
    forall (l : Locator),
      typ_of_loc p l g = None <-> loc_to_sval ge p l st = None.

  Definition gamma_expr_val_typ
             (p : path) (g : gamma_expr) (st : state) (ge : genv) : Prop :=
    forall (l : Locator) (t : typ) (v : Sval),
      typ_of_loc p l g = Some t ->
      loc_to_sval ge p l st = Some v ->
      val_typ (ge_senum ge) v t.

  Definition gamma_expr_prop
             (p : path) (g : gamma_expr) (st : state) (ge : genv) : Prop :=
    gamma_expr_domain p g st ge /\ gamma_expr_val_typ p g st ge.

  Set Printing Implicit.
  (* TODO: is this correct? *)
  Definition gamma_inst_domain
             (g : gamma_inst) (ge_inst : @genv_inst tags_t) : Prop :=
    forall (p : path),
      PathMap.get (p2l p) g = None <-> PathMap.get (p2l p) ge_inst = None.

  (* TODO: stub. *)
  Definition gamma_inst_types
             (g : gamma_inst) (ge_inst : @genv_inst tags_t) : Prop :=
    forall (p : path) (inst : inst_ref) (it : unit),
      PathMap.get (p2l p) g = Some it ->
      PathMap.get (p2l p) ge_inst = Some inst ->
      True (* Stub, property of [it] and [inst]. *).

  Definition gamma_inst_prop
             (g : gamma_inst) (ge_inst : genv_inst) : Prop :=
    gamma_inst_domain g ge_inst /\ gamma_inst_types g ge_inst.
  
  Definition gamma_func_domain
             (this : path) (gf : gamma_func) (gi : gamma_inst) (ge : genv) : Prop :=
    forall (e : expr), lookup_func_typ this gf gi e = None <-> lookup_func ge this e = None.

  (** TODO: stub. *)
  Definition gamma_func_types
             (this : path) (gf : gamma_func) (gi : gamma_inst) (ge : genv) : Prop :=
    forall (e : expr) (p p' : path) (fd : fundef) (ft : unit),
      lookup_func_typ this gf gi e = Some (p,ft) ->
      lookup_func ge this e = Some (p',fd) ->
      p = p' /\
      True (* Stub, some property on [fd] and [ft]. *).

  Definition gamma_func_prop
             (this : path) (gf : gamma_func) (gi : gamma_inst) (ge : genv) : Prop :=
    gamma_func_domain this gf gi ge /\ gamma_func_types this gf gi ge.

  (** TODO: externs... *)
  Definition gamma_stmt_prop
             (this : path) (g : gamma_stmt) (ge : genv) (st : state) : Prop :=
    gamma_expr_prop this (expr_gamma g) st ge /\
    gamma_inst_prop (inst_gamma g) ge /\
    gamma_func_prop this (func_gamma g) (inst_gamma g) ge.
  
  Notation run_expr := (@exec_expr tags_t dummy T).
  Notation run_stmt := (@exec_stmt tags_t dummy T).

  Definition typ_of_expr (e : expr) : typ :=
    match e with
    | MkExpression _ _ t _ => t
    end.
  (**[]*)
  
  (** Expression typing. *)
  Definition expr_types (this : path) (g : gamma_expr) (e : expr) : Prop :=
    forall (read_one_bit : option bool -> bool -> Prop)
      (ge : genv) (st : state),
      read_one_bit_reads read_one_bit ->
      gamma_expr_prop this g st ge ->
      (exists v, run_expr ge read_one_bit this st e v) /\
      forall v, run_expr ge read_one_bit this st e v ->
           val_typ (ge_senum ge) v (typ_of_expr e).
  (**[]*)

  (** Statement typing. *)
  Definition stmt_types (this : path) (g g' : gamma_stmt) (s : stmt) : Prop :=
    forall (read_one_bit : option bool -> bool -> Prop)
      (ge : genv) (st : state),
      read_one_bit_reads read_one_bit ->
      gamma_stmt_prop this g ge st ->
      (exists st' sig, run_stmt ge read_one_bit this st s st' sig) /\
      forall st' sig, run_stmt ge read_one_bit this st s st' sig ->
                 gamma_stmt_prop this g' ge st'.
End TypingDefs.

Notation "Γ '⊢e' e ≀ this"
  := (expr_types this Γ e) (at level 80, no associativity) : type_scope.
Notation "Γ1 '⊢s' s ⊣ Γ2 ≀ this"
  := (stmt_types this Γ1 Γ2 s) (at level 80, no associativity) : type_scope.

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

  Local Hint Unfold expr_types : core.
  Local Hint Constructors exec_expr : core.
  Local Hint Constructors val_typ : core.

  Variable (this : path).
  
  Section ExprTyping.
    Variable (Γ : @gamma_expr tags_t).

    Ltac soundtac :=
      autounfold with *;
      intros rob ge st Hrob Hg;
      split; eauto;
      try (intros v Hrn; inversion Hrn; subst; cbn; eauto).
  
    Lemma bool_sound : forall tag b dir,
        Γ ⊢e MkExpression tag (ExpBool b) TypBool dir ≀ this.
    Proof.
      intros; soundtac.
    Qed.
  
  Lemma arbitrary_int_sound : forall tag i z dir,
      Γ ⊢e
        MkExpression
        tag (ExpInt (P4Int.Build_t _ i z None)) TypInteger dir ≀ this.
  Proof.
    intros; soundtac.
  Qed.

  Lemma unsigned_int_sound : forall tag i z w dir,
      Γ ⊢e
        MkExpression
        tag (ExpInt (P4Int.Build_t _ i z (Some (w,false)))) (TypBit w) dir ≀ this.
  Proof.
    intros tag i z dir; soundtac.
    (* TODO: need some result about [P4Arith.to_loptbool]. *)
  Admitted.

  Lemma signed_int_sound : forall tag i z w dir,
      Γ ⊢e
        MkExpression
        tag (ExpInt (P4Int.Build_t _ i z (Some (w,true)))) (TypInt w) dir ≀ this.
  Proof.
    intros tag i z dir; soundtac.
    (* TODO: need some result about [P4Arith.to_loptbool]. *)
  Admitted.

  Lemma string_sound : forall tag s dir,
      Γ ⊢e MkExpression tag (ExpString s) TypString dir ≀ this.
  Proof.
    intros; soundtac.
  Qed.

  Lemma name_sound : forall tag x loc t dir,
      typ_of_loc this loc Γ = Some t ->
      Γ ⊢e MkExpression tag (ExpName x loc) t dir ≀ this.
  Proof.
    intros i x l t d Hgt; soundtac.
    - destruct l as [lp | lp]; simpl in Hgt;
        (*eapply envs_same_some_l in Hgt as [v Hv]; *) eauto.
      (*exists v. constructor; simpl.*)
      (** TODO:
          1. Need type preservation to [eval_val_to_sval].
          2. Perhaps [envs_same] needs to include [genv]. *)
      admit. admit.
    - destruct l as [lp | lp]; simpl in Hgt;
        simpl in *; eauto.
  Admitted.

  Lemma array_access_sound : forall tag arry idx ts dir n,
      typ_of_expr arry = TypArray (TypHeader ts) n ->
      typ_of_expr idx  = TypBit n ->
      Γ ⊢e arry ≀ this ->
      Γ ⊢e idx ≀ this ->
      Γ ⊢e MkExpression tag (ExpArrayAccess arry idx) (TypHeader ts) dir ≀ this.
  Proof.
    intros i e1 e2 ts d n Ht1 Ht2 He1 He2;
      autounfold with * in *.
    intros rob ge st Hrob Hg.
    pose proof He1 rob ge st Hrob Hg as [[v1 Hev1] He1']; clear He1.
    pose proof He2 rob ge st Hrob Hg as [[v2 Hev2] He2']; clear He2.
    split.
    - pose proof He1' v1 Hev1 as Hv1.
      pose proof He2' v2 Hev2 as Hv2.
      rewrite Ht1 in Hv1; rewrite Ht2 in Hv2.
      inversion Hv1; inversion Hv2; subst.
      (* Need to know [N_of_value idx < n]. *) admit.
    - intros v' Haa; inversion Haa; clear Haa; subst; simpl.
      (* Molly commented the things below out since 
         things does not work on H7 after Semantics.v changes *)
      (* rename H4 into He2; rename H10 into He1;
        rename H7 into Hsval; rename H9 into Haa;
          rename H11 into Huninit.
      pose proof He1' _ He1 as Hv1.
      pose proof He2' _ He2 as Hv2.
      rewrite Ht1 in Hv1; rewrite Ht2 in Hv2.
      inversion Hv1; inversion Hv2; subst. *)
      (* Need result about [Znth_def]. *)
  Admitted.

  Lemma bigstring_access_sound : forall tag bits lo hi dir w,
      (lo <= hi < w)%N ->
      typ_of_expr bits = TypBit w ->
      Γ ⊢e bits ≀ this ->
      Γ ⊢e MkExpression
        tag (ExpBitStringAccess bits lo hi)
        (TypBit (hi - lo + 1)%N) dir ≀ this.
  Proof.
    intros i e lo hi d w Hlwh Ht He.
    autounfold with * in *.
    intros rob ge st Hrob Hg.
    pose proof He rob ge st Hrob Hg as [[v Hev] He']; clear He.
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
      Forall (fun e => Γ ⊢e e ≀ this) es ->
      Γ ⊢e MkExpression tag (ExpList es)
        (TypTuple (map typ_of_expr es)) dir ≀ this.
  Proof.
    intros i es d Hes. autounfold with * in *.
    intros rob ge st Hrob Hg.
    rewrite Forall_forall in Hes.
      specialize Hes with
          (read_one_bit:=rob) (ge:=ge) (st:=st).
      pose proof reduce_inner_impl _ _ _ _ Hes Hrob as Hes';
        simpl in Hes'; clear Hes.
      pose proof reduce_inner_impl _ _ _ _ Hes' Hg as Hes;
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
          (R := run_expr ge rob this st)
          (Q := fun e v => val_typ (ge_senum ge) v (typ_of_expr e)) in Htyps; auto.
      rewrite Forall2_flip, Forall2_map_r in Htyps; auto.
  Qed.
  
  Lemma record_sound : forall tag es dir,
      Forall (fun e => Γ ⊢e e ≀ this) (map snd es) ->
      Γ ⊢e
        MkExpression
        tag (ExpRecord es)
        (TypRecord (map (fun '(x,e) => (x,typ_of_expr e)) es)) dir ≀ this.
  Proof.
    intros i es d Hes.
    autounfold with * in *.
    intros rob ge st Hrob Hg.
    rewrite Forall_forall in Hes.
    specialize Hes with
        (read_one_bit:=rob) (ge:=ge) (st:=st).
    pose proof reduce_inner_impl _ _ _ _ Hes Hrob as Hes';
      simpl in Hes'; clear Hes.
    pose proof reduce_inner_impl _ _ _ _ Hes' Hg as Hes;
      simpl in Hes; clear Hes'.
    rewrite split_impl_conj in Hes.
    destruct Hes as [Hrns Htyps]. split.
    - clear Htyps. rewrite <- Forall_forall in Hrns.
      rewrite Forall_exists_factor in Hrns.
      destruct Hrns as [vs Hvs].
      rewrite AList.Forall2_all_values
        with (ks := map fst es) in Hvs.
      + rewrite combine_map_fst_snd in Hvs; eauto. admit.
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
      (*rewrite <- AList.Forall2_all_values in Heskvs.
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
              (R := run_expr ge rob this st)
              (Q := fun e v => val_typ (ge_senum ge) v (typ_of_expr e)) in Hff2; auto.
          rewrite Forall2_flip,Forall2_map_r in Hff2; assumption.
      + repeat rewrite map_length; reflexivity.
      + rewrite Hmf; repeat rewrite map_length; reflexivity.
  Qed.*)
  Admitted.

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
  | UTNot :
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
      val_to_sval v (ValueBaseMap Some v).
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

  Lemma eval_unary_op_preserves_typ : forall o v v' g t t',
      unary_type o t t' ->
      Ops.Ops.eval_unary_op o v = Some v' ->
      val_typ g v t -> val_typ g v' t'.
  Proof.
    intros o v v' g t t' Hut Heval Hvt;
      inversion Hut; subst;
        inversion Hvt; subst;
          try (inversion Heval; subst; auto; assumption).
    - unfold Ops.Ops.eval_unary_op in Heval.
      destruct (P4Arith.BitArith.from_lbool v0)
        as [w' n'] eqn:Heqfromlbool.
      injection Heval as Hv'. rewrite <- Hv'.
      inversion H; subst; clear H.
      (** TODO: need helper lemma about
          [P4Arith.to_lbool] and [P4Arith.BitArith.bit_not]. *)
  Admitted.
  
  Lemma unary_op_sound : forall tag o e t dir,
      unary_type o (typ_of_expr e) t ->
      Γ ⊢e e ≀ this ->
      Γ ⊢e MkExpression tag (ExpUnaryOp o e) t dir ≀ this.
  Proof.
    intros i o e t d Hut He.
    autounfold with * in *; intros rob ge st Hrob Hg.
    specialize He with rob ge st.
    pose proof He Hrob Hg as [[v Hev] Hvt]; clear He; split.
    - apply Hvt in Hev as Hv; clear Hvt.
      assert (exists v', sval_to_val rob v v')
        by eauto using exec_val_exists.
      destruct H as [v' Hv'].
      assert (exists v''', Ops.Ops.eval_unary_op o v' = Some v''').
      (* Maybe try to factor this out?
        Lemma exists_eval_unary_op : forall o v,
          exists v', Ops.Ops.eval_unary_op o v = Some v'. *)
      { destruct (Ops.Ops.eval_unary_op o v') as [v'' |] eqn:Heqop; eauto.
        inversion Hut; subst; try inv_numeric; try inv_numeric_width;
          match goal with
          | H: _ = typ_of_expr ?e,
               Hv: val_typ _ ?v (typ_of_expr ?e),
                   Hv': sval_to_val _ ?v _
            |- _ => rewrite <- H in *; inversion Hv; inversion Hv'; subst
          end; simpl in *; try discriminate. }
      firstorder eauto. admit.
    - clear v Hev; intros v Hev.
      inversion Hev; subst; simpl in *.
      pose proof Hvt _ H7 as Hargsv.
      assert (typ_of_expr e = t) by eauto using unary_type_eq.
      rewrite H in *. clear e Hvt Hev H7 H.
      pose proof (@exec_val_preserves_typ tags_t _ _
           _ _ _ H8 (ge_senum ge)) as Hevpt.
      assert (Hgsb : exists gsb,
                 FuncAsMap.related
                   (AList.all_values (exec_val rob))
                   (ge_senum ge) gsb).
      { admit. }
      destruct Hgsb as [gsb Hgsb].
      pose proof Hevpt _ Hgsb _ Hargsv as Hargv.
      assert (Hv0: val_typ gsb v0 t)
        by eauto using eval_unary_op_preserves_typ.
      assert (Hgsb' :
                FuncAsMap.related
                  (AList.all_values val_to_sval)
                  gsb (ge_senum ge)).
      { (* TODO:
           Need assumption
           [read_one_bit_inverse rob read_detbit]. *)
        admit. }
      eauto using exec_val_preserves_typ.
  Admitted.

  (** Evidence a binary operation is valid for given types. *)
  Variant binary_type : OpBin -> typ -> typ -> typ -> Prop :=
  | BTPlusPlusBit w1 w2 t2 :
      numeric_width w2 t2 ->
      binary_type PlusPlus (TypBit w1) t2 (TypBit (w1 + w2)%N)
  | BTPlusPlusInt w1 w2 t2 :
      numeric_width w2 t2 ->
      binary_type PlusPlus (TypInt w1) t2 (TypInt (w1 + w2)%N)
  | BTShl w1 t1 t2 :
      numeric_width w1 t1 -> numeric t2 ->
      binary_type Shl t1 t2 t1
  | BTShrBit w1 w2 t1 :
      numeric_width w1 t1 ->
      binary_type Shr t1 (TypBit w2) t1
  | BTShlInteger w1 t1 :
      numeric_width w1 t1 ->
      binary_type Shr t1 TypInteger t1
  | BTShrInteger w1 t1 :
      numeric_width w1 t1 ->
      binary_type Shr t1 TypInteger t1
  | BTEq t :
      binary_type Eq t t TypBool
  | BTNotEq t :
      binary_type NotEq t t TypBool
  | BTPlus t :
      numeric t ->
      binary_type Plus t t t
  | BTMinus t :
      numeric t ->
      binary_type Minus t t t
  | BTMul t :
      numeric t ->
      binary_type Mul t t t
  | BTDiv t :
      numeric t ->
      binary_type Div t t t
  | BTMod t :
      numeric t ->
      binary_type Mod t t t
  | BTLe t :
      numeric t ->
      binary_type Le t t TypBool
  | BTGe t :
      numeric t ->
      binary_type Ge t t TypBool
  | BTLt t :
      numeric t ->
      binary_type Lt t t TypBool
  | BTGt t :
      numeric t ->
      binary_type Gt t t TypBool
  | BTPlusSat w t :
      numeric_width w t ->
      binary_type PlusSat t t t
  | BTMinusSat w t :
      numeric_width w t ->
      binary_type MinusSat t t t
  | BTBitAnd w t :
      numeric_width w t ->
      binary_type BitAnd t t t
  | BTBitOr w t :
      numeric_width w t ->
      binary_type BitOr t t t
  | BTBitXor w t :
      numeric_width w t ->
      binary_type BitXor t t t
  | BTAnd :
      binary_type And TypBool TypBool TypBool
  | BTOr :
      binary_type Or TypBool TypBool TypBool.

  Lemma binary_op_sound : forall tag o t e1 e2 dir,
      binary_type o (typ_of_expr e1) (typ_of_expr e2) t ->
      Γ ⊢e e1 ≀ this -> Γ ⊢e e2 ≀ this ->
      Γ ⊢e MkExpression tag (ExpBinaryOp o (e1,e2)) t dir ≀ this.
  Proof.
  Admitted.

  Inductive cast_type : typ -> typ -> Prop :=
  | CTBool w :
      cast_type (TypBit w) TypBool
  | CTBit t w :
      match t with
      | TypBool
      | TypBit _
      | TypInt _
      | TypInteger
      | TypEnum _ (Some (TypBit _)) _ => True
      | _ => False
      end ->
      cast_type t (TypBit w)
  | CTInt t w :
      match t with
      | TypBool
      | TypBit _
      | TypInt _
      | TypInteger
      | TypEnum _ (Some (TypInt _)) _ => True
      | _ => False
      end ->
      cast_type t (TypInt w)
  | CTEnum t1 t2 enum fields :
      match t1, t2 with
      | TypBit _, TypBit _
      | TypInt _, TypInt _
      | TypEnum _ (Some (TypBit _)) _, TypBit _
      | TypEnum _ (Some (TypInt _)) _, TypInt _ => True
      | _, _ => False
      end ->
      cast_type t1 (TypEnum enum (Some t2) fields)
  | CTNewType x t t' :
      cast_type t t' ->
      cast_type t (TypNewType x t')
  | CTStructOfTuple ts xts :
      Forall2 (fun t xt => cast_type t (snd xt)) ts xts ->
      cast_type (TypTuple ts) (TypStruct xts)
  | CTStructOfRecord xts xts' :
      AList.all_values cast_type xts xts' ->
      cast_type (TypRecord xts) (TypStruct xts')
  | CTHeaderOfTuple ts xts :
      Forall2 (fun t xt => cast_type t (snd xt)) ts xts ->
      cast_type (TypTuple ts) (TypHeader xts)
  | CTHeaderOfRecord xts xts' :
      AList.all_values cast_type xts xts' ->
      cast_type (TypRecord xts) (TypHeader xts')
  | CTTuple ts ts' :
      Forall2 cast_type ts ts' ->
      cast_type (TypTuple ts) (TypTuple ts').
  
  Lemma cast_sound : forall tag e t dir,
      cast_type (typ_of_expr e) t ->
      Γ ⊢e e ≀ this ->
      Γ ⊢e MkExpression tag (ExpCast t e) t dir ≀ this.
  Proof.
  Admitted.

  Lemma enum_member_sound : forall tag tname member ename members dir,
      (* TODO: need [ge] of [genv].
         name_to_type ge tname = Some (TypEnum ename None members) ->*)
      In member members ->
      Γ ⊢e MkExpression
        tag (ExpTypeMember tname member)
        (TypEnum ename None members) dir ≀ this.
  Proof.
  Admitted.

  Lemma senum_member_sound : forall tag tname member ename t members dir,
      (*name_to_type ge tname = Some (TypEnum ename (Some etyp) members) ->
      IdentMap.get ename (ge_senum ge) = Some fields ->*)
      In member members ->
      Γ ⊢e MkExpression
        tag (ExpTypeMember tname member)
        (TypEnum ename (Some t) members) dir ≀ this.
  Proof.
  Admitted.

  Lemma error_member_sound : forall tag err dir,
      Γ ⊢e MkExpression
        tag (ExpErrorMember err) TypError dir ≀ this.
  Proof.
    soundtac.
  Qed.

  Variant member_type (ts : P4String.AList tags_t typ)
    : typ -> Prop :=
  | record_member_type :
      member_type ts (TypRecord ts)
  | struct_member_type :
      member_type ts (TypStruct ts)
  | header_member_type :
      member_type ts (TypHeader ts)
  | union_member_type :
      member_type ts (TypHeaderUnion ts).
  
  Lemma other_member_sound : forall tag e x ts t dir,
      member_type ts (typ_of_expr e) ->
      AList.get ts x = Some t ->
      Γ ⊢e e ≀ this ->
      Γ ⊢e MkExpression
        tag (ExpExpressionMember e x) t dir ≀ this.
  Proof.
  Admitted.

  Lemma array_size_sound : forall tag e x dir t w,
      (* P4Arith.BitArith.bound 32 w -> *)
      (w < 2 ^ 32)%N ->
      typ_of_expr e = TypArray t w ->
      P4String.str x = "size"%string ->
      Γ ⊢e e ≀ this ->
      Γ ⊢e MkExpression
        tag (ExpExpressionMember e x) (TypBit 32) dir ≀ this.
  Proof.
  Admitted.

  Lemma array_last_index_sound : forall tag e x dir t w,
      typ_of_expr e = TypArray t w ->
      P4String.str x = "lastIndex"%string ->
      Γ ⊢e e ≀ this ->
      Γ ⊢e MkExpression
        tag (ExpExpressionMember e x) t dir ≀ this.
  Proof.
  Admitted.

  Lemma ternary_sound : forall tag e₁ e₂ e₃ t dir,
      typ_of_expr e₁ = TypBool ->
      typ_of_expr e₂ = typ_of_expr e₃ ->
      typ_of_expr e₂ = t ->
      Γ ⊢e e₁ ≀ this ->
      Γ ⊢e e₂ ≀ this ->
      Γ ⊢e e₃ ≀ this ->
      Γ ⊢e MkExpression tag (ExpTernary e₁ e₂ e₃) t dir ≀ this.
  Proof.
  Admitted.

  Lemma dontcare_sound : forall tag dir,
      Γ ⊢e MkExpression tag ExpDontCare TypVoid dir ≀ this.
  Proof.
    soundtac.
  Qed.

  Inductive lexpr_ok : expr -> Prop :=
  | lexpr_name tag x loc t dir :
      lexpr_ok (MkExpression tag (ExpName x loc) t dir)
  | lexpr_member tag e x t dir :
      lexpr_ok e ->
      lexpr_ok (MkExpression tag (ExpExpressionMember e x) t dir)
  | lexpr_slice tag e hi lo t dir :
      lexpr_ok e ->
      lexpr_ok (MkExpression tag (ExpBitStringAccess e lo hi) t dir)
  | lexpr_access tag e₁ e₂ t dir :
      lexpr_ok e₁ ->
      lexpr_ok (MkExpression tag (ExpArrayAccess e₁ e₂) t dir).
  End ExprTyping.

  Section StmtTyping.
    Variable (Γ : @gamma_stmt tags_t).
    
    Lemma assign_sound : forall tag e₁ e₂,
      lexpr_ok e₁ ->
      (expr_gamma Γ) ⊢e e₁ ≀ this ->
      (expr_gamma Γ) ⊢e e₂ ≀ this ->
      Γ ⊢s MkStatement
        tag (StatAssignment e₁ e₂) StmUnit
        ⊣ (* relation to update context with this_path and type. *) Γ ≀ this.
    Proof.
      (* Maybe typing needs to be parameterized by a path. *)
    Admitted.
  End StmtTyping.
End Soundness.
