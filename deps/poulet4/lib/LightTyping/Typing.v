Require Export Poulet4.LightTyping.ValueTyping
        Poulet4.Monads.Monad Poulet4.Monads.Option.
Require Poulet4.P4String Poulet4.P4cub.Util.EquivUtil.

(* TODO:
   Need parametric operations
   for [PathMap.t] and [Locator]
   to be shared by
   the static & dynamic semantics:
   [lookup : forall {A}, Locator -> path -> PathMap.t A -> option A]
   [update : forall {A}, Locator -> path -> A -> PathMap.t A -> PathMap.t A]
   Only the variable-to-value mapping of [state]
   relates to the type-context analogue. *)
    
Section TypingDefs.
  Context {tags_t : Type} {dummy : Inhabitant tags_t}.

  Notation typ := (@P4Type tags_t).
  Notation expr := (@Expression tags_t).
  Notation stmt := (@Statement tags_t).
  Notation block := (@Block tags_t).
  Notation signal := (@signal tags_t).
  Notation ident := string.
  Notation path := (list ident).
  Notation Sval := (@ValueBase (option bool)).
  Notation funtype := (@FunctionType tags_t).
  
  (* Normal (mutable/non-constant) variable typing environment. *)
  Definition gamma_var := PathMap.t typ.

  (* Constant variable typing environment. *)
  Definition gamma_const := PathMap.t typ.
  
  (* Expression typing environment. *)
  Record gamma_expr := {
    var_gamma :> gamma_var;
    const_gamma :> gamma_const }.

  (** Typing analogue to [Semantics.loc_to_sval]. *)
  Definition typ_of_loc_var
             (l : Locator) (g : gamma_var) : option typ :=
    match l with
    | LInstance p => PathMap.get p g
    | LGlobal   _ => None
    end.

  (** Typing analogue to [Semantics.loc_to_sval_const].*)
  Definition typ_of_loc_const
             (this : path) (l : Locator) (g : gamma_const) : option typ :=
    match l with
    | LInstance p => PathMap.get (this ++ p) g
    | LGlobal   p => PathMap.get p           g
    end.

  Definition bind_var_typ
             (l : Locator) (τ : typ) (g : gamma_var) : gamma_var :=
    PathMap.set (get_loc_path l) τ g.

  Definition bind_var_typ_gamma_expr
             (l : Locator) (τ : typ)
             '({| var_gamma:=vg; const_gamma:=cg |} : gamma_expr)
    : gamma_expr := {| var_gamma:=bind_var_typ l τ vg; const_gamma:=cg |}.
  
  Context `{T : @Target tags_t expr}.

  Definition gamma_var_domain (g : gamma_var) (st : state) : Prop :=
    forall l : Locator, typ_of_loc_var l g = None <-> loc_to_sval l st = None.

  Definition gamma_var_val_typ
             (g : gamma_var) (st : state)
             (gs : genv_senum) : Prop :=
    forall l t v,
      typ_of_loc_var l g = Some t ->
      loc_to_sval l st = Some v ->
      val_typ gs v t.

  Definition gamma_var_prop
             (g : gamma_var) (st : state) (gs : genv_senum) : Prop :=
    gamma_var_domain g st /\ gamma_var_val_typ g st gs.
  
  Definition gamma_const_domain
             (this : path) (g : gamma_const)
             (ge : genv) : Prop :=
    forall l : Locator,
      typ_of_loc_const this l g = None <-> loc_to_sval_const ge this l = None.

  Definition gamma_const_val_typ
             (this : path) (g : gamma_const)
             (ge : genv) : Prop :=
    forall l t v,
      typ_of_loc_const this l g = Some t ->
      loc_to_sval_const ge this l = Some v ->
      val_typ (ge_senum ge) v t.

  Definition gamma_const_prop
             (this : path) (g : gamma_const) (ge : genv) : Prop :=
    gamma_const_domain this g ge /\ gamma_const_val_typ this g ge.
  
  Definition gamma_expr_prop
             (this : path) (g : gamma_expr) (st : state) (ge : genv) : Prop :=
    gamma_var_prop g st ge /\ gamma_const_prop this g ge.
  
  Notation run_expr := (@exec_expr tags_t dummy T).
  Notation run_stmt := (@exec_stmt tags_t dummy T).
  Notation run_blk  := (@exec_block tags_t dummy T).
  Notation run_call := (@exec_call tags_t dummy T).

  Definition typ_of_expr
             '(MkExpression _ _ t _ : expr) : typ := t.

  Definition typ_of_stmt
             '(MkStatement _ _ t : stmt) : StmType := t.
  
  Definition delta_genv_prop
             (ge : @genv_typ tags_t) : list string -> Prop :=
    Forall (fun X => exists t, IdentMap.get X ge = Some t).
  
  (** Expression typing. *)
  Definition
    expr_types
    (this : path)     (** Local path. *)
    (Δ : list string) (** Type variables in context. *)
    (Γ : gamma_expr)  (** Typing environment. *)
    (e : expr)        (** Expression to type. *)
    : Prop :=
    forall (read_one_bit : option bool -> bool -> Prop)
      (ge : genv) (st : state),
      delta_genv_prop ge Δ ->
      read_one_bit_reads read_one_bit ->
      gamma_expr_prop this Γ st ge ->
      Δ ⊢ok typ_of_expr e ->
      (exists v, run_expr ge read_one_bit this st e v) /\
      forall v, run_expr ge read_one_bit this st e v ->
           val_typ (ge_senum ge) v (typ_of_expr e).
  (**[]*)

  (* Function definition typing environment. TODO! *)
  Definition gamma_func := PathMap.t funtype.

  (* Extern instance typing environment. TODO. *)
  Definition gamma_ext := PathMap.t unit.

  (* Statement typing Environment. *)
  Record gamma_stmt : Type := {
    expr_gamma :> gamma_expr;
    func_gamma :> gamma_func;
    inst_gamma :> genv_inst;
    ext_gamma :> gamma_ext }.

  Definition
    bind_typ_gamma_stmt
    (l : Locator) (τ : typ)
    '({| expr_gamma:=eg; func_gamma:=fg;
         inst_gamma:=ig; ext_gamma:=exg |} : gamma_stmt) : gamma_stmt :=
    {| expr_gamma:=bind_var_typ_gamma_expr l τ eg;
       func_gamma:=fg; inst_gamma:=ig; ext_gamma:=exg |}.

  (** Typing analogue to [lookup_func]. *)
  Definition lookup_func_typ
             (this : path) (gf : gamma_func) (gi : genv_inst)
             '(MkExpression _ func _ _ : expr)
    : option (option path * funtype) :=
    match func with
    | ExpName _ (LGlobal p) =>
      option_map (fun funt => (Some nil, funt)) (PathMap.get p gf)
    | ExpName _ (LInstance p) =>
      let* '(mk_inst_ref class _) := PathMap.get this gi in
      let^ ft := PathMap.get (class :: p) gf in (None,ft)
    | ExpExpressionMember (MkExpression _ (ExpName _ (LInstance p)) _ _) x
      => let* '(mk_inst_ref class inst_path) := PathMap.get (this ++ p) gi in
        let^ ft := PathMap.get [class; P4String.str x] gf in (Some inst_path, ft)
    | ExpExpressionMember (MkExpression _ (ExpName _ (LGlobal p)) _ _) x
      => let* '(mk_inst_ref class inst_path) := PathMap.get p gi in
        let^ ft := PathMap.get [class; P4String.str x] gf in (Some inst_path, ft)
    | _ => None
    end.

  Definition gamma_func_domain
             (this : path) (gf : gamma_func)
             (gi : genv_inst) (ge : genv) : Prop := forall (e : expr),
      lookup_func_typ this gf gi e = None <-> lookup_func ge this e = None.

  Variant fundef_funtype_prop
          (Δ : list string) (Γ : gamma_expr)
          (Γext : gamma_ext) (this : path)
    : @fundef tags_t -> funtype -> Prop :=
  (* TODO : need to know [body] & [init] are well-typed. *)
  | Internal_prop params body Xs params' rt :
      Forall2 (fun '(_,d) '(MkParameter _ d' _ _ _) => d = d') params params' ->
      fundef_funtype_prop
        Δ Γ Γext this
        (FInternal params body)
        (MkFunctionType Xs params' FunFunction rt)
  | Table_match name keys actions dflt entries key_typs :
      Forall2
        (fun '(MkTableKey _ e mk) '(t,mk') =>
           expr_types this Δ Γ e /\
           typ_of_expr e = t /\ P4String.str mk = mk')
        keys key_typs ->
      fundef_funtype_prop
        Δ Γ Γext this
        (FTable name keys actions dflt entries)
        (MkFunctionType [] [] FunTable TypVoid)
  | External_match class name Xs params rt :
      (* TODO: lookup [FExternal] by [class] or [name]. *)
      fundef_funtype_prop
        Δ Γ Γext this
        (FExternal class name)
        (MkFunctionType Xs params FunExtern rt).
  
  (** TODO: stub. *)
  Definition gamma_func_types
             (this : path) (d : list string)
             (g : gamma_expr) (gf : gamma_func)
             (gi : genv_inst) (gext : gamma_ext) (ge : genv) : Prop :=
    forall (e : expr) (p p' : option path) (fd : fundef) (ft : funtype),
      lookup_func_typ this gf gi e = Some (p,ft) ->
      lookup_func ge this e = Some (p',fd) ->
      p = p' /\ fundef_funtype_prop d g gext this fd ft.

  Definition gamma_func_prop
             (this : path) (d : list string)
             (g : gamma_expr) (gf : gamma_func)
             (gi : genv_inst) (gext : gamma_ext) (ge : genv) : Prop :=
    gamma_func_domain this gf gi ge /\
    gamma_func_types this d g gf gi gext ge.

  (** TODO: externs... *)
  Definition gamma_stmt_prop
             (this : path) (d : list string)
             (g : gamma_stmt) (ge : genv) (st : state) : Prop :=
    gamma_expr_prop this (expr_gamma g) st ge /\
    gamma_func_prop
      this d (expr_gamma g) (func_gamma g)
      (inst_gamma g) (ext_gamma g) ge /\
    inst_gamma g = ge_inst ge.
  
  Definition lub_StmType (τ₁ τ₂ : StmType) : StmType :=
    match τ₁, τ₂ with
    | StmUnit, _
    | _, StmUnit => StmUnit
    | _, _       => StmVoid
    end.
  
  (** Statement typing. *)
  Definition
    stmt_types
    (this : path)       (* Local path. *)
    (Δ : list string)   (* Type names in context. *)
    (Γ Γ' : gamma_stmt) (* Input & output typing environment. *)
    (s : stmt)          (* Statement in question. *)
    : Prop :=
    forall (read_one_bit : option bool -> bool -> Prop)
      (ge : genv) (st : state),
      delta_genv_prop ge Δ ->
      read_one_bit_reads read_one_bit ->
      gamma_stmt_prop this Δ Γ ge st ->
      (exists st' sig, run_stmt ge read_one_bit this st s st' sig) /\
      forall st' sig, run_stmt ge read_one_bit this st s st' sig ->
                 gamma_stmt_prop this Δ Γ' ge st'.

  Inductive Block_StmTypes : block -> StmType -> Prop :=
  | Empty_StmType tag :
      Block_StmTypes (BlockEmpty tag) StmUnit
  | Last_StmtType s tag t :
      typ_of_stmt s = t ->
      Block_StmTypes (BlockCons s (BlockEmpty tag)) t
  | Cons_StmtType s blk t :
      typ_of_stmt s = StmUnit ->
      Block_StmTypes blk t ->
      Block_StmTypes (BlockCons s blk) t.
      
  (** Block typing. *)
  Definition
    block_types
    (this : path)       (* Local path. *)
    (Δ : list string)   (* Type variable names in context. *)
    (Γ Γ' : gamma_stmt) (* Input & output typing environments. *)
    (blk : block)       (* Statement block. *)
    : Prop :=
    forall (read_one_bit : option bool -> bool -> Prop)
      (ge : genv) (st : state),
      delta_genv_prop ge Δ ->
      read_one_bit_reads read_one_bit ->
      gamma_stmt_prop this Δ Γ ge st ->
      (exists st' sig, run_blk ge read_one_bit this st blk st' sig) /\
      forall st' sig, run_blk ge read_one_bit this st blk st' sig ->
                 gamma_stmt_prop this Δ Γ' ge st'.
  
  (** Call typing. *)
  Definition
    call_types
    (this : path)     (* Local path. *)
    (Δ : list string) (* Typing variables in context. *)
    (Γ : gamma_stmt)  (* Typing environment. *)
    (call : expr)     (* Call expression. *)
    : Prop :=
    forall (read_one_bit : option bool -> bool -> Prop) (ge : genv) (st : state),
      delta_genv_prop ge Δ ->
      read_one_bit_reads read_one_bit ->
      gamma_stmt_prop this Δ Γ ge st ->
      Δ ⊢ok typ_of_expr call ->
      (exists st' sig, run_call ge read_one_bit this st call st' sig) /\
      forall st' sig, run_call ge read_one_bit this st call st' sig ->
                 gamma_stmt_prop this Δ Γ ge st'.
End TypingDefs.

Notation "Δ '~' Γ '⊢ₑ' e ≀ this"
  := (expr_types this Δ Γ e)
       (at level 80, no associativity) : type_scope.
Notation "Δ '~' Γ₁ '⊢ₛ' s ⊣ Γ₂ ≀ this"
  := (stmt_types this Δ Γ₁ Γ₂ s)
       (at level 80, no associativity) : type_scope.
Notation "Δ '~' Γ₁ '⊢ᵦ' blk ⊣ Γ₂ ≀ this"
  := (block_types this Δ Γ₁ Γ₂ blk)
       (at level 80, no associativity) : type_scope.
Notation "Δ '~' Γ '⊢ᵪ' e ≀ this"
  := (call_types this Δ Γ e)
       (at level 80, no associativity) : type_scope.

Scheme my_P4Type_ind       := Induction for P4Type       Sort Prop
  with my_ControlType_ind  := Induction for ControlType  Sort Prop
  with my_FunctionType_ind := Induction for FunctionType Sort Prop
  with my_P4Parameter_ind  := Induction for P4Parameter  Sort Prop.

(* TODO. *)
Section Soundness.
  Context {tags_t : Type} {dummy : Inhabitant tags_t}.

  Notation typ := (@P4Type tags_t).
  Notation expr := (@Expression tags_t).
  Notation stmt := (@Statement tags_t).
  Notation block := (@Block tags_t).
  Notation signal := (@signal tags_t).
  Notation ident := string.
  Notation path := (list ident).
  Notation Sval := (@ValueBase tags_t (option bool)).

  Context `{T : @Target tags_t expr}.

  Definition
    ok_get_real_type_ex_def
    Δ τ (H: Δ ⊢ok τ) := forall ge : genv,
      delta_genv_prop ge Δ ->
      exists ρ, get_real_type ge τ = Some ρ.
  
  Definition
    ok_get_real_ctrl_ex_def
    Δ ct (H: ControlType_ok Δ ct) := forall ge : genv,
      delta_genv_prop ge Δ ->
      exists ct', get_real_ctrl ge ct = Some ct'.

  Definition
    ok_get_real_func_ex_def
    Δ ft (H : FunctionType_ok Δ ft) := forall ge : genv,
      delta_genv_prop ge Δ ->
      exists ft', get_real_func ge ft = Some ft'.

  Definition
    ok_get_real_param_ex_def
    Δ p (H: P4Parameter_ok Δ p) := forall ge : genv,
      delta_genv_prop ge Δ ->
      exists p', get_real_param ge p = Some p'.

  Definition
    ok_get_real_type_ex_ind :=
    my_P4Type_ok_ind
      _ ok_get_real_type_ex_def
      ok_get_real_ctrl_ex_def
      ok_get_real_func_ex_def
      ok_get_real_param_ex_def.
  
  Lemma ok_get_real_type_ex :
    forall Δ τ (H : Δ ⊢ok τ),
      ok_get_real_type_ex_def Δ τ H.
  Proof.
    apply ok_get_real_type_ex_ind;
      unfold ok_get_real_type_ex_def,
      ok_get_real_ctrl_ex_def,
      ok_get_real_func_ex_def,
      ok_get_real_param_ex_def; cbn;
        unfold option_bind, option_ret; eauto 2.
    - intros d t n H Hge ge Hdge.
      apply Hge in Hdge as [r Hr]; rewrite Hr; eauto 2.
    - intros d ts H ge Hge. admit.
      (* Need custom induction principle...sigh. *)
    - admit.
    - admit.
    - intros d t H Hge ge Hdge.
      apply Hge in Hdge as [r Hr]; rewrite Hr; eauto 2.
    - admit.
    - admit.
    - admit.
    - intros d X ot mems H ge Hdge.
      inversion H; subst; eauto. admit.
      (* Need custom induction principle. *)
    - intros d X H ge Hdge.
      unfold delta_genv_prop in Hdge.
      rewrite Forall_forall in Hdge.
      intuition.
    - intros d X t H Hge ge Hdge. admit.
      (* TODO: maybe need to change [get_real_type]. *)
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
  Admitted.
  
  Notation run_expr := (@exec_expr tags_t dummy T).
  Notation run_stmt := (@exec_stmt tags_t dummy T).
  Notation run_blk := (@exec_block tags_t dummy T).

  Local Hint Unfold expr_types : core.
  Local Hint Constructors exec_expr : core.
  Local Hint Constructors val_typ : core.
  Local Hint Constructors exec_val : core.
  Local Hint Constructors P4Type_ok : core.

  Variables (this : path) (Δ : list string).
  
  Section ExprTyping.
    Variable (Γ : @gamma_expr tags_t).

    Ltac soundtac :=
      autounfold with *;
      intros rob ge st Hdlta Hrob Hg Hok;
      split; eauto;
      try (intros v Hrn; inversion Hrn; subst; cbn; eauto).
  
    Lemma bool_sound : forall tag b dir,
        Δ ~ Γ ⊢ₑ MkExpression tag (ExpBool b) TypBool dir ≀ this.
    Proof.
      intros; soundtac.
    Qed.
  
    Lemma arbitrary_int_sound : forall tag i z dir,
        Δ ~ Γ ⊢ₑ
          MkExpression
          tag (ExpInt (P4Int.Build_t _ i z None)) TypInteger dir ≀ this.
    Proof.
      intros; soundtac.
    Qed.
    
    Lemma unsigned_int_sound : forall tag i z w dir,
        Δ ~ Γ ⊢ₑ
          MkExpression tag
          (ExpInt
             (P4Int.Build_t _ i z (Some (w,false))))
          (TypBit w) dir ≀ this.
    Proof.
      intros tag i z dir; soundtac.
      (* TODO: need some result about [P4Arith.to_loptbool]. *)
    Admitted.
    
    Lemma signed_int_sound : forall tag i z w dir,
        Δ ~ Γ ⊢ₑ
          MkExpression
          tag
          (ExpInt (P4Int.Build_t _ i z (Some (w,true))))
          (TypInt w) dir ≀ this.
    Proof.
      intros tag i z dir; soundtac.
      (* TODO: need some result about [P4Arith.to_loptbool]. *)
    Admitted.
    
    Lemma string_sound : forall tag s dir,
        Δ ~ Γ ⊢ₑ MkExpression tag (ExpString s) TypString dir ≀ this.
    Proof.
      intros; soundtac.
    Qed.
    
    Lemma name_sound : forall tag x loc t dir,
        is_directional dir = true ->
        typ_of_loc_var loc Γ = Some t ->
        Δ ~ Γ ⊢ₑ MkExpression tag (ExpName x loc) t dir ≀ this.
    Proof.
      intros i x l t d Hd Hgt; soundtac.
      - unfold gamma_expr_prop, gamma_var_prop, gamma_var_domain in Hg.
        destruct Hg as [[Hg _] _].
        assert (Hv : exists v, loc_to_sval l st = Some v).
        { destruct (loc_to_sval l st) as [v |] eqn:Hv; eauto.
          rewrite <- Hg, Hgt in Hv; discriminate. }
        destruct Hv; eauto.
      - unfold gamma_expr_prop, gamma_var_prop, gamma_var_val_typ in Hg.
        destruct Hg as [[_ Hg] _]; eauto.
      - rewrite Hd in H7; discriminate.
    Qed.

    Lemma constant_sound : forall tag x loc t dir,
        is_directional dir = false ->
        typ_of_loc_const this loc Γ = Some t ->
        Δ ~ Γ ⊢ₑ MkExpression tag (ExpName x loc) t dir ≀ this.
    Proof.
      intros i x l t d Hd Hgt; soundtac.
      - unfold gamma_expr_prop, gamma_const_prop, gamma_const_domain in Hg.
        destruct Hg as (_ & Hg & _).
        assert (Hv : exists v, loc_to_sval_const ge this l = Some v).
        { destruct (loc_to_sval_const ge this l) as [v |] eqn:Hv; eauto.
          rewrite <- Hg, Hgt in Hv; discriminate. }
        destruct Hv; eauto.
      - rewrite Hd in H7; discriminate.
      - unfold gamma_expr_prop, gamma_const_prop, gamma_const_val_typ in Hg.
        destruct Hg as (_ & _ & Hg); eauto.
    Qed.
    
    Lemma array_access_sound : forall tag arry idx ts dir n,
        typ_of_expr arry = TypArray (TypHeader ts) n ->
        typ_of_expr idx  = TypBit n ->
        Δ ~ Γ ⊢ₑ arry ≀ this ->
        Δ ~ Γ ⊢ₑ idx ≀ this ->
        Δ ~ Γ ⊢ₑ MkExpression
          tag (ExpArrayAccess arry idx) (TypHeader ts) dir ≀ this.
    Proof.
      intros i e1 e2 ts d n Ht1 Ht2 He1 He2;
        autounfold with * in *.
      intros rob ge st Hrob Hg Hok; simpl in *.
      rewrite Ht1, Ht2 in *.
      pose proof He1 rob ge st Hrob Hg as [[v1 Hev1] He1']; clear He1; auto.
      pose proof He2 rob ge st Hrob Hg as [[v2 Hev2] He2']; clear He2; auto.
      (*split.
      - assert (Hv2': exists v2', sval_to_val rob v2 v2')
          by eauto using exec_val_exists.
        pose proof He1' v1 Hev1 as Hv1.
        pose proof He2' v2 Hev2 as Hv2.
        destruct Hv2' as [v2' Hv2'].
        inversion Hv1; inversion Hv2; inversion Hv2';
          subst; try discriminate.
        rename v into bs; inversion H7; subst; clear H7.
        assert
          (Hz: exists z, array_access_idx_to_z (ValBaseBit lb') = Some z)
          by (simpl; eauto); destruct Hz as [z Hz].
        assert (Hreal: exists real, get_real_type ge (TypHeader ts) = Some real).
        { assert
            (Hdelta :
               Forall
                 (fun X =>
                    exists t, IdentMap.get X (ge_typ ge) = Some t) Δ) by admit.
          assert
            (Hge_typ : forall t,
                Δ ⊢ok t ->
                forall v, val_typ v t ->
                     exists t', get_real_type ge t = Some t' /\
                           val_typ v t'.
                                           
            ).
      - intros v' Haa; inversion Haa; clear Haa; subst; simpl.*)
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
        Δ ~ Γ ⊢ₑ bits ≀ this ->
        Δ ~ Γ ⊢ₑ MkExpression
          tag (ExpBitStringAccess bits lo hi)
          (TypBit (hi - lo + 1)%N) dir ≀ this.
    Proof.
      intros i e lo hi d w Hlwh Ht He.
      autounfold with * in *.
      intros rob ge st Hrob Hg Hok.
      rewrite Ht in *.
      pose proof He rob ge st Hrob Hg as [[v Hev] He']; clear He; auto.
      split.
      - apply He' in Hev as Hv;
          inversion Hv; subst; rename v0 into bits.
        exists (ValBaseBit (bitstring_slice bits (N.to_nat lo) (N.to_nat hi))).
        eapply exec_expr_bitstring_access with (wn := length bits); eauto; lia.
      - clear v Hev. intros v Hrn; inversion Hrn; subst; simpl.
        (*rename H8 into He; rename H9 into Hsval; rename H12 into Hlhw.*)
        (* Need result about [bitstring_slice]. *) admit.
    Admitted.
  
    Lemma list_sound : forall tag es dir,
        Forall (fun e => Δ ~ Γ ⊢ₑ e ≀ this) es ->
        Δ ~ Γ ⊢ₑ MkExpression tag (ExpList es)
          (TypTuple (map typ_of_expr es)) dir ≀ this.
    Proof.
      intros i es d Hes. autounfold with * in *.
      intros rob ge st Hrob Hg Hok.
      rewrite Forall_forall in Hes.
      specialize Hes with
          (read_one_bit:=rob) (ge:=ge) (st:=st).
      pose proof reduce_inner_impl _ _ _ _ Hes Hrob as Hes';
        simpl in Hes'; clear Hes.
      pose proof reduce_inner_impl _ _ _ _ Hes' Hg as Hes;
        simpl in Hes; clear Hes'.
      simpl in *; inversion Hok;
        rename H0 into Hτs; rename H into Hτs_eq.
      rewrite <- Forall_forall in Hes.
      (*rewrite Forall_map in Hτs.
      unfold Basics.compose in *.
      pose proof Forall_impl_Forall _ _ _ _ Hes Hτs as Hq.
      apply Forall_and_inv in Hq as [Hrnes Htyps]; split.
      - clear Htyps.
        rewrite Forall_exists_factor in Hrnes.
        destruct Hrnes as [vs Hvs]; eauto.
      - clear Hrnes; intros v Hrn; simpl.
        inversion Hrn; subst; clear Hrn.
        rename H6 into Hesvs.
        rewrite Forall_forall in Htyps.
        apply forall_Forall2 with (bs := vs) in Htyps;
          eauto using Forall2_length.
        apply Forall2_impl with
            (R := run_expr ge rob this st)
            (Q := fun e v => val_typ (ge_senum ge) v (typ_of_expr e)) in Htyps; auto.
        rewrite Forall2_flip, Forall2_map_r in Htyps; auto.
    Qed.*)
    Admitted.

    Lemma record_sound : forall tag es dir,
        Forall (fun e => Δ ~ Γ ⊢ₑ e ≀ this) (map snd es) ->
        Δ ~ Γ ⊢ₑ MkExpression
          tag (ExpRecord es)
          (TypRecord (map (fun '(x,e) => (x,typ_of_expr e)) es)) dir ≀ this.
    Proof.
      intros i es d Hes.
      autounfold with * in *.
      intros rob ge st Hrob Hg Hok.
      rewrite Forall_forall in Hes.
      specialize Hes with
          (read_one_bit:=rob) (ge:=ge) (st:=st).
      pose proof reduce_inner_impl _ _ _ _ Hes Hrob as Hes';
        simpl in Hes'; clear Hes.
      pose proof reduce_inner_impl _ _ _ _ Hes' Hg as Hes;
        simpl in Hes; clear Hes'.
      simpl in *; inversion Hok;
        rename H0 into Hτs; rename H into Hτs_eq.
      rewrite <- Forall_forall in Hes.
      pose proof Forall_map
           (P4Type_ok Δ) snd
           (map (fun '(x, e) => (x, typ_of_expr e)) es)
        as Hfm.
      unfold Basics.compose in Hfm.
      (*rewrite <- Hfm in Hτs; clear Hfm.
      rewrite map_snd_map in Hτs.
      rewrite Forall_map in Hτs.
      unfold Basics.compose in *.
      pose proof Forall_impl_Forall _ _ _ _ Hes Hτs as Hq.
      apply Forall_and_inv in Hq as [Hrns Htyps]; split.
      - clear Htyps.
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
        rewrite <- Hmf in Heskvs.*)
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
    
    Lemma eval_unary_op_preserves_typ : forall o v v' g t t',
        unary_type o t t' ->
        Ops.eval_unary_op o v = Some v' ->
        val_typ g v t -> @val_typ tags_t  _ g v' t'.
    Proof.
      intros o v v' g t t' Hut Heval Hvt;
        inversion Hut; subst;
          inversion Hvt; subst;
            try (inversion Heval; subst; auto; assumption).
      - unfold Ops.eval_unary_op in Heval.
        destruct (P4Arith.BitArith.from_lbool v0)
          as [w' n'] eqn:Heqfromlbool.
        injection Heval as Hv'. rewrite <- Hv'.
        inversion H; subst; clear H.
    (** TODO: need helper lemma about
        [P4Arith.to_lbool] and [P4Arith.BitArith.bit_not]. *)
    Admitted.
  
    Lemma unary_op_sound : forall tag o e t dir,
        unary_type o (typ_of_expr e) t ->
        Δ ~ Γ ⊢ₑ e ≀ this ->
        Δ ~ Γ ⊢ₑ MkExpression tag (ExpUnaryOp o e) t dir ≀ this.
    Proof.
      intros i o e t d Hut He.
      autounfold with * in *; intros rob ge st Hrob Hg Hok.
      specialize He with rob ge st.
      simpl in *.
      apply unary_type_eq in Hut as Hut_eq.
      rewrite Hut_eq in He.
      (*pose proof He Hrob Hg Hok as [[v Hev] Hvt]; clear He; split.
      - apply Hvt in Hev as Hv; clear Hvt.
        assert (exists v', sval_to_val rob v v')
          by eauto using exec_val_exists.
        destruct H as [v' Hv'].
        assert (exists v''', Ops.eval_unary_op o v' = Some v''').
        (* Maybe try to factor this out?
           Lemma exists_eval_unary_op : forall o v,
           exists v', Ops.eval_unary_op o v = Some v'. *)
        { destruct (Ops.eval_unary_op o v') as [v'' |] eqn:Heqop; eauto.
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
        pose proof
             (@exec_val_preserves_typ
                tags_t _ _ _ _ _ H8 (ge_senum ge)) as Hevpt.
        assert (Hgsb : exists gsb,
                   FuncAsMap.related
                     (AList.all_values (exec_val rob))
                     (ge_senum ge) gsb).
        { admit. }
        destruct Hgsb as [gsb Hgsb].
        pose proof Hevpt _ Hgsb _ Hargsv as Hargv.
        assert (Hv0: val_typ gsb v0 (typ_of_expr e))
          by eauto using eval_unary_op_preserves_typ.
        assert (Hgsb' :
                  FuncAsMap.related
                    (AList.all_values val_to_sval)
                    gsb (ge_senum ge)).
        { (* TODO:
             Need assumption
             [read_one_bit_inverse rob read_detbit]. *)
          admit. }
        eauto using exec_val_preserves_typ.*)
    Admitted.

    Lemma binary_op_sound : forall tag o t e1 e2 dir,
        binary_type o (typ_of_expr e1) (typ_of_expr e2) t ->
        Δ ~ Γ ⊢ₑ e1 ≀ this ->
        Δ ~ Γ ⊢ₑ e2 ≀ this ->
        Δ ~ Γ ⊢ₑ MkExpression tag (ExpBinaryOp o (e1,e2)) t dir ≀ this.
    Proof.
    Admitted.
  
    Lemma cast_sound : forall tag e t dir,
        cast_type (typ_of_expr e) t ->
        Δ ~ Γ ⊢ₑ e ≀ this ->
        Δ ~ Γ ⊢ₑ MkExpression tag (ExpCast t e) t dir ≀ this.
    Proof.
    Admitted.

    Lemma enum_member_sound : forall tag tname member ename members dir,
        (* TODO: need [ge] of [genv].
           name_to_type ge tname = Some (TypEnum ename None members) ->*)
        List.In member members ->
        Δ ~ Γ ⊢ₑ MkExpression
          tag (ExpTypeMember tname member)
          (TypEnum ename None members) dir ≀ this.
    Proof.
    Admitted.

    Lemma senum_member_sound : forall tag tname member ename t members dir,
        (*name_to_type ge tname = Some (TypEnum ename (Some etyp) members) ->
          IdentMap.get ename (ge_senum ge) = Some fields ->*)
        List.In member members ->
        Δ ~ Γ ⊢ₑ MkExpression
          tag (ExpTypeMember tname member)
          (TypEnum ename (Some t) members) dir ≀ this.
    Proof.
    Admitted.

    Lemma error_member_sound : forall tag err dir,
        Δ ~ Γ ⊢ₑ MkExpression
          tag (ExpErrorMember err) TypError dir ≀ this.
    Proof.
      soundtac.
    Qed.
  
    Lemma other_member_sound : forall tag e x ts t dir,
      member_type ts (typ_of_expr e) ->
      AList.get ts x = Some t ->
      Δ ~ Γ ⊢ₑ e ≀ this ->
      Δ ~ Γ ⊢ₑ MkExpression
        tag (ExpExpressionMember e x) t dir ≀ this.
    Proof.
    Admitted.

    Lemma array_size_sound : forall tag e x dir t w,
        (* P4Arith.BitArith.bound 32 w -> *)
        (w < 2 ^ 32)%N ->
        typ_of_expr e = TypArray t w ->
        P4String.str x = "size"%string ->
        Δ ~ Γ ⊢ₑ e ≀ this ->
        Δ ~ Γ ⊢ₑ MkExpression
          tag (ExpExpressionMember e x) (TypBit 32) dir ≀ this.
    Proof.
    Admitted.

    Lemma array_last_index_sound : forall tag e x dir t w,
        typ_of_expr e = TypArray t w ->
        P4String.str x = "lastIndex"%string ->
        Δ ~ Γ ⊢ₑ e ≀ this ->
        Δ ~ Γ ⊢ₑ MkExpression
          tag (ExpExpressionMember e x) t dir ≀ this.
    Proof.
    Admitted.

    Lemma ternary_sound : forall tag e₁ e₂ e₃ t dir,
        typ_of_expr e₁ = TypBool ->
        typ_of_expr e₂ = typ_of_expr e₃ ->
        typ_of_expr e₂ = t ->
        Δ ~ Γ ⊢ₑ e₁ ≀ this ->
        Δ ~ Γ ⊢ₑ e₂ ≀ this ->
        Δ ~ Γ ⊢ₑ e₃ ≀ this ->
        Δ ~ Γ ⊢ₑ MkExpression tag (ExpTernary e₁ e₂ e₃) t dir ≀ this.
    Proof.
    Admitted.

    Lemma dontcare_sound : forall tag dir,
        Δ ~ Γ ⊢ₑ MkExpression tag ExpDontCare TypVoid dir ≀ this.
    Proof.
      soundtac.
    Qed.
  End ExprTyping.

  Local Hint Constructors exec_stmt : core.
  Local Hint Constructors exec_block : core.
  
  Section StmtTyping.
    Variable (Γ : @gamma_stmt tags_t).
    
    Lemma assign_sound : forall tag e₁ e₂,
        typ_of_expr e₁ = typ_of_expr e₂ ->
        lexpr_ok e₁ ->
        Δ ~ Γ ⊢ₑ e₁ ≀ this ->
        Δ ~ Γ ⊢ₑ e₂ ≀ this \/ Δ ~ Γ ⊢ᵪ e₂ ≀ this ->
        Δ ~ Γ ⊢ₛ MkStatement
          tag (StatAssignment e₁ e₂) StmUnit ⊣ Γ ≀ this.
    Proof.
    Admitted.

    Lemma cond_sound : forall tag e s₁ s₂ Γ₁,
        typ_of_expr e = TypBool ->
        Δ ~ Γ ⊢ₑ e ≀ this ->
        Δ ~ Γ ⊢ₛ s₁ ⊣ Γ₁ ≀ this ->
        predopt (fun s₂ => exists Γ₂, Δ ~ Γ ⊢ₛ s₂ ⊣ Γ₂ ≀ this) s₂ ->
        Δ ~ Γ ⊢ₛ MkStatement
          tag (StatConditional e s₁ s₂)
          (match s₂ with
           | None    => typ_of_stmt s₁
           | Some s₂ => lub_StmType (typ_of_stmt s₁) (typ_of_stmt s₂)
           end) ⊣ Γ ≀ this.
    Proof.
    Admitted.

    Lemma exit_sound : forall tag,
        Δ ~ Γ ⊢ₛ MkStatement tag StatExit StmVoid ⊣ Γ ≀ this.
    Proof.
      unfold stmt_types; intros; split; eauto.
      intros ? ? Hrn; inversion Hrn; subst; eauto.
    Qed.

    Lemma return_sound : forall tag e,
        predopt (fun e => Δ ~ Γ ⊢ₑ e ≀ this) e ->
        Δ ~ Γ ⊢ₛ MkStatement tag (StatReturn e) StmVoid ⊣ Γ ≀ this.
    Proof.
    Admitted.

    Lemma empty_sound : forall tag,
        Δ ~ Γ ⊢ₛ MkStatement tag StatEmpty StmUnit ⊣ Γ ≀ this.
    Proof.
      unfold stmt_types; intros; split; eauto.
      intros ? ? Hrn; inversion Hrn; subst; eauto.
    Qed.
    
    Lemma block_sound : forall Γ' tag blk t,
        Block_StmTypes blk t ->
        Δ ~ Γ ⊢ᵦ blk ⊣ Γ' ≀ this ->
        Δ ~ Γ ⊢ₛ MkStatement tag (StatBlock blk) t ⊣ Γ ≀ this.
    Proof.
    Admitted.

    Lemma method_call_sound : forall tag e τs es,
        Δ ~ Γ ⊢ᵪ MkExpression dummy_tags
          (ExpFunctionCall e τs es)
          TypVoid Directionless ≀ this ->
        Δ ~ Γ ⊢ₛ MkStatement tag
          (StatMethodCall e τs es) StmUnit ⊣ Γ ≀ this.
    Proof.
    Admitted.

    Lemma direct_application_sound : forall tag τ es,
        Δ ~ Γ ⊢ₑ MkExpression dummy_tags
          (ExpFunctionCall
             (direct_application_expression τ)
             nil (map Some es)) TypVoid Directionless ≀ this ->
        Δ ~ Γ ⊢ₛ MkStatement tag
          (StatDirectApplication τ es) StmUnit ⊣ Γ ≀ this.
    Proof.
    Admitted.

    Lemma stat_variable_sound : forall tag τ x e l,
        predopt
          (fun e =>
             typ_of_expr e = τ /\
             (Δ ~ Γ ⊢ₑ e ≀ this \/ Δ ~ Γ ⊢ᵪ e ≀ this)) e ->
        Δ ~ Γ ⊢ₛ MkStatement
          tag (StatVariable τ x e l) StmUnit
          ⊣ bind_typ_gamma_stmt l τ Γ ≀ this.
    Proof.
    Admitted.
  End StmtTyping.
End Soundness.