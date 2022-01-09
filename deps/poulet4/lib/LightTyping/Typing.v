Require Export Poulet4.LightTyping.ValueTyping
        Poulet4.Monads.Monad Poulet4.Monads.Option.
Require Poulet4.P4String Poulet4.P4cub.Util.EquivUtil.

(** * P4light Typing Definitions *)

Section TypingDefs.
  Context {tags_t : Type}.

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

  Definition gamma_var_domain
             `{T : @Target tags_t expr}
             (g : gamma_var) (st : state) : Prop :=
    forall l : Locator, typ_of_loc_var l g = None <-> loc_to_sval l st = None.

  Definition gamma_var_val_typ
             `{T : @Target tags_t expr}
             (g : gamma_var) (st : state)
             (gt : genv_typ) : Prop :=
    forall l t v,
      typ_of_loc_var l g = Some t ->
      loc_to_sval l st = Some v ->
      exists rt, get_real_type gt t = Some rt /\ ⊢ᵥ v \: normᵗ rt.

  Definition gamma_var_prop
             `{T : @Target tags_t expr}
             (g : gamma_var) (st : state)
             (gt : genv_typ) : Prop :=
    gamma_var_domain g st /\ gamma_var_val_typ g st gt.
  
  Definition gamma_const_domain
             `{T : @Target tags_t expr}
             (this : path) (g : gamma_const)
             (ge : genv) : Prop :=
    forall l : Locator,
      typ_of_loc_const this l g = None <-> loc_to_sval_const ge this l = None.

  Definition gamma_const_val_typ
             `{T : @Target tags_t expr}
             (this : path) (g : gamma_const)
             (ge : genv) : Prop :=
    forall l t v,
      typ_of_loc_const this l g = Some t ->
      loc_to_sval_const ge this l = Some v ->
      exists rt, get_real_type ge t = Some rt /\
            ⊢ᵥ v \: normᵗ rt.
  
  Definition gamma_const_prop
             `{T : @Target tags_t expr}
             (this : path) (g : gamma_const) (ge : genv) : Prop :=
    gamma_const_domain this g ge /\ gamma_const_val_typ this g ge.
  
  Definition gamma_expr_prop
             `{T : @Target tags_t expr}
             (this : path) (g : gamma_expr) (st : state) (ge : genv) : Prop :=
    gamma_var_prop g st ge /\ gamma_const_prop this g ge.
  
  Notation run_expr := (@exec_expr tags_t).
  Notation run_stmt := (@exec_stmt tags_t).
  Notation run_blk  := (@exec_block tags_t).
  Notation run_call := (@exec_call tags_t).

  Definition typ_of_expr
             '(MkExpression _ _ t _ : expr) : typ := t.

  Definition typ_of_stmt
             '(MkStatement _ _ t : stmt) : StmType := t.
  
  Definition delta_genv_prop
             (ge : @genv_typ tags_t) : list string -> Prop :=
    Forall (fun X => exists t, IdentMap.get X ge = Some t /\ [] ⊢ok t).

  Definition genv_is_expr_typ (ge : @genv_typ tags_t) : Prop :=
    forall t r, get_real_type ge t = Some r ->
           is_expr_typ t -> is_expr_typ r.
  
  (** Expression typing. *)
  Definition
    expr_types
    (this : path)     (** Local path. *)
    (Δ : list string) (** Type variables in context. *)
    (Γ : gamma_expr)  (** Typing environment. *)
    (e : expr)        (** Expression to type. *)
    : Prop :=
    forall (T : @Target tags_t expr)
      (read_one_bit : option bool -> bool -> Prop)
      (ge : genv) (st : state),
      delta_genv_prop ge Δ ->            (** The domain of [ge_typ ge] is [Δ]. *)
      read_one_bit_reads read_one_bit -> (** [read_one_bit] is productive. *)
      gamma_expr_prop this Γ st ge ->    (** Static & dynamic environments agree. *)
      Δ ⊢ok typ_of_expr e ->             (** Type variables are bound. *)
      is_expr_typ (typ_of_expr e) ->     (** Is a valid expression type. *)
      genv_is_expr_typ ge ->             (** [ge] preserves [is_expr_typ]. *)
      (** Progress. *)
      (exists v, run_expr ge read_one_bit this st e v) /\
      (* Preservation. *)
      forall v, run_expr ge read_one_bit this st e v ->
           exists rt, get_real_type ge (typ_of_expr e) = Some rt /\
                 ⊢ᵥ v \: normᵗ rt.
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
             `{T : @Target tags_t expr}
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
  
  Definition gamma_func_types
             `{T : @Target tags_t expr}
             (this : path) (d : list string)
             (g : gamma_expr) (gf : gamma_func)
             (gi : genv_inst) (gext : gamma_ext) (ge : genv) : Prop :=
    forall (e : expr) (p p' : option path) (fd : fundef) (ft : funtype),
      lookup_func_typ this gf gi e = Some (p,ft) ->
      lookup_func ge this e = Some (p',fd) ->
      p = p' /\ fundef_funtype_prop d g gext this fd ft.

  Definition gamma_func_prop
             `{T : @Target tags_t expr}
             (this : path) (d : list string)
             (g : gamma_expr) (gf : gamma_func)
             (gi : genv_inst) (gext : gamma_ext) (ge : genv) : Prop :=
    gamma_func_domain this gf gi ge /\
    gamma_func_types this d g gf gi gext ge.

  (** TODO: externs... *)
  Definition gamma_stmt_prop
             `{T : @Target tags_t expr}
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
    forall (dummy : Inhabitant tags_t)
      (T : @Target tags_t expr)
      (read_one_bit : option bool -> bool -> Prop)
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
    forall (dummy : Inhabitant tags_t)
      (T : @Target tags_t expr)
      (read_one_bit : option bool -> bool -> Prop)
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
    forall (dummy : Inhabitant tags_t)
      (T : @Target tags_t expr)
      (read_one_bit : option bool -> bool -> Prop) (ge : genv) (st : state),
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
