Require Export Poulet4.P4light.Semantics.Typing.LvalueTyping.
Require Poulet4.P4light.Syntax.P4String
        Poulet4.Utils.Util.EquivUtil.

(** * P4light Typing Definitions *)

(** All well-typed p4light term is defined as
    one satisfying progress & preservation,
    rather than an [Inductive] rule. *)

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
             (g : gamma_var) (st : state) : Prop := forall l t,
      typ_of_loc_var l g = Some t -> exists sv, loc_to_sval l st = Some sv.

  Definition gamma_var_val_typ
             `{T : @Target tags_t expr}
             (g : gamma_var) (st : state)
             (gt : genv_typ) : Prop := forall l t v,
      typ_of_loc_var l g = Some t ->
      loc_to_sval l st = Some v ->
      exists rt, get_real_type gt t = Some rt /\ ⊢ᵥ v \: normᵗ rt.

  Definition gamma_var_prop
             `{T : @Target tags_t expr}
             (g : gamma_var) (st : state)
             (gt : genv_typ) : Prop :=
    gamma_var_domain g st /\ gamma_var_val_typ g st gt.
  
  Definition sub_gamma_var (Γ Γ' : gamma_var) : Prop :=
    FuncAsMap.submap (fun l => typ_of_loc_var l Γ) (fun l => typ_of_loc_var l Γ').
  
  Definition gamma_const_domain
             `{T : @Target tags_t expr}
             (this : path) (g : gamma_const)
             (ge : genv) : Prop := forall l t,
      typ_of_loc_const this l g = Some t ->
      exists v, loc_to_val_const ge this l = Some v.

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
  
  Definition sub_gamma_const (this : path) (Γ Γ' : gamma_const) : Prop :=
    FuncAsMap.submap
      (fun l => typ_of_loc_const this l Γ)
      (fun l => typ_of_loc_const this l Γ').
  
  Definition gamma_expr_prop
             `{T : @Target tags_t expr}
             (this : path) (g : gamma_expr) (st : state) (ge : genv) : Prop :=
    gamma_var_prop g st ge /\ gamma_const_prop this g ge.

  Definition sub_gamma_expr (this : path) (Γ Γ' : gamma_expr) : Prop :=
    sub_gamma_var Γ Γ' /\ sub_gamma_const this Γ Γ'.
  
  Notation run_expr := (@exec_expr tags_t).
  Notation run_lexpr := (@exec_lexpr tags_t).
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

  (* Function-type closures.
     TODO:
     Probably needs to be defined
     mutually with [gamma_stmt]. *)
  Record closure := {
    closure_gamma   : gamma_expr (* Typing context at definition. *); 
    closure_funtype : funtype    (* Type signature of function. *)}.
  
  (* Function definition typing environment. *)
  Definition gamma_func := PathMap.t closure.

  (* Extern instance typing environment. TODO. *)
  Definition gamma_ext := PathMap.t unit.

  (* Statement typing Environment. *)
  Record gamma_stmt : Type := {
    expr_gamma :> gamma_expr;
    func_gamma :> gamma_func;
    ext_gamma :> gamma_ext }.

  Definition
    bind_typ_gamma_stmt
    (l : Locator) (τ : typ)
    '({| expr_gamma:=eg; func_gamma:=fg;
         ext_gamma:=exg |} : gamma_stmt) : gamma_stmt :=
    {| expr_gamma:=bind_var_typ_gamma_expr l τ eg;
       func_gamma:=fg; ext_gamma:=exg |}.

  (** Typing analogue to [lookup_func]. *)
  Definition lookup_func_typ
             (this : path) (gf : gamma_func) (gi : genv_inst)
             '(MkExpression _ func _ _ : expr)
    : option (option path * closure) :=
    match func with
    | ExpName _ (LGlobal p) =>
      option_map (fun funt => (Some nil, funt)) (PathMap.get p gf)
    | ExpName _ (LInstance p) =>
      let* '{|iclass:=class|} := PathMap.get this gi in
      let^ ft := PathMap.get (class :: p) gf in (None,ft)
    | ExpExpressionMember (MkExpression _ (ExpName _ (LInstance p)) _ _) x
      => let* '{|iclass:=class; ipath:=inst_path|} := PathMap.get (this ++ p) gi in
        let^ ft := PathMap.get [class; P4String.str x] gf in (Some inst_path, ft)
    | ExpExpressionMember (MkExpression _ (ExpName _ (LGlobal p)) _ _) x
      => let* '{|iclass:=class; ipath:=inst_path|} := PathMap.get p gi in
        let^ ft := PathMap.get [class; P4String.str x] gf in (Some inst_path, ft)
    | _ => None
    end.

  Definition gamma_func_domain
             `{T : @Target tags_t expr}
             (this : path) (gf : gamma_func)
             (ge : genv) : Prop := forall e ft,
      lookup_func_typ this gf ge e = Some ft ->
      exists fd, lookup_func ge this e = Some fd.
  
  Definition lub_StmType (τ₁ τ₂ : StmType) : StmType :=
    match τ₁, τ₂ with
    | StmUnit, _
    | _, StmUnit => StmUnit
    | _, _       => StmVoid
    end.

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

  Section Typing.
    Context `{T : @Target tags_t expr} (** Architecture/target.*).
    Variables
      (ge : genv)       (** Statically determined global environment. *)
      (this : path)     (** Local path. *)
      (Δ : list string) (** Type variables in context. *).

    (** Expression typing. *)
    Definition
      expr_types
      (Γ : gamma_expr)  (** Typing environment. *)
      (e : expr)        (** Expression to type. *)
      : Prop :=
      genv_is_expr_typ ge ->             (** [ge] preserves [is_expr_typ]. *)
      delta_genv_prop ge Δ ->            (** The domain of [ge_typ ge] is [Δ]. *)
      Δ ⊢okᵉ e ->                        (** Type variables are bound. *)
      is_expr e ->                       (** Is a well-formed expression. *)
      forall (read_one_bit : option bool -> bool -> Prop) (** Interprets uninitialized bits. *)
        (st : state)                      (** Runtime environment. *),
        (forall b b', read_one_bit (Some b) b'
                 <-> b = b')             ->  (** Interprets initialized bits correctly. *)
        read_one_bit_reads read_one_bit -> (** [read_one_bit] is productive. *)
        gamma_expr_prop this Γ st ge ->    (** Static & dynamic environments agree. *)
        (** Progress. *)
        (exists v, run_expr ge read_one_bit this st e v) /\
        (** Preservation. *)
        (forall v, run_expr ge read_one_bit this st e v ->
              exists rt, get_real_type ge (typ_of_expr e) = Some rt /\
                    ⊢ᵥ v \: normᵗ rt) /\
        (** L-expression progress & preservation. *)
        (lexpr_ok e ->
         (exists lv s, run_lexpr ge read_one_bit this st e lv s) /\
         forall lv s, run_lexpr ge read_one_bit this st e lv s ->
                 var_gamma Γ ⊢ₗlv \: typ_of_expr e).
    (**[]*)

    Variant fundef_funtype_prop
            (Γ : gamma_expr) (Γext : gamma_ext)
      : @fundef tags_t -> funtype -> Prop :=
    (* TODO : need to know [body] & [init] are well-typed. *)
    | Internal_prop params body Xs params' rt :
        Forall2 (fun '(_,d) '(MkParameter _ d' _ _ _) => d = d') params params' ->
        (** Should use a closure environment to type [body]. *)
        fundef_funtype_prop
          Γ Γext
          (FInternal params body)
          (MkFunctionType Xs params' FunFunction rt)
    | Table_match name keys actions dflt entries key_typs :
        Forall2
          (fun '(MkTableKey _ e mk) '(t,mk') =>
             expr_types Γ e /\
             typ_of_expr e = t /\ P4String.str mk = mk')
          keys key_typs ->
        fundef_funtype_prop
          Γ Γext
          (FTable name keys actions dflt entries)
          (MkFunctionType [] [] FunTable TypVoid)
    | External_match class name Xs params rt :
        (* TODO: lookup [FExternal] by [class] or [name]. *)
        fundef_funtype_prop
          Γ Γext
          (FExternal class name)
          (MkFunctionType Xs params FunExtern rt).

    Definition gamma_func_types
               (gf : gamma_func)
               (gext : gamma_ext) : Prop :=
      forall (e : expr) (p p' : option path)
        (fd : fundef) (clos : closure),
        lookup_func_typ this gf ge e = Some (p,clos) ->
        lookup_func ge this e = Some (p',fd) ->
        p = p' /\
        fundef_funtype_prop
          (closure_gamma clos)
          gext fd
          (closure_funtype clos).

  Definition gamma_func_prop
             (gf : gamma_func) (gext : gamma_ext) : Prop :=
    gamma_func_domain this gf ge /\
    gamma_func_types gf gext.

  (** TODO: externs... *)
  Definition gamma_stmt_prop
             (g : gamma_stmt) (st : state) : Prop :=
    gamma_expr_prop this (expr_gamma g) st ge /\
    gamma_func_prop (func_gamma g) (ext_gamma g).
    
    (** Statement typing. *)
    Definition
      stmt_types
      (Γ Γ' : gamma_stmt) (* Input & output typing environment. *)
      (s : stmt)          (* Statement in question. *)
      : Prop :=
      genv_is_expr_typ ge ->             (** [ge] preserves [is_expr_typ]. *)
      delta_genv_prop ge Δ ->            (** The domain of [ge_typ ge] is [Δ]. *)
      Δ ⊢okˢ s ->                        (** Free type variables are bound. *)
      is_stmt s ->                       (** Is a well-formed statement. *)
      forall (dummy : Inhabitant tags_t)       (** Default [tags_t]. *)
        (read_one_bit : option bool -> bool -> Prop) (** Interpretation of uninitialized bits. *)
        (st : state),                     (** The evaluation environment. *)
        (forall b b', read_one_bit (Some b) b'
                 <-> b = b')             ->  (** Interprets initialized bits correctly. *)
        read_one_bit_reads read_one_bit -> (** [read_one_bit] is productive. *)
        gamma_stmt_prop Γ st ->            (** [st] is well-typed. *)
        sub_gamma_expr this Γ Γ' /\
        (** Progress. *)
        (exists st' sig, run_stmt ge read_one_bit this st s st' sig) /\
        (** Preservation. *)
        forall st' sig, run_stmt ge read_one_bit this st s st' sig ->
                   gamma_stmt_prop Γ' st'.

    (** Block typing. *)
    Definition
      block_types
      (Γ Γ' : gamma_stmt) (* Input & output typing environments. *)
      (blk : block)       (* Statement block. *)
      : Prop :=
      genv_is_expr_typ ge ->             (** [ge] preserves [is_expr_typ]. *)
      delta_genv_prop ge Δ ->            (** The domain of [ge_typ ge] is [Δ]. *)
      Δ ⊢okᵇ blk ->                      (** Free type variables are bound. *)
      is_block blk ->                    (** Is a well-formed block. *)
      forall (dummy : Inhabitant tags_t)       (** Default [tags_t]. *)
        (read_one_bit : option bool -> bool -> Prop) (** Interpretation of uninitialized bits. *)
        (st : state),                     (** The evaluation environment. *)
        (forall b b', read_one_bit (Some b) b'
                 <-> b = b')             ->  (** Interprets initialized bits correctly. *)
        read_one_bit_reads read_one_bit -> (** [read_one_bit] is productive. *)
        gamma_stmt_prop Γ st ->            (** [st] is well-typed. *)
        sub_gamma_expr this Γ Γ' /\
        FuncAsMap.submap (var_gamma Γ) (var_gamma Γ') /\
        (exists st' sig, run_blk ge read_one_bit this st blk st' sig) /\
        forall st' sig, run_blk ge read_one_bit this st blk st' sig ->
                   gamma_stmt_prop Γ' st'.
  
    (** Call typing. *)
    Definition
      call_types
      (Γ : gamma_stmt)  (* Typing environment. *)
      (call : expr)     (* Call expression. *)
      : Prop :=
      genv_is_expr_typ ge ->             (** [ge] preserves [is_expr_typ]. *)
      delta_genv_prop ge Δ ->            (** The domain of [ge_typ ge] is [Δ]. *)
      Δ ⊢okᵉ call ->                     (** Free type variables are bound. *)
      forall (dummy : Inhabitant tags_t)       (** Default [tags_t]. *)
        (read_one_bit : option bool -> bool -> Prop) (** Interpretation of uninitialized bits. *)
        (st : state),                     (** The evaluation environment. *)
        (forall b b', read_one_bit (Some b) b'
                 <-> b = b')             ->  (** Interprets initialized bits correctly. *)
        read_one_bit_reads read_one_bit -> (** [read_one_bit] is productive. *)
        gamma_stmt_prop Γ st ->            (** [st] is well-typed. *)
        (** Progress. *)
        (exists st' sig, run_call ge read_one_bit this st call st' sig) /\
        (** Preservation. *)
        forall st' sig, run_call ge read_one_bit this st call st' sig ->
                   gamma_stmt_prop Γ st'.
  End Typing.
End TypingDefs.

Notation "x '⊢ₑ' e"
  := (expr_types
        (fst (fst (fst x)))
        (snd (fst (fst x)))
        (snd (fst x)) (snd x) e)
       (at level 80, no associativity) : type_scope.
Notation "x 'ᵗ⊢ₑ' e \: t"
  := (x ⊢ₑ e /\ t = typ_of_expr e)
       (at level 80, no associativity) : type_scope.
Notation "x '⊢ₛ' s ⊣ Γ₂"
  := (stmt_types
        (fst (fst (fst x)))
        (snd (fst (fst x)))
        (snd (fst x)) (snd x)
        Γ₂ s)
       (at level 80, no associativity) : type_scope.
Notation "x '⊢ᵦ' blk ⊣ Γ₂"
  := (block_types
        (fst (fst (fst x)))
        (snd (fst (fst x)))
        (snd (fst x)) (snd x)
        Γ₂ blk)
       (at level 80, no associativity) : type_scope.
Notation "x '⊢ᵪ' e"
  := (call_types
        (fst (fst (fst x)))
        (snd (fst (fst x)))
        (snd (fst x)) (snd x) e)
       (at level 80, no associativity) : type_scope.
