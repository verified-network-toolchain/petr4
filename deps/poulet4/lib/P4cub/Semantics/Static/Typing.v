Require Import Coq.PArith.BinPos Coq.ZArith.BinInt Coq.NArith.BinNat
        Poulet4.P4cub.Syntax.AST Poulet4.Utils.P4Arith
        Poulet4.P4cub.Syntax.CubNotations
        Poulet4.P4cub.Semantics.Static.Util.
From RecordUpdate Require Import RecordSet.
Import String AllCubNotations Clmt.Notations RecordSetNotations.

(** * Expression typing. *)

Reserved Notation "'`⟨' Δ , Γ ⟩ ⊢ e ∈ τ" (at level 80, no associativity).

Local Open Scope ty_scope.
Local Open Scope expr_scope.

Inductive type_expr (Δ : nat) (Γ : list Expr.t)
  : Expr.e -> Expr.t -> Prop :=
| type_bool (b : bool) :
  `⟨ Δ, Γ ⟩ ⊢ b ∈ Expr.TBool
| type_bit w n :
  BitArith.bound w n ->
  `⟨ Δ, Γ ⟩ ⊢ w `W n ∈ Expr.TBit w
| type_int w n :
  IntArith.bound w n ->
  `⟨ Δ, Γ ⟩ ⊢ w `S n ∈ Expr.TInt w
| type_var τ og x :
  nth_error Γ x = Some τ ->
  t_ok Δ τ ->
  `⟨ Δ, Γ ⟩ ⊢ Expr.Var τ og x ∈ τ
| type_slice hi lo e w τ :
  (Npos lo <= Npos hi < w)%N ->
  numeric_width w τ ->
  `⟨ Δ, Γ ⟩ ⊢ e ∈ τ ->
  `⟨ Δ, Γ ⟩ ⊢ Expr.Slice hi lo e ∈ Expr.TBit (Npos hi - Npos lo + 1)%N
| type_cast τ τ' e :
  proper_cast τ' τ ->
  t_ok Δ τ ->
  `⟨ Δ, Γ ⟩ ⊢ e ∈ τ' ->
  `⟨ Δ, Γ ⟩ ⊢ Expr.Cast τ e ∈ τ
| type_uop op τ τ' e :
  uop_type op τ τ' ->
  t_ok Δ τ' ->
  `⟨ Δ, Γ ⟩ ⊢ e ∈ τ ->
  `⟨ Δ, Γ ⟩ ⊢ Expr.Uop τ' op e ∈ τ'
| type_bop op τ₁ τ₂ τ e₁ e₂ :
  bop_type op τ₁ τ₂ τ ->
  t_ok Δ τ ->
  `⟨ Δ, Γ ⟩ ⊢ e₁ ∈ τ₁ ->
  `⟨ Δ, Γ ⟩ ⊢ e₂ ∈ τ₂ ->
  `⟨ Δ, Γ ⟩ ⊢ Expr.Bop τ op e₁ e₂ ∈ τ
| type_index e₁ e₂ w τ :
  t_ok Δ τ ->
  `⟨ Δ, Γ ⟩ ⊢ e₁ ∈ Expr.TArray (Z.to_N (BitArith.upper_bound w)) τ ->
  `⟨ Δ, Γ ⟩ ⊢ e₂ ∈ Expr.TBit w ->
  `⟨ Δ, Γ ⟩ ⊢ Expr.Index τ e₁ e₂ ∈ τ
| type_member τ x e τs b :
  nth_error τs x = Some τ ->
  t_ok Δ τ ->
  `⟨ Δ, Γ ⟩ ⊢ e ∈ Expr.TStruct b τs ->
  `⟨ Δ, Γ ⟩ ⊢ Expr.Member τ x e ∈ τ
| type_lists ls es τ τs :
  t_ok_lists Δ ls ->
  type_lists_ok ls τ τs ->
  Forall2 (type_expr Δ Γ) es τs ->
  `⟨ Δ, Γ ⟩ ⊢ Expr.Lists ls es ∈ τ
| type_error err :
  `⟨ Δ, Γ ⟩ ⊢ Expr.Error err ∈ Expr.TError
where "'`⟨' Δ , Γ ⟩ ⊢ e ∈ τ" := (type_expr Δ Γ e τ) : type_scope.

Local Close Scope expr_scope.
Local Open Scope pat_scope.

(** Select-pattern-typing. *)
Inductive type_pat : Parser.pat -> Expr.t -> Prop :=
| type_wild t : type_pat Parser.Wild t
| type_mask p₁ p₂ w :
  type_pat p₁ (Expr.TBit w) ->
  type_pat p₂ (Expr.TBit w) ->
  type_pat (Parser.Mask p₁ p₂) (Expr.TBit w)
| type_range p₁ p₂ w :
  type_pat p₁ (Expr.TBit w) ->
  type_pat p₂ (Expr.TBit w) ->
  type_pat (Parser.Range p₁ p₂) (Expr.TBit w)
| type_pbit w n :
  type_pat (w PW n) (Expr.TBit w)
| type_pint w z :
  type_pat (w PS z) (Expr.TInt w)
| type_pstruct ps ts :
  Forall2 type_pat ps ts ->
  type_pat (Parser.Lists ps) (Expr.TStruct false ts).
Local Close Scope pat_scope.

(** Parser-expression typing. *)
Variant type_prsrexpr 
        (total_states : nat) (Δ : nat) (Γ : list Expr.t)
  : Parser.pt -> Prop :=
  | type_goto (st : Parser.state_label) :
    valid_state total_states st ->
    type_prsrexpr total_states Δ Γ (Parser.Direct st)
  | type_select e default cases τ :
    valid_state total_states default ->
    `⟨ Δ, Γ ⟩ ⊢ e ∈ τ ->
    Forall
      (fun '(p,st) => type_pat p τ /\ valid_state total_states st)
      cases ->
    type_prsrexpr total_states Δ Γ (Parser.Select e default cases).

(** * Statement typing. *)
Inductive type_fun_kind
  (Δ : nat) (Γ : list Expr.t) (fs : fenv) (c : ctx)
    : Stmt.fun_kind -> list Expr.t -> Expr.params -> Prop :=
| type_call_funct f τs oe params ot :
  fs f = Some (List.length τs, {|paramargs:=params; rtrns:=ot|}) ->
  predop lvalue_ok oe ->
  relop (type_expr Δ Γ) oe (option_map (tsub_t (gen_tsub τs)) ot) ->
  type_fun_kind Δ Γ fs c (Stmt.Funct f τs oe) τs params
| type_call_action a cargs aa cparams params :
  action_call_ok aa c ->
  aa a = Some (cparams,params) ->
  Forall2 (type_expr Δ Γ) cargs cparams ->
  type_fun_kind Δ Γ fs c (Stmt.Action a cargs) [] params
| type_call_method ei m τs oe params ot extern_insts methods :
  extern_call_ok extern_insts c ->
  extern_insts ei = Some (inl methods) ->
  Field.get m methods = Some (List.length τs, {|paramargs:=params; rtrns:=ot|}) ->
  predop lvalue_ok oe ->
  relop (type_expr Δ Γ) oe (option_map (tsub_t (gen_tsub τs)) ot) ->
  type_fun_kind Δ Γ fs c (Stmt.Method ei m τs oe) τs params.

Definition type_arg
  (Δ : nat) (Γ : list Expr.t) : Expr.arg -> Expr.param -> Prop :=
  rel_paramarg
    (type_expr Δ Γ)
    (fun e τ => `⟨ Δ, Γ ⟩ ⊢ e ∈ τ /\ lvalue_ok e).

Definition type_args
  (Δ : nat) (Γ : list Expr.t) : Expr.args -> list Expr.param -> Prop :=
  Forall2 (type_arg Δ Γ).

Reserved Notation "'`⧼' Δ , Γ , f , c ⧽ ⊢ s ⊣ sig" (at level 80, no associativity).

Local Open Scope stmt_scope.

Inductive type_stmt (Δ : nat) (Γ : list Expr.t) (fs : fenv)
  : ctx -> Stmt.s -> signal -> Prop :=
| type_skip c :
  `⧼ Δ, Γ, fs, c ⧽ ⊢ Stmt.Skip ⊣ Cont
| type_return c eo :
  match c, eo with
  | CFunction (Some τ), Some e => `⟨ Δ, Γ ⟩ ⊢ e ∈ τ
  | c, None => return_void_ok c
  | _, _ => False
  end ->
  `⧼ Δ, Γ, fs, c ⧽ ⊢ Stmt.Return eo ⊣ Return
| type_exit c :
  exit_ctx_ok c ->
  `⧼ Δ, Γ, fs, c ⧽ ⊢ Stmt.Exit ⊣ Exit
| type_transition total_states i e :
  type_prsrexpr total_states Δ Γ e ->
  `⧼ Δ, Γ, fs, CParserState total_states i ⧽ ⊢ Stmt.Transition e ⊣ Trans
| type_assign c τ e₁ e₂ :
  lvalue_ok e₁ ->
  `⟨ Δ, Γ ⟩ ⊢ e₁ ∈ τ ->
  `⟨ Δ, Γ ⟩ ⊢ e₂ ∈ τ ->
  `⧼ Δ, Γ, fs, c ⧽ ⊢ e₁ `:= e₂ ⊣ Cont
| type_fun_call c params τs args fk :
  type_fun_kind Δ Γ fs c fk τs params ->
  Forall (t_ok Δ) τs ->
  type_args Δ Γ args (map (tsub_param (gen_tsub τs)) (map snd params)) ->
  `⧼ Δ, Γ, fs, c ⧽ ⊢ Stmt.Call fk args ⊣ Cont
| type_apply
    c extern_args args x extern_params params sig insts :
  apply_instance_ok insts sig c ->
  insts x = Some (inr (sig,extern_params,params)) ->
  type_args Δ Γ args (map snd params) ->
  `⧼ Δ, Γ, fs, c ⧽ ⊢ Stmt.Apply x extern_args args ⊣ Cont
| type_invoke tbl tbls aa i :
  In tbl tbls ->
  `⧼ Δ, Γ, fs, CApplyBlock tbls aa i ⧽ ⊢ Stmt.Invoke tbl ⊣ Cont
| type_vardecl c og τ te s sig :
    match te with
    | inr e => `⟨ Δ, Γ ⟩ ⊢ e ∈ τ
    | inl τ' => τ' = τ /\ t_ok Δ τ'
    end ->
    `⧼ Δ, τ :: Γ, fs, c ⧽ ⊢ s ⊣ sig ->
    `⧼ Δ, Γ, fs, c ⧽ ⊢ Stmt.Var og te s ⊣ sig
| type_seq c s₁ s₂ sig₁ sig₂ :
  `⧼ Δ, Γ, fs, c ⧽ ⊢ s₁ ⊣ sig₁ ->
  `⧼ Δ, Γ, fs, c ⧽ ⊢ s₂ ⊣ sig₂ ->
  `⧼ Δ, Γ, fs, c ⧽ ⊢ s₁ `; s₂ ⊣ sig₂
| type_cond c e s₁ s₂ sig₁ sig₂ sig :
  lub sig₁ sig₂ = Some sig ->
  `⟨ Δ, Γ ⟩ ⊢ e ∈ Expr.TBool ->
  `⧼ Δ, Γ, fs, c ⧽ ⊢ s₁ ⊣ sig₁ ->
  `⧼ Δ, Γ, fs, c ⧽ ⊢ s₂ ⊣ sig₂ ->
  `⧼ Δ, Γ, fs, c ⧽ ⊢ If e Then s₁ Else s₂ ⊣ sig
where "'`⧼' Δ , Γ , fs , c ⧽ '⊢' s ⊣ sig" := (type_stmt Δ Γ fs c s sig).

Local Close Scope stmt_scope.

(** * Control-declaration typing. *)

(** Control-declaration typing context. *)
Record ctrl_type_env : Set :=
  mk_ctrl_type_env
    { ctype_vars : nat
    ; ctypes : list Expr.t
    ; cfuncts : fenv (** available functions. *)
    ; cinsts : ienv  (** available control instances. *)
    ; actns : aenv   (** available action signatures. *)
    ; tbls : list string (** available table names. *) }.

Global Instance eta_ctrl_type_env : Settable _ :=
  settable! mk_ctrl_type_env
  < ctype_vars ; ctypes ; cfuncts ; cinsts ; actns ; tbls >.

Reserved Notation "Γ '⊢ᵪ' d '⊣' result"
         (at level 80, no associativity).

Variant ctrldecl_type : Set :=
  | ctrl_var_type (τ : Expr.t)
  | ctrl_act_type (a : string)
      (ctrl_params : list Expr.t) (data_params : Expr.params)
  | ctrl_tbl_type (t : string).

(** Control declaration typing,
    Producing either a new action or table. *)
Variant type_ctrldecl (Γ : ctrl_type_env)
  : Control.d -> ctrldecl_type -> Prop :=
  | type_ctrl_var x te τ :
    match te with
    | inr e => `⟨ ctype_vars Γ, ctypes Γ ⟩ ⊢ e ∈ τ
    | inl τ' => τ' = τ /\ t_ok (ctype_vars Γ) τ'
    end ->
    Γ ⊢ᵪ Control.Var x te ⊣ ctrl_var_type τ
  | type_action action_name cparams dparams body sig :
    `⧼ ctype_vars Γ, map snd cparams ++ bind_all dparams (ctypes Γ),
        cfuncts Γ, CAction (actns Γ) (cinsts Γ) ⧽ ⊢ body ⊣ sig ->
    Γ ⊢ᵪ Control.Action action_name cparams dparams body
      ⊣ ctrl_act_type action_name (map snd cparams) dparams
  | type_table table_name key actions :
    (** Keys type. *)
    Forall
      (fun e => exists τ, `⟨ ctype_vars Γ, ctypes Γ ⟩ ⊢ e ∈ τ) (map fst key) ->
    (** Actions type *)
    Forall
      (fun '(a,data_args) =>
         exists ctrl_params data_params,
           actns Γ a = Some (ctrl_params, data_params)
           /\ type_args (ctype_vars Γ) (ctypes Γ)
               data_args (List.map snd data_params))
      actions ->
    Γ ⊢ᵪ Control.Table
      table_name key actions ⊣  ctrl_tbl_type table_name
where "Γ '⊢ᵪ' d '⊣' result"
  := (type_ctrldecl Γ d result) : type_scope.

(** * Toplevel-declaration typing. *)

(* TODO: add packages to [ienv]. *)
Record top_type_env : Set :=
  mk_top_type_env
    { tfuncts : fenv (** available function signatures. *)
    ; cnstrs : constructor_env (** available constructors. *)
    ; insts_env : ienv (** available instances for parsers, controls, externs. *) }.

Global Instance eta_top_type_env : Settable _ :=
  settable! mk_top_type_env
  < tfuncts ; cnstrs ; insts_env >.

Reserved Notation "Γ₁ '⊢ₜ' d ⊣ Γ₂"
         (at level 80, no associativity).

Local Open Scope climate_scope.

Definition type_ctrl
           (params : Expr.params)
           (Γ : list Expr.t)
           (fs : fenv)
           (cis : ienv)
           (ctrl : list Control.d) : ctrl_type_env -> Prop :=
  FoldLeft
    (fun d Γ Γ' =>
       exists result,
         Γ ⊢ᵪ d ⊣ result /\
           match result with
           | ctrl_var_type τ =>
               Γ' = Γ <| ctypes := τ :: Γ.(ctypes) |>
           | ctrl_act_type an cps dps =>
               Γ' = Γ <| actns := an ↦ (cps, dps) ,, actns Γ |>
           | ctrl_tbl_type tn =>
               Γ' = Γ <| tbls := tn :: tbls Γ |>
           end)
    ctrl
    {| ctype_vars := 0
    ; ctypes := bind_all params Γ
    ; cfuncts := fs
    ; cinsts := cis
    ; actns := ∅ ; tbls := [] |}.

(** Top-level declaration typing. *)
Inductive type_topdecl (Γ : top_type_env)
  : TopDecl.d -> top_type_env -> Prop :=
| type_instantiate_control
    control_decl_name instance_name
    cparams expr_cparams cargs expr_cargs extern_params params :
  cnstrs Γ control_decl_name =
    Some (ControlType cparams expr_cparams extern_params params) ->
  Forall2
    (fun carg cparam =>
       match cparam with
       | TopDecl.ControlInstType eps ps
         => insts_env Γ carg = Some (inr (ControlSig,eps,ps))
       | TopDecl.ExternInstType extern_type
         => (* TODO:
              How to represent extern types?
              [nth_error (externs (insts_envs Γ)) extn = extern_type] *)
           False
       | _ => False
       end) cargs cparams ->
  Forall2
    (type_expr 0 [])
    expr_cargs expr_cparams ->
  Γ ⊢ₜTopDecl.Instantiate
    control_decl_name instance_name [] cargs expr_cargs
    ⊣ Γ <| insts_env :=
    insts_bind_other
      instance_name ControlSig extern_params params
      Γ.(insts_env) |>
| type_instantiate_parser
    parser_decl_name instance_name
    cparams expr_cparams cargs expr_cargs extern_params params :
  cnstrs Γ parser_decl_name =
    Some (ParserType cparams expr_cparams extern_params params) ->
  Forall2
    (fun carg cparam =>
       match cparam with
       | TopDecl.ParserInstType eps ps
         => insts_env Γ carg = Some (inr (ParserSig,eps,ps))
       | TopDecl.ExternInstType extern_type
         => (* TODO:
              How to represent extern types?
              [nth_error (externs (insts_envs Γ)) extn = extern_type] *)
           False
       | _ => False
       end) cargs cparams ->
  Forall2
    (type_expr 0 [])
    expr_cargs expr_cparams ->
  Γ ⊢ₜTopDecl.Instantiate
    parser_decl_name instance_name [] cargs expr_cargs
    ⊣ Γ <| insts_env :=
      insts_bind_other
        instance_name ParserSig extern_params params
        Γ.(insts_env) |>
| type_instantiate_package
    package_decl_name instance_name
    cparams expr_cparams cargs expr_cargs :
  cnstrs Γ package_decl_name =
    Some (PackageType cparams expr_cparams) ->
  Forall2
    (fun carg cparam =>
       match cparam with
       | TopDecl.ControlInstType eps ps
         => insts_env Γ carg = Some (inr (ControlSig,eps,ps))
       | TopDecl.ParserInstType eps ps
         => insts_env Γ carg = Some (inr (ParserSig,eps,ps))
       | TopDecl.ExternInstType extern_type
         => (* TODO:
              How to represent extern types?
              [nth_error (externs (insts_envs Γ)) extn = extern_type] *)
           False
       | _ => False
       end) cargs cparams ->
  Forall2
    (type_expr 0 [])
    expr_cargs expr_cparams ->
  Γ ⊢ₜTopDecl.Instantiate
    package_decl_name instance_name [] cargs expr_cargs
    ⊣ Γ (* TODO: represent package types in [ienv] *)
| type_instantiate_extern
    (* TODO: How to represent extern types & type instantiations? *)
    extern_decl_name extern_name
    expr_cparams cparams τs expr_cargs cargs methods :
  Forall (t_ok 0) τs ->
  cnstrs Γ extern_decl_name =
    Some (ExternType (List.length τs) cparams expr_cparams extern_name) ->
  Forall2
    (fun carg cparam =>
       match cparam with
       | TopDecl.ExternInstType extern_type
         => (* TODO:
              How to represent extern types?
              [nth_error (externs (insts_envs Γ)) extn = extern_type] *)
           False
       | _ => False
       end)
    cargs (map (tsub_cparam (gen_tsub τs)) cparams) ->
  Forall2
    (type_expr 0 [])
    expr_cargs (map (tsub_t (gen_tsub τs)) expr_cparams) ->
  Γ ⊢ₜ TopDecl.Instantiate extern_decl_name extern_name τs cargs expr_cargs
    ⊣ Γ <| insts_env := (* TODO: sub [τs] into methods *)
         insts_bind_externs
           extern_name methods Γ.(insts_env) |>
| type_control
    control_name cparams expr_cparams extern_params params
    control_decls apply_blk Γ' sig insts :
  (* TODO: check params are [t_ok []] *)
  (* TODO: add extern runtime params
     to instance envrionment when checking control body. *)
  insts = cbind_all (insts_env Γ) cparams ->
  type_ctrl
    params expr_cparams (tfuncts Γ) insts control_decls Γ' ->
  `⧼ 0, bind_all params expr_cparams,
      tfuncts Γ, CApplyBlock (tbls Γ') (actns Γ') insts ⧽
    ⊢ apply_blk ⊣ sig ->
  Γ ⊢ₜ
    TopDecl.Control
    control_name cparams expr_cparams extern_params
    params control_decls apply_blk
    ⊣ Γ <| cnstrs :=
    control_name
      ↦ ControlType
      (map snd cparams) expr_cparams (map snd extern_params) params ,, cnstrs Γ |>
| type_parser
    parser_decl_name cparams expr_cparams extern_params params
    start_state states insts :
  (* TODO: check params are [t_ok []] *)
  (* TODO: add extern runtime params
     to instance envrionment when checking control body. *)
  insts = cbind_all (insts_env Γ) cparams ->
  Forall
    (fun state =>
       `⧼ 0, bind_all params expr_cparams, tfuncts Γ,
           CParserState (List.length states) insts ⧽ ⊢ state ⊣ Trans)
    (start_state :: states) ->
  Γ ⊢ₜ TopDecl.Parser
    parser_decl_name cparams expr_cparams extern_params params
    start_state states
    ⊣ Γ <| cnstrs :=
            parser_decl_name
              ↦ ParserType
              (map snd cparams) expr_cparams
              (map snd extern_params) params ,, cnstrs Γ |>
| type_extern
    extern_name type_params cparams expr_cparams methods :
  (* TODO: check types as [t_ok] *)
  Γ ⊢ₜ TopDecl.Extern extern_name type_params cparams expr_cparams methods
    ⊣ Γ <| cnstrs :=
              extern_name
                ↦ ExternType
                type_params (map snd cparams)
                expr_cparams extern_name ,, cnstrs Γ |>
| type_function function_name type_params arrow body sig :
  good_signal arrow sig ->
  `⧼ type_params, bind_all (paramargs arrow) [], tfuncts Γ,
      CFunction (rtrns arrow) ⧽ ⊢ body ⊣ sig ->
  Γ ⊢ₜ TopDecl.Funct
    function_name type_params arrow body
    ⊣ Γ <| tfuncts := function_name ↦ (type_params,arrow) ,, tfuncts Γ |>
where
"Γ₁ '⊢ₜ' d ⊣ Γ₂"
  := (type_topdecl Γ₁ d Γ₂).

Local Close Scope climate_scope.

Definition type_prog
  : TopDecl.prog -> top_type_env -> top_type_env -> Prop :=
  FoldLeft (fun d Γ Γ' => Γ ⊢ₜ d ⊣ Γ').
