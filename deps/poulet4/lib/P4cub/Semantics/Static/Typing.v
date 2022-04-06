Require Import Coq.PArith.BinPos Coq.ZArith.BinInt Coq.NArith.BinNat
        Poulet4.P4cub.Syntax.AST Poulet4.Utils.P4Arith
        Poulet4.P4cub.Syntax.CubNotations
        Poulet4.P4cub.Semantics.Static.Util.
Import String.

Import AllCubNotations Clmt.Notations.

(** * Expression typing. *)

Record expr_type_env : Set := { type_vars:nat; types:list Expr.t }.

Reserved Notation "Γ '⊢ₑ' e ∈ t" (at level 80, no associativity).

Local Open Scope ty_scope.
Local Open Scope expr_scope.

Inductive type_expr (Γ : expr_type_env)
  : Expr.e -> Expr.t -> Prop :=
| type_bool (b : bool) :
  Γ ⊢ₑ b ∈ Expr.TBool
| type_bit w n :
  BitArith.bound w n ->
  Γ ⊢ₑ w `W n ∈ Expr.TBit w
| type_int w n :
  IntArith.bound w n ->
  Γ ⊢ₑ w `S n ∈ Expr.TInt w
| type_var x τ :
  nth_error (types Γ) x = Some τ ->
  t_ok (type_vars Γ) τ ->
  Γ ⊢ₑ Expr.Var τ x ∈ τ
| type_slice e hi lo w τ :
  (Npos lo <= Npos hi < w)%N ->
  numeric_width w τ ->
  Γ ⊢ₑ e ∈ τ ->
  Γ ⊢ₑ Expr.Slice e hi lo ∈ Expr.TBit (Npos hi - Npos lo + 1)%N
| type_cast τ τ' e :
  proper_cast τ' τ ->
  t_ok (type_vars Γ) τ' ->
  t_ok (type_vars Γ) τ ->
  Γ ⊢ₑ e ∈ τ' ->
  Γ ⊢ₑ Expr.Cast τ e ∈ τ
| type_uop op τ τ' e :
  uop_type op τ τ' ->
  Γ ⊢ₑ e ∈ τ ->
  Γ ⊢ₑ Expr.Uop τ' op e ∈ τ'
| type_bop op τ₁ τ₂ τ e₁ e₂ :
  bop_type op τ₁ τ₂ τ ->
  Γ ⊢ₑ e₁ ∈ τ₁ ->
  Γ ⊢ₑ e₂ ∈ τ₂ ->
  Γ ⊢ₑ Expr.Bop τ op e₁ e₂ ∈ τ
| type_member τ x e τs b :
  nth_error τs x = Some τ ->
  t_ok (type_vars Γ) τ ->
  Γ ⊢ₑ e ∈ Expr.TStruct τs b ->
  Γ ⊢ₑ Expr.Member τ x e ∈ τ
| type_struct es oe τs (b : bool) :
  relop (type_expr Γ) oe (if b then Some Expr.TBool else None) ->
  Forall2 (type_expr Γ) es τs ->
  Γ ⊢ₑ Expr.Struct es oe ∈ Expr.TStruct τs b
| type_error err :
  Γ ⊢ₑ Expr.Error err ∈ Expr.TError
where "Γ '⊢ₑ' e ∈ τ" := (type_expr Γ e τ) : type_scope.

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
  type_pat (Parser.Struct ps) (Expr.TStruct ts false).
Local Close Scope pat_scope.

(** Parser-expression typing. *)
Variant type_prsrexpr 
        (total_states : nat) (Γ : expr_type_env)
  : Parser.e -> Prop :=
  | type_goto (st : Parser.state) :
    valid_state total_states st ->
    type_prsrexpr total_states Γ (Parser.Goto st)
  | type_select e default cases τ :
    valid_state total_states default ->
    Γ ⊢ₑ e ∈ τ ->
    Forall
      (fun '(p,st) => type_pat p τ /\ valid_state total_states st)
      cases ->
    type_prsrexpr total_states Γ (Parser.Select e default cases).

(** * Statement typing. *)

Record stmt_type_env : Set :=
  { sfuncts : fenv
  ; cntx   : ctx
  ; expr_env :> expr_type_env }.

Reserved Notation "Γ₁ ⊢ₛ s ⊣ Γ₂ ↓ sig" (at level 80, no associativity).

Local Open Scope stmt_scope.

Inductive type_stmt
  : stmt_type_env -> Stmt.s -> list Expr.t -> signal -> Prop :=
| type_skip Γ :
  Γ ⊢ₛ Stmt.Skip ⊣ types Γ ↓ Cont
| type_seq_cont s₁ s₂ Δ Γ Γ' Γ'' sig con fns :
  {|sfuncts:=fns;cntx:=con;expr_env:={|type_vars:=Δ;types:=Γ|}|}
    ⊢ₛ s₁ ⊣ Γ' ↓ Cont ->
  {|sfuncts:=fns;cntx:=con;expr_env:={|type_vars:=Δ;types:=Γ'|}|}
    ⊢ₛ s₂ ⊣ Γ'' ↓ sig ->
  {|sfuncts:=fns;cntx:=con;expr_env:={|type_vars:=Δ;types:=Γ|}|}
    ⊢ₛ s₁ `; s₂ ⊣ Γ'' ↓ sig
| type_block s Γ Γ' sig :
  Γ ⊢ₛ s ⊣ Γ' ↓ sig ->
  Γ ⊢ₛ Stmt.Block s ⊣ types Γ ↓ Cont
| type_vardecl Δ Γ con fns τ eo :
    match eo with
    | inr e => Γ ⊢ₑ e ∈ τ
    | inl τ => t_ok Δ τ
    end ->
    {| sfuncts := fns
    ; cntx := con
    ; expr_env :=
      {| type_vars := Δ
      ; types := types Γ|}
    |} ⊢ₛ Stmt.Var eo
       ⊣ τ :: types Γ ↓ Cont
| type_assign (Γ : stmt_type_env) τ e₁ e₂ :
  lvalue_ok e₁ ->
  Γ ⊢ₑ e₁ ∈ τ ->
  Γ ⊢ₑ e₂ ∈ τ ->
  Γ ⊢ₛ e₁ `:= e₂ ⊣ types Γ ↓ Cont
| type_cond Δ Γ Γ₁ Γ₂ e s₁ s₂  sig₁ sig₂ con fns :
  {|type_vars:=Δ;types:=Γ|} ⊢ₑ e ∈ Expr.TBool ->
  {|sfuncts:=fns;cntx:=con;expr_env:={|type_vars:=Δ;types:=Γ|}|}
    ⊢ₛ s₁ ⊣ Γ₁ ↓ sig₁ ->
  {|sfuncts:=fns;cntx:=con;expr_env:={|type_vars:=Δ;types:=Γ|}|}
    ⊢ₛ s₂ ⊣ Γ₂ ↓ sig₂ ->
  {|sfuncts:=fns;cntx:=con;expr_env:={|type_vars:=Δ;types:=Γ|}|}
    ⊢ₛ If e Then s₁ Else s₂ ⊣ Γ ↓ lub sig₁ sig₂
| type_return Γ eo :
  match cntx Γ, eo with
  | CFunction (Some τ), Some e => Γ ⊢ₑ e ∈ τ
  | c, None => return_void_ok c
  | _, _ => False
  end ->
  Γ ⊢ₛ Stmt.Return eo ⊣ types Γ ↓ Return
| type_exit Γ :
  exit_ctx_ok (cntx Γ) ->
  Γ ⊢ₛ Stmt.Exit ⊣ types Γ ↓ Return
| type_void_call Γ params τs args f :
  sfuncts Γ f = Some (List.length τs, {|paramargs:=params; rtrns:=None|}) ->
  Forall (t_ok (type_vars Γ)) τs ->
  Forall2
    (rel_paramarg
       (type_expr Γ)
       (fun e τ => Γ ⊢ₑ e ∈ τ /\ lvalue_ok e))
    args (map (tsub_param (gen_tsub τs)) params) ->
  Γ ⊢ₛ Stmt.FunCall f τs {|paramargs:=args;rtrns:=None|} ⊣ types Γ ↓ Cont
| type_act_call Γ cparams dparams cargs dargs a aa :
  action_call_ok aa (cntx Γ) ->
  aa a = Some (cparams,dparams) ->
  Forall2 (type_expr Γ) cargs cparams ->
  Forall2
    (rel_paramarg
       (type_expr Γ)
       (fun e τ => Γ ⊢ₑ e ∈ τ /\ lvalue_ok e))
    dargs dparams ->
  Γ ⊢ₛ Stmt.ActCall a cargs dargs ⊣ types Γ ↓ Cont
| type_fun_call Γ params τs args f τ e :
  sfuncts Γ f = Some (List.length τs, {|paramargs:=params; rtrns:=Some τ|}) ->
  Forall (t_ok (type_vars Γ)) (τ :: τs) ->
  lvalue_ok e ->
  Γ ⊢ₑ e ∈ tsub_t (gen_tsub τs) τ ->
  Forall2
    (rel_paramarg
       (type_expr Γ)
       (fun e τ => Γ ⊢ₑ e ∈ τ /\ lvalue_ok e))
    args (map (tsub_param (gen_tsub τs)) params) ->
  Γ ⊢ₛ Stmt.FunCall f τs {|paramargs:=args;rtrns:=Some e|} ⊣ types Γ ↓ Cont
| type_apply_control
    Γ fns extern_args args x extern_params params
    tbls actions control_insts extern_insts :
  nth_error control_insts x = Some (extern_params,params) ->
  Forall2
    (fun extern_instance extern_type
     => True (* TODO: checking types of extern instances.*))
    extern_args extern_params ->
  Forall2
    (rel_paramarg
       (type_expr Γ)
       (fun e τ => Γ ⊢ₑ e ∈ τ /\ lvalue_ok e))
    args params ->
  {| expr_env := Γ
  ; sfuncts :=fns
  ; cntx := CApplyBlock
              tbls actions control_insts extern_insts |}
    ⊢ₛ Stmt.Apply x extern_args args ⊣ types Γ ↓ Cont
| type_apply_parser
    Γ fns extern_args args x extern_params params
    parser_insts extern_insts :
  nth_error parser_insts x = Some (extern_params,params) ->
  Forall2
    (fun extern_instance extern_type
     => True (* TODO: checking types of extern instances.*))
    extern_args extern_params ->
  Forall2
    (rel_paramarg
       (type_expr Γ)
       (fun e τ => Γ ⊢ₑ e ∈ τ /\ lvalue_ok e))
    args params ->
  {| expr_env := Γ
  ; sfuncts :=fns
  ; cntx := CParserState
              parser_insts extern_insts |}
    ⊢ₛ Stmt.Apply x extern_args args ⊣ types Γ ↓ Cont
| type_invoke
    Γ fns tbl tbls actions
    control_insts extern_insts :
  In tbl tbls ->
  {| expr_env := Γ
  ; sfuncts :=fns
  ; cntx := CApplyBlock
              tbls actions control_insts extern_insts |}
    ⊢ₛ Stmt.Invoke tbl ⊣ types Γ ↓ Cont
| type_method_call_void
    Γ x f τs args fns con
    methods extern_insts params :
  nth_error extern_insts x = Some methods ->
  Field.get f methods = Some (List.length τs, {|paramargs:=params; rtrns:=None|}) ->
  extern_call_ok extern_insts con ->
  Forall (t_ok (type_vars Γ)) τs ->
  Forall2
    (rel_paramarg
       (type_expr Γ)
       (fun e τ => Γ ⊢ₑ e ∈ τ /\ lvalue_ok e))
    args (map (tsub_param (gen_tsub τs)) params) ->
  {|sfuncts:=fns;cntx:=con;expr_env:=Γ|}
    ⊢ₛ Stmt.MethodCall x f τs {|paramargs:=args;rtrns:=None|} ⊣ types Γ ↓ Cont
| type_method_call_fruit
    Γ x f τs args e τ fns con
    methods extern_insts params :
  nth_error extern_insts x = Some methods ->
  Field.get f methods = Some (List.length τs, {|paramargs:=params; rtrns:=Some τ|}) ->
  extern_call_ok extern_insts con ->
  Forall (t_ok (type_vars Γ)) (τ :: τs) ->
  lvalue_ok e ->
  Γ ⊢ₑ e ∈ tsub_t (gen_tsub τs) τ ->
  Forall2
    (rel_paramarg
       (type_expr Γ)
       (fun e τ => Γ ⊢ₑ e ∈ τ /\ lvalue_ok e))
    args (map (tsub_param (gen_tsub τs)) params) ->
  {|sfuncts:=fns;cntx:=con;expr_env:=Γ|}
    ⊢ₛ Stmt.MethodCall x f τs {|paramargs:=args;rtrns:=Some e|} ⊣ types Γ ↓ Cont
where "Γ₁ '⊢ₛ' s '⊣' Γ₂ '↓' sig"
        := (type_stmt Γ₁ s Γ₂ sig).

Local Close Scope stmt_scope.

(** Parser State typing. *)
Definition type_parser_state
           (fns : fenv) (parser_insts : ienv)
           (extern_insts : eienv) (total_states : nat)
           (Γ : expr_type_env)
          '({|Parser.stmt:=s; Parser.trans:=e|} : Parser.state_block) : Prop :=
  exists (Γ' : expr_type_env) (sig : signal),
    {| sfuncts := fns
    ; cntx := CParserState parser_insts extern_insts
    ; expr_env := Γ|}
      ⊢ₛ s ⊣ types Γ' ↓ sig /\ type_prsrexpr total_states Γ' e.

(** * Control-declaration typing. *)

(** Control-declaration typing context. *)
Record ctrl_type_env : Set :=
  { cexpr_env : expr_type_env
  ; cfuncts : fenv       (** available functions. *)
  ; ccntrl_insts : ienv  (** available control instances. *)
  ; cextrn_insts : eienv (** available extern instances. *)
  ; actns : aenv         (** available action signatures. *)
  ; tbls : list string   (** available table names. *) }.

Reserved Notation "Γ '⊢ᵪ' d '⊣' acts '∧' tbs"
         (at level 80, no associativity).

Local Open Scope ctrl_scope.

(** Control declaration typing. *)
Inductive type_ctrldecl (Γ : ctrl_type_env)
  : Control.d -> aenv -> list string -> Prop :=
| type_action action_name cparams dparams body Γ' sig :
  {| sfuncts := cfuncts Γ
  ; cntx     := CAction (actns Γ) (cextrn_insts Γ)
  ; expr_env :=
    {| type_vars := type_vars (cexpr_env Γ)
    ; types := cparams ++ bind_all dparams (types (cexpr_env Γ)) |}
  |} ⊢ₛ body ⊣ Γ' ↓ sig ->
  Γ ⊢ᵪ Control.Action action_name cparams dparams body ⊣ actns Γ ∧ tbls Γ
| type_table table_name key actions :
  (** Keys type. *)
  Forall
    (fun '(e,_) => exists τ,
         cexpr_env Γ ⊢ₑ e ∈ τ) key ->
  (** Actions available *)
  Forall (fun a => exists pms, actns Γ a = Some pms) actions ->
  Γ ⊢ᵪ Control.Table
    table_name {| Control.table_key:=key
               ; Control.table_actions:=actions
               |} ⊣  actns Γ ∧ table_name :: tbls Γ
| type_ctrldecl_seq d₁ d₂ actions' actions'' tbls' tbls'' :
  Γ ⊢ᵪ d₁ ⊣ actions' ∧ tbls' ->
  {| cexpr_env := cexpr_env Γ
  ; cfuncts := cfuncts Γ
  ; ccntrl_insts := ccntrl_insts Γ
  ; cextrn_insts := cextrn_insts Γ
  ; actns := actions'
  ; tbls := tbls'
  |} ⊢ᵪ d₂ ⊣ actions'' ∧ tbls'' ->
  Γ ⊢ᵪ d₁ ;c; d₂ ⊣ actions'' ∧ tbls''
where "Γ '⊢ᵪ' d '⊣' acts '∧' tbs"
  := (type_ctrldecl Γ d acts tbs) : type_scope.

Local Close Scope ctrl_scope.

(** * Toplevel-declaration typing. *)

Record top_type_env : Set :=
  { tfuncts : fenv (** available function signatures. *)
  ; cnstrs : constructor_env (** available constructors. *)
  ; insts_envs
      :> insts_env (** available instances for parsers, controls, externs. *)
  ; package_insts : nat (** De Bruijn counter of package instance names. *) }.

Reserved Notation "Γ₁ '⊢ₜ' d ⊣ Γ₂"
         (at level 80, no associativity).

Local Open Scope top_scope.
Local Open Scope climate_scope.

(** Top-level declaration typing. *)
Inductive type_topdecl (Γ : top_type_env)
  : TopDecl.d -> top_type_env -> Prop :=
| type_instantiate_control
    control_decl_name cparams cargs extern_params params :
  cnstrs Γ control_decl_name =
    Some (ControlType cparams extern_params params) ->
  Forall2
    (fun carg cparam =>
       match carg, cparam with
       | TopDecl.CAExpr e, TopDecl.EType τ
         => {|type_vars:=0;types:=[]|} ⊢ₑ e ∈ τ
       | TopDecl.CAName ctrl, TopDecl.ControlInstType eps ps
         => nth_error (controls (insts_envs Γ)) ctrl = Some (eps,ps)
       | TopDecl.CAName extn, TopDecl.ExternInstType extern_type
         => (* TODO:
              How to represent extern types?
              [nth_error (externs (insts_envs Γ)) extn = extern_type] *)
           False
       | _, _ => False
       end) cargs cparams ->
  Γ ⊢ₜTopDecl.Instantiate control_decl_name [] cargs
    ⊣ {| tfuncts := tfuncts Γ
      ; cnstrs := cnstrs Γ
      ; insts_envs :=
        {| parsers := parsers (insts_envs Γ)
        ; controls := (extern_params,params) :: controls (insts_envs Γ)
        ; externs := externs (insts_envs Γ) |}
      ; package_insts := package_insts Γ |}
| type_instantiate_parser
    parser_decl_name cparams cargs extern_params params :
  cnstrs Γ parser_decl_name =
    Some (ParserType cparams extern_params params) ->
  Forall2
    (fun carg cparam =>
       match carg, cparam with
       | TopDecl.CAExpr e, TopDecl.EType τ
         => {|type_vars:=0;types:=[]|} ⊢ₑ e ∈ τ
       | TopDecl.CAName prsr, TopDecl.ParserInstType eps ps
         => nth_error (parsers (insts_envs Γ)) prsr = Some (eps,ps)
       | TopDecl.CAName extn, TopDecl.ExternInstType extern_type
         => (* TODO:
              How to represent extern types?
              [nth_error (externs (insts_envs Γ)) extn = extern_type] *)
           False
       | _, _ => False
       end) cargs cparams ->
  Γ ⊢ₜTopDecl.Instantiate parser_decl_name [] cargs
    ⊣ {| tfuncts := tfuncts Γ
      ; cnstrs := cnstrs Γ
      ; insts_envs :=
        {| controls := controls (insts_envs Γ)
        ; parsers := (extern_params,params) :: parsers (insts_envs Γ)
        ; externs := externs (insts_envs Γ) |}
      ; package_insts := package_insts Γ |}
| type_instantiate_package
    package_decl_name cparams cargs :
  cnstrs Γ package_decl_name = Some (PackageType cparams) ->
  Forall2
    (fun carg cparam =>
       match carg, cparam with
       | TopDecl.CAExpr e, TopDecl.EType τ
         => {|type_vars:=0;types:=[]|} ⊢ₑ e ∈ τ
       | TopDecl.CAName prsr, TopDecl.ParserInstType eps ps
         => nth_error (parsers (insts_envs Γ)) prsr = Some (eps,ps)
       | TopDecl.CAName ctrl, TopDecl.ControlInstType eps ps
         => nth_error (controls (insts_envs Γ)) ctrl = Some (eps,ps)
       | TopDecl.CAName pkge, TopDecl.PackageInstType => True
       | TopDecl.CAName extn, TopDecl.ExternInstType extern_type
         => (* TODO:
              How to represent extern types?
              [nth_error (externs (insts_envs Γ)) extn = extern_type] *)
           False
       | _, _ => False
       end) cargs cparams ->
  Γ ⊢ₜTopDecl.Instantiate package_decl_name [] cargs
    ⊣ {| tfuncts := tfuncts Γ
      ; cnstrs := cnstrs Γ
      ; insts_envs := insts_envs Γ
      ; package_insts := S (package_insts Γ) |}
| type_instantiate_extern
    (* TODO: How to represent extern types & type instantiations? *)
    extern_decl_name extern_name cparams τs cargs methods :
  Forall (t_ok 0) τs ->
  cnstrs Γ extern_decl_name =
    Some (ExternType (List.length τs) cparams extern_name) ->
  Forall2
    (fun carg cparam =>
       match carg, cparam with
       | TopDecl.CAExpr e, TopDecl.EType τ
         => {|type_vars:=0;types:=[]|} ⊢ₑ e ∈ τ
       | TopDecl.CAName extn, TopDecl.ExternInstType extern_type
         => (* TODO:
              How to represent extern types?
              [nth_error (externs (insts_envs Γ)) extn = extern_type] *)
           False
       | _, _ => False
       end)
    cargs (map (tsub_cparam (gen_tsub τs)) cparams) ->
  Γ ⊢ₜ TopDecl.Instantiate extern_decl_name τs cargs
    ⊣ {| tfuncts := tfuncts Γ
      ; cnstrs := cnstrs Γ
      ; insts_envs :=
        {| controls := controls (insts_envs Γ)
        ; parsers := parsers (insts_envs Γ)
        ; externs := methods :: externs (insts_envs Γ) |}
      ; package_insts := package_insts Γ |}
| type_control
    control_name cparams extern_params params
    control_decls apply_blk tables actions Γₑ Γ' sig insts :
  (* TODO: check params are [t_ok []] *)
  (Γₑ,insts) = cbind_all (insts_envs Γ) cparams ->
  {| cexpr_env := {|type_vars:=0;types:=bind_all params Γₑ|}
  ; cfuncts := tfuncts Γ
  ; ccntrl_insts := controls insts
  ; cextrn_insts := externs insts
  ; actns := ∅ ; tbls := [] |}
    ⊢ᵪ control_decls ⊣ actions ∧ tables ->
  {| expr_env := {|type_vars:=0;types:=bind_all params Γₑ|}
  ; sfuncts := tfuncts Γ
  ; cntx := CApplyBlock tables actions (controls insts) (externs insts) |}
    ⊢ₛ apply_blk ⊣ Γ' ↓ sig ->
  Γ ⊢ₜ
    TopDecl.Control
    control_name cparams extern_params
    params control_decls apply_blk
    ⊣ {| tfuncts := tfuncts Γ
      ; cnstrs :=
        control_name ↦ ControlType cparams extern_params params ,, cnstrs Γ
      ; insts_envs := insts_envs Γ
      ; package_insts := package_insts Γ |}
| type_parser
    parser_decl_name cparams extern_params params
    start_state states Γₑ insts :
  (* TODO: check params are [t_ok []] *)
  (Γₑ,insts) = cbind_all (insts_envs Γ) cparams ->
  Forall
    (type_parser_state
       (tfuncts Γ) (parsers insts)
       (externs insts) (List.length states)
       {|type_vars:=0;types:=bind_all params Γₑ|})
    (start_state :: states) ->
  Γ ⊢ₜ TopDecl.Parser
    parser_decl_name cparams extern_params params
    start_state states
    ⊣ {| tfuncts := tfuncts Γ
      ; cnstrs :=
        parser_decl_name ↦ ParserType cparams extern_params params ,, cnstrs Γ
      ; insts_envs := insts_envs Γ
      ; package_insts := package_insts Γ |}
| type_extern
    extern_name type_params cparams methods :
  (* TODO: check types as [t_ok] *)
  Γ ⊢ₜ TopDecl.Extern extern_name type_params cparams methods
    ⊣ {| tfuncts := tfuncts Γ
      ; cnstrs :=
        extern_name ↦ ExternType type_params cparams extern_name ,, cnstrs Γ
      ; insts_envs := insts_envs Γ
      ; package_insts := package_insts Γ |}
| type_function function_name type_params arrow body Γ' sig :
  good_signal arrow sig ->
  {| sfuncts := tfuncts Γ
  ; cntx := CFunction (rtrns arrow)
  ; expr_env :=
    {| type_vars := type_params
    ; types := bind_all (paramargs arrow) [] |}
  |} ⊢ₛ body ⊣ Γ' ↓ sig ->
  Γ ⊢ₜ TopDecl.Funct
    function_name type_params arrow body
    ⊣ {| tfuncts := function_name ↦ (type_params,arrow) ,, tfuncts Γ
      ; cnstrs := cnstrs Γ
      ; insts_envs := insts_envs Γ
      ; package_insts := package_insts Γ |}
| type_topdecl_seq
    d₁ d₂ insts' insts''
    package_insts' package_insts''
    fns' fns'' cnstrs' cnstrs'' :
  Γ ⊢ₜ d₁
    ⊣ {| tfuncts := fns'
      ; cnstrs := cnstrs'
      ; insts_envs := insts'
      ; package_insts := package_insts' |} ->
  {| tfuncts := fns'
  ; cnstrs := cnstrs'
  ; insts_envs := insts'
  ; package_insts := package_insts' |}
    ⊢ₜ d₂
    ⊣ {| tfuncts := fns''
      ; cnstrs := cnstrs''
      ; insts_envs := insts''
      ; package_insts := package_insts' |} ->
  Γ ⊢ₜ d₁ ;%; d₂
    ⊣ {| tfuncts := fns''
      ; cnstrs := cnstrs''
      ; insts_envs := insts''
      ; package_insts := package_insts'' |}
where
"Γ₁ '⊢ₜ' d ⊣ Γ₂"
  := (type_topdecl Γ₁ d Γ₂).

Local Close Scope top_scope.
Local Close Scope climate_scope.
