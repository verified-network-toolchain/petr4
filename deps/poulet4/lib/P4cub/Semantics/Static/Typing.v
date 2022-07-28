Require Import Coq.PArith.BinPos Coq.ZArith.BinInt Coq.NArith.BinNat
        Poulet4.P4cub.Syntax.AST Poulet4.Utils.P4Arith
        Poulet4.P4cub.Syntax.CubNotations
        Poulet4.P4cub.Semantics.Static.Util.
From RecordUpdate Require Import RecordSet.
Import String AllCubNotations Clmt.Notations RecordSetNotations.


(** * Expression typing. *)

Record expr_type_env : Set :=
  mk_expr_type_env { type_vars:nat; types:list Expr.t }.

Global Instance eta_expr_type_env : Settable _ :=
  settable! mk_expr_type_env < type_vars ; types >.

Reserved Notation "Γ '⊢ₑ' e ∈ τ" (at level 80, no associativity).

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
| type_slice hi lo e w τ :
  (Npos lo <= Npos hi < w)%N ->
  numeric_width w τ ->
  Γ ⊢ₑ e ∈ τ ->
  Γ ⊢ₑ Expr.Slice hi lo e ∈ Expr.TBit (Npos hi - Npos lo + 1)%N
| type_cast τ τ' e :
  proper_cast τ' τ ->
  t_ok (type_vars Γ) τ ->
  Γ ⊢ₑ e ∈ τ' ->
  Γ ⊢ₑ Expr.Cast τ e ∈ τ
| type_uop op τ τ' e :
  uop_type op τ τ' ->
  t_ok (type_vars Γ) τ' ->
  Γ ⊢ₑ e ∈ τ ->
  Γ ⊢ₑ Expr.Uop τ' op e ∈ τ'
| type_bop op τ₁ τ₂ τ e₁ e₂ :
  bop_type op τ₁ τ₂ τ ->
  t_ok (type_vars Γ) τ ->
  Γ ⊢ₑ e₁ ∈ τ₁ ->
  Γ ⊢ₑ e₂ ∈ τ₂ ->
  Γ ⊢ₑ Expr.Bop τ op e₁ e₂ ∈ τ
| type_index e₁ e₂ n τ :
  Γ ⊢ₑ e₁ ∈ Expr.TArray n τ ->
  Γ ⊢ₑ e₂ ∈ Expr.TBit n ->
  Γ ⊢ₑ Expr.Index τ e₁ e₂ ∈ τ
| type_member τ x e τs b :
  nth_error τs x = Some τ ->
  t_ok (type_vars Γ) τ ->
  Γ ⊢ₑ e ∈ Expr.TStruct b τs ->
  Γ ⊢ₑ Expr.Member τ x e ∈ τ
| type_lists ls es τ τs :
  type_lists_ok ls τ τs ->
  Forall2 (type_expr Γ) es τs ->
  Γ ⊢ₑ Expr.Lists ls es ∈ τ
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
  type_pat (Parser.Lists ps) (Expr.TStruct false ts).
Local Close Scope pat_scope.

(** Parser-expression typing. *)
Variant type_prsrexpr 
        (total_states : nat) (Γ : expr_type_env)
  : Parser.e -> Prop :=
  | type_goto (st : Parser.state_label) :
    valid_state total_states st ->
    type_prsrexpr total_states Γ (Parser.Direct st)
  | type_select e default cases τ :
    valid_state total_states default ->
    Γ ⊢ₑ e ∈ τ ->
    Forall
      (fun '(p,st) => type_pat p τ /\ valid_state total_states st)
      cases ->
    type_prsrexpr total_states Γ (Parser.Select e default cases).

(** * Statement typing. *)

Record stmt_type_env : Set :=
  mk_stmt_type_env
    { sfuncts : fenv
    ; cntx   : ctx
    ; expr_env :> expr_type_env }.

Global Instance eta_stmt_type_env : Settable _ :=
  settable! mk_stmt_type_env < sfuncts ; cntx ; expr_env >.

Reserved Notation "Γ '⊢ₛ' s ⊣ sig" (at level 80, no associativity).

Local Open Scope stmt_scope.

Inductive type_stmt
  : stmt_type_env -> Stmt.s -> signal -> Prop :=
| type_skip Γ :
  Γ ⊢ₛ Stmt.Skip ⊣ Cont
| type_return Γ eo :
  match cntx Γ, eo with
  | CFunction (Some τ), Some e => Γ ⊢ₑ e ∈ τ
  | c, None => return_void_ok c
  | _, _ => False
  end ->
  Γ ⊢ₛ Stmt.Return eo ⊣ Return
| type_exit Γ :
  exit_ctx_ok (cntx Γ) ->
  Γ ⊢ₛ Stmt.Exit ⊣ Return
| type_transition (Γ : stmt_type_env) total_states e :
  transition_ok total_states (cntx Γ) ->
  type_prsrexpr total_states Γ e ->
  Γ ⊢ₛ Stmt.Transition e ⊣ Return
| type_assign (Γ : stmt_type_env) τ e₁ e₂ :
  lvalue_ok e₁ ->
  Γ ⊢ₑ e₁ ∈ τ ->
  Γ ⊢ₑ e₂ ∈ τ ->
  Γ ⊢ₛ e₁ `:= e₂ ⊣ Cont
| type_fun_call Γ params τs args fk :
  match fk with
  | Stmt.Funct f τs' oe
    => τs = τs' /\ predop lvalue_ok oe /\ exists ot,
        sfuncts Γ f = Some (List.length τs, {|paramargs:=params; rtrns:=ot|})
        /\ predop (t_ok (type_vars Γ)) ot      
        /\ relop (type_expr Γ) oe ot
  | Stmt.Action a cargs
    => τs = [] /\ exists aa cparams,
        action_call_ok aa (cntx Γ) 
        /\ aa a = Some (cparams,params)
        /\ Forall2 (type_expr Γ) cargs cparams
  | Stmt.Method ei m τs' oe
    => τs = τs' /\ predop lvalue_ok oe /\ exists extern_insts methods,
        extern_call_ok extern_insts (cntx Γ)
        /\ extern_insts ei = Some (inl methods) /\ exists ot,
          Field.get m methods = Some (List.length τs, {|paramargs:=params; rtrns:=ot|})
          /\ predop (t_ok (type_vars Γ)) ot
          /\ relop (type_expr Γ) oe ot
  end ->  
  Forall (t_ok (type_vars Γ)) τs ->
  Forall2
    (rel_paramarg
       (type_expr Γ)
       (fun e τ => Γ ⊢ₑ e ∈ τ /\ lvalue_ok e))
    args (map (tsub_param (gen_tsub τs)) params) ->
  Γ ⊢ₛ Stmt.Call fk args ⊣ Cont
| type_apply
    Γ extern_args args x extern_params params sig insts :
  apply_instance_ok insts sig (cntx Γ) ->
  insts x = Some (inr (sig,extern_params,params)) ->
  Forall2
    (fun extern_instance extern_type
     => True (* TODO: checking types of extern instances.*))
    extern_args extern_params ->
  Forall2
    (rel_paramarg
       (type_expr Γ)
       (fun e τ => Γ ⊢ₑ e ∈ τ /\ lvalue_ok e))
    args params ->
  Γ ⊢ₛ Stmt.Apply x extern_args args ⊣ Cont
| type_invoke
    Γ tbl es tbls τs :
  table_invoke_ok tbls (cntx Γ) ->
  tbls tbl = Some τs ->
  Forall2 (type_expr Γ) es τs ->
  Γ ⊢ₛ Stmt.Invoke tbl es ⊣ Cont
| type_vardecl (Γ : stmt_type_env) τ te s sig :
    match te with
    | inr e => Γ ⊢ₑ e ∈ τ
    | inl τ' => τ' = τ /\ t_ok (type_vars Γ) τ'
    end ->
    (Γ <| expr_env :=
       Γ.(expr_env)
           <| types :=
         τ :: Γ.(types) |> |>) ⊢ₛ s ⊣ sig ->
    Γ ⊢ₛ Stmt.Var te s ⊣ sig
| type_seq Γ s₁ s₂ sig₁ sig₂ :
  Γ ⊢ₛ s₁ ⊣ sig₁ ->
  Γ ⊢ₛ s₂ ⊣ sig₂ ->
  Γ ⊢ₛ s₁ `; s₂ ⊣ sig₂
| type_cond (Γ : stmt_type_env) e s₁ s₂ sig₁ sig₂ :
  Γ ⊢ₑ e ∈ Expr.TBool ->
  Γ ⊢ₛ s₁ ⊣ sig₁ ->
  Γ ⊢ₛ s₂ ⊣ sig₂ ->
  Γ ⊢ₛ If e Then s₁ Else s₂ ⊣ lub sig₁ sig₂
where "Γ '⊢ₛ' s ⊣ sig" := (type_stmt Γ s sig).

Local Close Scope stmt_scope.

(** * Control-declaration typing. *)

(** Control-declaration typing context. *)
Record ctrl_type_env : Set :=
  mk_ctrl_type_env
    { cexpr_env : expr_type_env
    ; cfuncts : fenv (** available functions. *)
    ; cinsts : ienv  (** available control instances. *)
    ; actns : aenv   (** available action signatures. *)
    ; tbls : tbl_env (** available table names. *) }.

Global Instance eta_ctrl_type_env : Settable _ :=
  settable! mk_ctrl_type_env
  < cexpr_env ; cfuncts ; cinsts ; actns ; tbls >.

Reserved Notation "Γ '⊢ᵪ' d '⊣' result"
         (at level 80, no associativity).

(** Control declaration typing,
    Producing either a new action or table. *)
Variant type_ctrldecl (Γ : ctrl_type_env)
  : Control.d ->
    (string * (list Expr.t * Expr.params))
    + (string * list Expr.t) -> Prop :=
  | type_action action_name cparams dparams body sig :
    {| sfuncts := cfuncts Γ
    ; cntx     := CAction (actns Γ) (cinsts Γ)
    ; expr_env :=
      {| type_vars := type_vars (cexpr_env Γ)
      ; types := cparams ++ bind_all dparams (types (cexpr_env Γ)) |}
    |} ⊢ₛ body ⊣ sig ->
    Γ ⊢ᵪ Control.Action action_name cparams dparams body
      ⊣ inl (action_name,(cparams,dparams))
  | type_table table_name key_sig actions :
    (*
      (** Keys type. *)
      Forall
      (fun '(e,_) => exists τ,
      cexpr_env Γ ⊢ₑ e ∈ τ) key ->
     *)
  (** Actions available *)
    Forall (fun a => exists pms, actns Γ a = Some pms) actions ->
    Γ ⊢ᵪ Control.Table
      table_name key_sig actions ⊣  inr (table_name, map fst key_sig)
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
           | inl (an,cdps) =>
               Γ' = Γ <| actns := an ↦ cdps ,, actns Γ |>
           | inr (tn,key_sig) =>
               Γ' = Γ <| tbls := tn ↦ key_sig ,, tbls Γ |>
           end)
    ctrl
    {| cexpr_env := {|type_vars:=0;types:=bind_all params Γ|}
    ; cfuncts := fs
    ; cinsts := cis
    ; actns := ∅ ; tbls := ∅ |}.

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
    control_decls apply_blk Γₑ Γ' sig insts :
  (* TODO: check params are [t_ok []] *)
  (Γₑ,insts) = cbind_all (insts_envs Γ) cparams ->
  type_ctrl params Γₑ (tfuncts Γ) (controls insts) (externs insts) control_decls Γ' ->
  {| expr_env := {|type_vars:=0;types:=bind_all params Γₑ |}
  ; sfuncts := tfuncts Γ
  ; cntx := CApplyBlock (tbls Γ') (actns Γ') (controls insts) (externs insts) |}
    ⊢ₛ apply_blk ⊣ sig ->
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
    (fun state =>
       {| sfuncts := tfuncts Γ
       ;  cntx := CParserState (parsers insts) (externs insts)
       ;  expr_env := {|type_vars:=0;types:=bind_all params Γₑ|}
       |} ⊢ₛ state ⊣ Return)
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
| type_function function_name type_params arrow body sig :
  good_signal arrow sig ->
  {| sfuncts := tfuncts Γ
  ; cntx := CFunction (rtrns arrow)
  ; expr_env :=
    {| type_vars := type_params
    ; types := bind_all (paramargs arrow) [] |}
  |} ⊢ₛ body ⊣ sig ->
  Γ ⊢ₜ TopDecl.Funct
    function_name type_params arrow body
    ⊣ {| tfuncts := function_name ↦ (type_params,arrow) ,, tfuncts Γ
      ; cnstrs := cnstrs Γ
      ; insts_envs := insts_envs Γ
      ; package_insts := package_insts Γ |}
where
"Γ₁ '⊢ₜ' d ⊣ Γ₂"
  := (type_topdecl Γ₁ d Γ₂).

Local Close Scope climate_scope.

Definition type_prog
  : TopDecl.prog -> top_type_env -> top_type_env -> Prop :=
  FoldLeft (fun d Γ Γ' => Γ ⊢ₜ d ⊣ Γ').
