Require Import Coq.PArith.BinPos Coq.ZArith.BinInt Coq.NArith.BinNat
        Poulet4.P4cub.Syntax.AST Poulet4.Utils.P4Arith
        Poulet4.P4cub.Syntax.CubNotations
        Poulet4.P4cub.Semantics.Static.Util.
From RecordUpdate Require Import RecordSet.
Import Clmt.Notations RecordSetNotations.

(** * Expression typing. *)

Reserved Notation "'`⟨' Δ , Γ ⟩ ⊢ e ∈ τ" (at level 80, no associativity).

Local Open Scope typ_scope.
Local Open Scope exp_scope.

Inductive type_exp (Δ : nat) (Γ : list Typ.t)
  : Exp.t -> Typ.t -> Prop :=
| type_bool (b : bool) :
  `⟨ Δ, Γ ⟩ ⊢ Exp.Bool b ∈ Typ.Bool
| type_bit w n :
  BitArith.bound w n ->
  `⟨ Δ, Γ ⟩ ⊢ w `W n ∈ Typ.Bit w
| type_int w n :
  IntArith.bound w n ->
  `⟨ Δ, Γ ⟩ ⊢ w `S n ∈ Typ.Int w
| type_varbit m w n :
  (w <= m)%N ->
  BitArith.bound w n ->
  `⟨ Δ, Γ ⟩ ⊢ Exp.VarBit m w n ∈ Typ.VarBit m
| type_var τ og x :
  nth_error Γ x = Some τ ->
  typ_ok Δ τ ->
  `⟨ Δ, Γ ⟩ ⊢ Exp.Var τ og x ∈ τ
| type_slice hi lo e w τ :
  (Npos lo <= Npos hi < w)%N ->
  numeric_width w τ ->
  `⟨ Δ, Γ ⟩ ⊢ e ∈ τ ->
  `⟨ Δ, Γ ⟩ ⊢ Exp.Slice hi lo e ∈ Typ.Bit (Npos hi - Npos lo + 1)%N
| type_cast τ τ' e :
  proper_cast τ' τ ->
  typ_ok Δ τ ->
  `⟨ Δ, Γ ⟩ ⊢ e ∈ τ' ->
  `⟨ Δ, Γ ⟩ ⊢ Exp.Cast τ e ∈ τ
| type_uop op τ τ' e :
  una_type op τ τ' ->
  typ_ok Δ τ' ->
  `⟨ Δ, Γ ⟩ ⊢ e ∈ τ ->
  `⟨ Δ, Γ ⟩ ⊢ Exp.Uop τ' op e ∈ τ'
| type_bop op τ₁ τ₂ τ e₁ e₂ :
  bin_type op τ₁ τ₂ τ ->
  typ_ok Δ τ ->
  `⟨ Δ, Γ ⟩ ⊢ e₁ ∈ τ₁ ->
  `⟨ Δ, Γ ⟩ ⊢ e₂ ∈ τ₂ ->
  `⟨ Δ, Γ ⟩ ⊢ Exp.Bop τ op e₁ e₂ ∈ τ
| type_index e₁ e₂ w τ :
  typ_ok Δ τ ->
  `⟨ Δ, Γ ⟩ ⊢ e₁ ∈ Typ.Array (Z.to_N (BitArith.upper_bound w)) τ ->
  `⟨ Δ, Γ ⟩ ⊢ e₂ ∈ Typ.Bit w ->
  `⟨ Δ, Γ ⟩ ⊢ Exp.Index τ e₁ e₂ ∈ τ
| type_member τ x e τs b :
  nth_error τs x = Some τ ->
  typ_ok Δ τ ->
  `⟨ Δ, Γ ⟩ ⊢ e ∈ Typ.Struct b τs ->
  `⟨ Δ, Γ ⟩ ⊢ Exp.Member τ x e ∈ τ
| type_lists ls es τ τs :
  typ_ok_lists Δ ls ->
  type_lst_ok ls τ τs ->
  Forall2 (type_exp Δ Γ) es τs ->
  `⟨ Δ, Γ ⟩ ⊢ Exp.Lists ls es ∈ τ
| type_error err :
  `⟨ Δ, Γ ⟩ ⊢ Exp.Error err ∈ Typ.Error
where "'`⟨' Δ , Γ ⟩ ⊢ e ∈ τ" := (type_exp Δ Γ e τ) : type_scope.

Local Close Scope exp_scope.
Local Open Scope pat_scope.

(** Select-pattern-typing. *)
Inductive type_pat : Pat.t -> Typ.t -> Prop :=
| type_wild t : type_pat Pat.Wild t
| type_mask p₁ p₂ w :
  type_pat p₁ (Typ.Bit w) ->
  type_pat p₂ (Typ.Bit w) ->
  type_pat (Pat.Mask p₁ p₂) (Typ.Bit w)
| type_range p₁ p₂ w :
  type_pat p₁ (Typ.Bit w) ->
  type_pat p₂ (Typ.Bit w) ->
  type_pat (Pat.Range p₁ p₂) (Typ.Bit w)
| type_pbit w n :
  type_pat (w PW n) (Typ.Bit w)
| type_pint w z :
  type_pat (w PS z) (Typ.Int w)
| type_pstruct ps ts :
  Forall2 type_pat ps ts ->
  type_pat (Pat.Lists ps) (Typ.Struct false ts).
Local Close Scope pat_scope.

(** Parser-expession typing. *)
Variant type_trns 
        (total_states : nat) (Δ : nat) (Γ : list Typ.t)
  : Trns.t -> Prop :=
  | type_goto st :
    valid_state total_states st ->
    type_trns total_states Δ Γ (Trns.Direct st)
  | type_select e default cases τ :
    valid_state total_states default ->
    `⟨ Δ, Γ ⟩ ⊢ e ∈ τ ->
    Forall
      (fun '(p,st) => type_pat p τ /\ valid_state total_states st)
      cases ->
    type_trns total_states Δ Γ (Trns.Select e default cases).

(** * Statement typing. *)
Inductive type_call
  (Δ : nat) (Γ : list Typ.t) (fs : fenv) (c : ctx)
    : Call.t -> list Typ.t -> Typ.params -> Prop :=
| type_call_funct f τs oe params ot :
  fs f = Some (List.length τs, {|paramargs:=params; rtrns:=ot|}) ->
  predop lexpr_ok oe ->
  relop (type_exp Δ Γ) oe (option_map (tsub_typ (gen_tsub τs)) ot) ->
  type_call Δ Γ fs c (Call.Funct f τs oe) τs params
| type_call_action a cargs aa cparams params :
  action_call_ok aa c ->
  aa a = Some (cparams,params) ->
  Forall2 (type_exp Δ Γ) cargs cparams ->
  type_call Δ Γ fs c (Call.Action a cargs) [] params
| type_call_method ei m τs oe params ot extern_insts methods :
  extern_call_ok extern_insts c ->
  extern_insts ei = Some (inl methods) ->
  Field.get m methods = Some (List.length τs, {|paramargs:=params; rtrns:=ot|}) ->
  predop lexpr_ok oe ->
  relop (type_exp Δ Γ) oe (option_map (tsub_typ (gen_tsub τs)) ot) ->
  type_call Δ Γ fs c (Call.Method ei m τs oe) τs params
| type_call_inst x exts insts sig params extern_params :
  apply_instance_ok insts sig c ->
  List.length extern_params = List.length exts ->
  insts x = Some (inr (sig,extern_params,params)) ->
  type_call Δ Γ fs c (Call.Inst x exts) [] params.

Definition type_arg
  (Δ : nat) (Γ : list Typ.t) : Exp.arg -> Typ.param -> Prop :=
  rel_paramarg
    (type_exp Δ Γ)
    (fun e τ => `⟨ Δ, Γ ⟩ ⊢ e ∈ τ /\ lexpr_ok e).

Definition type_args
  (Δ : nat) (Γ : list Typ.t) : Exp.args -> list Typ.param -> Prop :=
  Forall2 (type_arg Δ Γ).

Reserved Notation "'`⧼' Δ , Γ , f , c ⧽ ⊢ s ⊣ sig" (at level 80, no associativity).

Local Open Scope stm_scope.

Inductive type_stm (Δ : nat) (Γ : list Typ.t) (fs : fenv)
  : ctx -> Stm.t -> Signal.t -> Prop :=
| type_skip c :
  `⧼ Δ, Γ, fs, c ⧽ ⊢ Stm.Skip ⊣ Signal.Cnt
| type_ret c eo :
  match c, eo with
  | CFunction (Some τ), Some e => `⟨ Δ, Γ ⟩ ⊢ e ∈ τ
  | c, None => return_void_ok c
  | _, _ => False
  end ->
  `⧼ Δ, Γ, fs, c ⧽ ⊢ Stm.Ret eo ⊣ Signal.Ret
| type_exit c :
  exit_ctx_ok c ->
  `⧼ Δ, Γ, fs, c ⧽ ⊢ Stm.Exit ⊣ Signal.Ext
| type_trans total_states i e :
  type_trns total_states Δ Γ e ->
  `⧼ Δ, Γ, fs, CParserState total_states i ⧽ ⊢ Stm.Trans e ⊣ Signal.Trns
| type_asgn c τ e₁ e₂ :
  lexpr_ok e₁ ->
  `⟨ Δ, Γ ⟩ ⊢ e₁ ∈ τ ->
  `⟨ Δ, Γ ⟩ ⊢ e₂ ∈ τ ->
  `⧼ Δ, Γ, fs, c ⧽ ⊢ e₁ `:= e₂ ⊣ Signal.Cnt
| type_fun_call c params τs args fk :
  type_call Δ Γ fs c fk τs params ->
  Forall (typ_ok Δ) τs ->
  type_args Δ Γ args (map (tsub_param (gen_tsub τs)) (map snd params)) ->
  `⧼ Δ, Γ, fs, c ⧽ ⊢ Stm.App fk args ⊣ Signal.Cnt
| type_invoke eo tbl tbls aa i n :
  tbls tbl = Some n ->
  predop
    (fun e =>
       `⟨ Δ, Γ ⟩ ⊢
         e ∈ Typ.Struct
         false
         [Typ.Bool; Typ.Bool; Typ.Bit (N.of_nat n)])
    eo ->
  `⧼ Δ, Γ, fs, CApplyBlock tbls aa i ⧽ ⊢ Stm.Invoke eo tbl ⊣ Signal.Cnt
| type_letin c og τ te s sig :
  SumForall
    (fun τ' => τ' = τ /\ typ_ok Δ τ')
    (fun e => `⟨ Δ, Γ ⟩ ⊢ e ∈ τ) te ->
    `⧼ Δ, τ :: Γ, fs, c ⧽ ⊢ s ⊣ sig ->
    `⧼ Δ, Γ, fs, c ⧽ ⊢ `let og := te `in s ⊣ sig
| type_seq c s₁ s₂ sig :
  `⧼ Δ, Γ, fs, c ⧽ ⊢ s₁ ⊣ Signal.Cnt ->
  `⧼ Δ, Γ, fs, c ⧽ ⊢ s₂ ⊣ sig ->
  `⧼ Δ, Γ, fs, c ⧽ ⊢ s₁ `; s₂ ⊣ sig
| type_cond c e s₁ s₂ sig₁ sig₂ sig :
  Signal.lub sig₁ sig₂ = Some sig ->
  `⟨ Δ, Γ ⟩ ⊢ e ∈ Typ.Bool ->
  `⧼ Δ, Γ, fs, c ⧽ ⊢ s₁ ⊣ sig₁ ->
  `⧼ Δ, Γ, fs, c ⧽ ⊢ s₂ ⊣ sig₂ ->
  `⧼ Δ, Γ, fs, c ⧽ ⊢ `if e `then s₁ `else s₂ ⊣ sig
where "'`⧼' Δ , Γ , fs , c ⧽ '⊢' s ⊣ sig" := (type_stm Δ Γ fs c s sig).

Local Close Scope stm_scope.

(** * Control-declaration typing. *)

(** Control-declaration typing context. *)
Record ctrl_type_env : Set :=
  mk_ctrl_type_env
    { ctype_vars : nat
    ; ctypes : list Typ.t
    ; cfuncts : fenv (** available functions. *)
    ; cinsts : ienv  (** available control instances. *)
    ; actns : aenv   (** available action signatures. *)
    ; tbls : tbl_env (** available table names. *) }.

Global Instance eta_ctrl_type_env : Settable _ :=
  settable! mk_ctrl_type_env
  < ctype_vars ; ctypes ; cfuncts ; cinsts ; actns ; tbls >.

Reserved Notation "Γ '⊢ᵪ' d '⊣' result"
         (at level 80, no associativity).

Variant ctrl_type : Set :=
  | ctrl_var_type (τ : Typ.t)
  | ctrl_act_type (action_name : String.string)
      (ctrl_params : list Typ.t) (data_params : Typ.params)
  | ctrl_tbl_type (table_name : String.string) (number_of_actions : nat).

(** Control declaration typing,
    Producing either a new action or table. *)
Variant type_ctrl (Γ : ctrl_type_env)
  : Ctrl.t -> ctrl_type -> Prop :=
  | type_ctrl_var x te τ :
    SumForall
      (fun τ' => τ' = τ /\ typ_ok (ctype_vars Γ) τ')
      (fun e  => `⟨ ctype_vars Γ, ctypes Γ ⟩ ⊢ e ∈ τ) te ->
    Γ ⊢ᵪ Ctrl.Var x te ⊣ ctrl_var_type τ
  | type_action action_name cparams dparams body sig :
    `⧼ ctype_vars Γ, map snd cparams ++ bind_all dparams (ctypes Γ),
        cfuncts Γ, CAction (actns Γ) (cinsts Γ) ⧽ ⊢ body ⊣ sig ->
    Γ ⊢ᵪ Ctrl.Action action_name cparams dparams body
      ⊣ ctrl_act_type action_name (map snd cparams) dparams
  | type_table table_name key actions def :
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
    predop
      (fun '(a, es) =>
         In a (map fst actions)
         /\ exists ctrl_params data_params,
           actns Γ a = Some (ctrl_params, data_params)
           /\ Forall2 (type_exp (ctype_vars Γ) (ctypes Γ)) es ctrl_params)
      def ->
    Γ ⊢ᵪ Ctrl.Table
      table_name key actions def ⊣ ctrl_tbl_type table_name (List.length actions)
where "Γ '⊢ᵪ' d '⊣' result"
  := (type_ctrl Γ d result) : type_scope.

Local Open Scope climate_scope.

Definition type_ctrls
           (Γ : list Typ.t)
           (fs : fenv)
           (cis : ienv)
           (ctrl : list Ctrl.t) : ctrl_type_env -> Prop :=
  FoldLeft
    (fun d Γ Γ' =>
       exists result,
         Γ ⊢ᵪ d ⊣ result /\
           match result with
           | ctrl_var_type τ =>
               Γ' = Γ <| ctypes := τ :: Γ.(ctypes) |>
           | ctrl_act_type an cps dps =>
               Γ' = Γ <| actns := an ↦ (cps, dps) ,, actns Γ |>
           | ctrl_tbl_type tn n =>
               Γ' = Γ <| tbls := tn ↦ n ,, tbls Γ |>
           end)
    ctrl
    {| ctype_vars := 0
    ; ctypes := Γ
    ; cfuncts := fs
    ; cinsts := cis
    ; actns := ∅ ; tbls := ∅ |}.

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

Reserved Notation "Γ₁ '⊢tp' d ⊣ Γ₂"
         (at level 80, no associativity).

(** Top-level declaration typing. *)
Inductive type_top (Γ : top_type_env)
  : Top.t -> top_type_env -> Prop :=
| type_instantiate_cnstr
    sig decl_name instance_name
    cparams exp_cparams cargs exp_cargs extern_params params :
  cnstrs Γ decl_name =
    Some (CtrType sig cparams exp_cparams extern_params params) ->
  Forall2
    (fun carg cparam =>
       match cparam with
       | InstTyp.Ctr sig eps ps
         => insts_env Γ carg = Some (inr (sig,eps,ps))
       | InstTyp.Extern extern_type
         => (* TODO:
              How to represent extern types?
              [nth_error (externs (insts_envs Γ)) extn = extern_type] *)
           False
       | _ => False
       end) cargs cparams ->
  Forall2
    (type_exp 0 [])
    exp_cargs exp_cparams ->
  Γ ⊢tp Top.Instantiate
    decl_name instance_name [] cargs exp_cargs
    ⊣ Γ <| insts_env :=
    insts_bind_other
      instance_name sig extern_params params
      Γ.(insts_env) |>
| type_instantiate_package
    package_decl_name instance_name
    cparams exp_cparams cargs exp_cargs :
  cnstrs Γ package_decl_name =
    Some (PackageType cparams exp_cparams) ->
  Forall2
    (fun carg cparam =>
       match cparam with
       | InstTyp.Ctr sig eps ps
         => insts_env Γ carg = Some (inr (sig,eps,ps))
       | InstTyp.Extern extern_type
         => (* TODO:
              How to represent extern types?
              [nth_error (externs (insts_envs Γ)) extn = extern_type] *)
           False
       | _ => False
       end) cargs cparams ->
  Forall2
    (type_exp 0 [])
    exp_cargs exp_cparams ->
  Γ ⊢tp Top.Instantiate
    package_decl_name instance_name [] cargs exp_cargs
    ⊣ Γ (* TODO: represent package types in [ienv] *)
| type_instantiate_extern
    (* TODO: How to represent extern types & type instantiations? *)
    extern_decl_name extern_name
    exp_cparams cparams τs exp_cargs cargs methods :
  Forall (typ_ok 0) τs ->
  cnstrs Γ extern_decl_name =
    Some (ExternType (List.length τs) cparams exp_cparams extern_name) ->
  Forall2
    (fun carg cparam =>
       match cparam with
       | InstTyp.Extern extern_type
         => (* TODO:
              How to represent extern types?
              [nth_error (externs (insts_envs Γ)) extn = extern_type] *)
           False
       | _ => False
       end)
    cargs (map (tsub_insttyp (gen_tsub τs)) cparams) ->
  Forall2
    (type_exp 0 [])
    exp_cargs (map (tsub_typ (gen_tsub τs)) exp_cparams) ->
  Γ ⊢tp Top.Instantiate extern_decl_name extern_name τs cargs exp_cargs
    ⊣ Γ <| insts_env := (* TODO: sub [τs] into methods *)
         insts_bind_externs
         extern_name methods Γ.(insts_env) |>   
| type_control
    control_name cparams exp_cparams extern_params params
    control_decls apply_blk Γ' sig insts :
  (* TODO: check params are [typ_ok []] *)
  (* TODO: add extern runtime params
     to instance envrionment when checking control body. *)
  insts = cbind_all (insts_env Γ) cparams ->
  type_ctrls
    exp_cparams (tfuncts Γ) insts control_decls Γ' ->
  `⧼ 0, bind_all params exp_cparams,
      tfuncts Γ, CApplyBlock (tbls Γ') (actns Γ') insts ⧽
    ⊢ apply_blk ⊣ sig ->
  Γ ⊢tp
    Top.Control
    control_name cparams exp_cparams extern_params
    params control_decls apply_blk
    ⊣ Γ <| cnstrs :=
    control_name
      ↦ CtrType Cnstr.Control
      (map snd cparams) exp_cparams (map snd extern_params) params ,, cnstrs Γ |>
| type_parser
    parser_decl_name cparams exp_cparams extern_params params
    start_state states insts :
  (* TODO: check params are [typ_ok []] *)
  (* TODO: add extern runtime params
     to instance envrionment when checking control body. *)
  insts = cbind_all (insts_env Γ) cparams ->
  Forall
    (fun state =>
       `⧼ 0, bind_all params exp_cparams, tfuncts Γ,
           CParserState (List.length states) insts ⧽ ⊢ state ⊣ Signal.Trns)
    (start_state :: states) ->
  Γ ⊢tp Top.Parser
    parser_decl_name cparams exp_cparams extern_params params
    start_state states
    ⊣ Γ <| cnstrs :=
            parser_decl_name
              ↦ CtrType Cnstr.Parser
              (map snd cparams) exp_cparams
              (map snd extern_params) params ,, cnstrs Γ |>
| type_extern
    extern_name type_params cparams exp_cparams methods :
  (* TODO: check types as [typ_ok] *)
  Γ ⊢tp Top.Extern extern_name type_params cparams exp_cparams methods
    ⊣ Γ <| cnstrs :=
              extern_name
                ↦ ExternType
                type_params (map snd cparams)
                exp_cparams extern_name ,, cnstrs Γ |>
| type_function function_name type_params arrow body sig :
  good_signal arrow sig ->
  `⧼ type_params, bind_all (paramargs arrow) [], tfuncts Γ,
      CFunction (rtrns arrow) ⧽ ⊢ body ⊣ sig ->
  Γ ⊢tp Top.Funct
    function_name type_params arrow body
    ⊣ Γ <| tfuncts := function_name ↦ (type_params,arrow) ,, tfuncts Γ |>
where
"Γ₁ '⊢tp' d ⊣ Γ₂"
  := (type_top Γ₁ d Γ₂).

Local Close Scope climate_scope.

Definition type_prog
  : Top.prog -> top_type_env -> top_type_env -> Prop :=
  FoldLeft (fun d Γ Γ' => Γ ⊢tp d ⊣ Γ').
