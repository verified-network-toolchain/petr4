Require Import Coq.ZArith.BinInt
  Poulet4.P4cub.Syntax.CubNotations
  Poulet4.P4light.Architecture.Target
  Poulet4.P4light.Syntax.Syntax
  Poulet4.P4cub.Semantics.Climate
  RecordUpdate.RecordSet.
From Poulet4.P4cub.Semantics.Dynamic Require Import
     BigStep.Value.Value.
From Poulet4.P4cub.Semantics.Dynamic Require Export
  BigStep.ExprUtil BigStep.ValEnvUtil BigStep.InstUtil
  BigStep.Value.Embed.
From RecordUpdate Require Import RecordSet.
Import Clmt.Notations RecordSetNotations.

(** * Expression evaluation. *)

Reserved Notation "⟨ ϵ , e ⟩ ⇓ v"
         (at level 80, no associativity).

Local Open Scope val_scope.
Local Open Scope exp_scope.

Inductive exp_big_step (ϵ : list Val.t)
  : Exp.t -> Val.t -> Prop :=
| ebs_bool (b : bool) :
  ⟨ ϵ, Exp.Bool b ⟩ ⇓ Val.Bool b
| ebs_bit w n :
  ⟨ ϵ, w `W n ⟩ ⇓ w VW n
| ebs_int w z :
  ⟨ ϵ, w `S z ⟩ ⇓ w VS z
| ebs_varbit m w n :
  ⟨ ϵ, Exp.VarBit m w n ⟩ ⇓ Val.VarBit m w n
| ebs_var τ og x v :
  nth_error ϵ x = Some v ->
  ⟨ ϵ, Exp.Var τ og x ⟩ ⇓ v
| ebs_slice e hi lo v v' :
  slice_val hi lo v = Some v' ->
  ⟨ ϵ, e ⟩ ⇓ v ->
  ⟨ ϵ, Exp.Slice hi lo e ⟩ ⇓ v'
| ebs_cast τ e v v' :
  eval_cast τ v = Some v' ->
  ⟨ ϵ, e ⟩ ⇓ v ->
  ⟨ ϵ, Exp.Cast τ e ⟩ ⇓ v'
| ebs_error err :
  ⟨ ϵ, Exp.Error err ⟩ ⇓ Val.Error err
| ebs_uop τ op e v v' :
  eval_una op v = Some v' ->
  ⟨ ϵ, e ⟩ ⇓ v ->
  ⟨ ϵ, Exp.Uop τ op e ⟩ ⇓ v'
| ebs_bop τ op e₁ e₂ v v₁ v₂ :
  eval_bin op v₁ v₂ = Some v ->
  ⟨ ϵ, e₁ ⟩ ⇓ v₁ ->
  ⟨ ϵ, e₂ ⟩ ⇓ v₂ ->
  ⟨ ϵ, Exp.Bop τ op e₁ e₂ ⟩ ⇓ v
| ebs_member τ x e ls vs v :
  nth_error vs x = Some v ->
  ⟨ ϵ, e ⟩ ⇓ Val.Lists ls vs ->
  ⟨ ϵ, Exp.Member τ x e ⟩ ⇓ v
| ebs_index τ e₁ e₂ ls vs w n v :
  nth_error vs (Z.to_nat n) = Some v ->
  ⟨ ϵ, e₁ ⟩ ⇓ Val.Lists ls vs ->
  ⟨ ϵ, e₂ ⟩ ⇓ w VW n ->
  ⟨ ϵ, Exp.Index τ e₁ e₂ ⟩ ⇓ v
| ebs_lists ls es vs :
  Forall2 (exp_big_step ϵ) es vs ->
  ⟨ ϵ, Exp.Lists ls es ⟩ ⇓ Val.Lists ls vs
where "⟨ ϵ , e ⟩ ⇓ v"
  := (exp_big_step ϵ e v) : type_scope.

Local Open Scope lval_scope.

(** L-expession evaluation. *)

Reserved Notation "'l⟨' ϵ , e ⟩ '⇓' lv" (at level 80, no associativity).

Inductive lexp_big_step (ϵ : list Val.t) : Exp.t -> Lval.t -> Prop :=
| lebs_var τ og x :
  l⟨ ϵ, Exp.Var τ og x ⟩ ⇓ Lval.Var x
| lebs_slice hi lo e lv :
  l⟨ ϵ, e ⟩ ⇓ lv ->
  l⟨ ϵ, Exp.Slice hi lo e ⟩ ⇓ Lval.Slice hi lo lv
| lebs_member τ x e lv :
  l⟨ ϵ, e ⟩ ⇓ lv ->
  l⟨ ϵ, Exp.Member τ x e ⟩ ⇓ lv DOT x
| lebs_index τ e₁ e₂ lv w n :
  ⟨ ϵ, e₂ ⟩ ⇓ (w VW n)%val ->
  l⟨ ϵ, e₁ ⟩ ⇓ lv ->
  l⟨ ϵ, Exp.Index τ e₁ e₂ ⟩ ⇓ Lval.Index (Z.to_N n) lv
where "'l⟨' ϵ , e ⟩ '⇓' lv"
  := (lexp_big_step ϵ e lv) : type_scope.

Local Close Scope exp_scope.
Local Close Scope lval_scope.

(** Transition evaluation. *)

Reserved Notation "'p⟨' ϵ , e ⟩ ⇓ st" (at level 80, no associativity).

Variant trns_big_step (ϵ : list Val.t)
  : Trns.t -> Lbl.t -> Prop :=
  | tbs_direct st :
    p⟨ ϵ, Trns.Direct st ⟩ ⇓ st
  | tbs_select e default cases v :
    ⟨ ϵ, e ⟩ ⇓ v ->
    p⟨ ϵ, Trns.Select e default cases ⟩
       ⇓ match Field.find_value (fun p => match_pattern p v) cases with
         | Some st => st
         | None    => default
         end
where "'p⟨' ϵ , e ⟩ ⇓ st"
  := (trns_big_step ϵ e st) : type_scope.

(** * Statement evaluation. *)

(** Statement signals. *)
Variant signal : Set :=
  | Cont                    (** continue *)
  | Exit                    (** exit *)
  | Acpt                    (** parser accept *)
  | Rjct                    (** parser reject *)       
  | Rtrn (v : option Val.t) (** return *).

Variant Embed_signal : signal -> Value.signal -> Prop :=
| embed_cont : Embed_signal Cont Value.SContinue
| embed_exit : Embed_signal Exit Value.SExit
| embed_rjct x : Embed_signal Rjct (Value.SReject x)
| embed_acpt : Embed_signal Acpt Value.SContinue (* TODO: look at tofino, maybe return here *)
| embed_rtrn_none : Embed_signal (Rtrn None) Value.SReturnNull
| embed_rtrn_some v v' :
  Embed v v' ->
  Embed_signal (Rtrn (Some v)) (Value.SReturn v').

Variant parser_signal : signal -> signal -> Prop :=
| parser_acpt_cont : parser_signal Acpt Cont
| parser_rjct_rjct : parser_signal Rjct Rjct
| parser_exit_exit : parser_signal Exit Exit.

(** Evidence that control-flow
      is interrupted by an exit or return statement. *)
Variant interrupt : signal -> Prop :=
| interrupt_exit    : interrupt Exit
| interrupt_rtrn vo : interrupt (Rtrn vo)
| interrupt_rjct    : interrupt Rjct.

(** A final parser state. *)
Variant final_state : Lbl.t -> signal -> Prop :=
  | final_accept : final_state Lbl.Accept Acpt
  | final_reject : final_state Lbl.Reject Rjct.

(** An intermediate parser state. *)
Variant intermediate_state : Lbl.t -> Prop :=
  | intermediate_start  : intermediate_state Lbl.Start
  | intermediate_name x : intermediate_state (Lbl.Name x).

(** Context for statement evaluation.
    Syntactically where a statement
    occurs within a program
    determines which environments
    are available to it. *)
Variant ctx : Set :=
  | CAction
      (available_actions : aenv)
  | CFunction
  | CApplyBlock
      (tables : tenv)
      (available_actions : aenv)
      (available_controls : inst_env Val.t)
  | CParserState
      (parser_arg_length : nat)
      (start : Stm.t)
      (states : list Stm.t)
      (available_parsers : inst_env Val.t).

Variant actions_of_ctx : ctx -> aenv -> Prop :=
  | actions_of_CAction a :
    actions_of_ctx (CAction a) a
  | actions_of_CApplyBlock te aa cs :
    actions_of_ctx (CApplyBlock te aa cs) aa.

(** Fetch the next state-block to evaluate. *)
Definition get_state_block
           (strt : Stm.t)
           (states : list Stm.t)
           (next : Lbl.t) : option Stm.t :=
  match next with
  | Lbl.Start  => Some strt
  | Lbl.Name x => nth_error states x
  | _             => None
  end.

Local Open Scope stm_scope.

Definition lv_update_signal
           (olv : option Lval.t) (sig : signal)
           (ϵ : list Val.t) : list Val.t :=
  match olv, sig with
  | Some lv, Rtrn (Some v) => lv_update lv v ϵ
  | _ , _ => ϵ
  end.

Notation light_set := (@ValueSet unit).

Variant table_entry_big_step
  : table_entry (Expression:=Exp.t) -> Pat.t -> action_ref -> Prop :=
  | bs_mk_table_entry mtchs pats aref :
    Forall2 embed_pat_valset pats mtchs ->
    table_entry_big_step (mk_table_entry mtchs aref) (Pat.Lists pats) aref.

Notation Extern_Sem := (ExternSem (tags_t:=unit) (Expression:=Exp.t)).

Section StmEvalEnv.
  Variable ext_sem : Extern_Sem.
  
  Record stm_eval_env : Type :=
    mk_stm_eval_env {
        functs : fenv (** function closure. *) ;
        extrn_env   : extern_env (** extern environment. *);
        extrn_state : extern_state (** extern state. *) }.
  
  Global Instance eta_stm_eval_env : Settable _
    := settable! mk_stm_eval_env <functs; extrn_env; extrn_state>.
End StmEvalEnv.

Arguments functs {_}.
Arguments extrn_env {_}.
Arguments extrn_state {_}.
Arguments eta_stm_eval_env {_}.

(** Statement evaluation :
    Given a statement evaluation environment [Ψ]
    and a De Bruijn val environment [ϵ],
    a syntactic context [c],
    a statement [s] is evaluated to
    a new val environment [ϵ'],
    a signal [sig], and a new extern state [ψ]. *)
Reserved Notation "⧼ Ψ , ϵ , c , s ⧽ ⤋ ⧼ ϵ' , sig , ψ ⧽"
         (at level 80, no associativity).

Definition copy_out_from_arg
  (input_arg : paramarg Val.t Lval.t) (output_arg : paramarg Val.t Val.t)
  (ϵ_call : list Val.t) : list Val.t :=
  match input_arg, output_arg with
  | PAOut lv, PAOut v
  | PAInOut lv, PAInOut v => lv_update lv v ϵ_call
  | _, _ => ϵ_call
  end.

Fixpoint copy_out_from_args
  (input_args : Argsv) (output_args : list (paramarg Val.t Val.t))
  (ϵ_call : list Val.t) : list Val.t :=
  match input_args, output_args with
  | i :: iargs, o :: oargs => copy_out_from_args iargs oargs (copy_out_from_arg i o ϵ_call)
  | _, _ => ϵ_call
  end.

Definition arg_big_step (ϵ : list Val.t) : Exp.arg -> Argv -> Prop :=
  rel_paramarg
    (exp_big_step ϵ)
    (lexp_big_step ϵ).

Definition args_big_step (ϵ : list Val.t) : Exp.args -> Argsv -> Prop :=
  Forall2 (arg_big_step ϵ).

Variant eval_table_action
  : option (string * list Exp.t) -> option (@action_ref Exp.t) -> bool -> string -> list Exp.t -> Prop :=
  | eval_table_action_hit def a opt_ctrl_args ctrl_args :
    (** Force control-plane arguments to be defined. *)
    Forall2 (fun oe e => oe = Some e) opt_ctrl_args ctrl_args ->
    eval_table_action def (Some (mk_action_ref a opt_ctrl_args)) true a ctrl_args
  | eval_table_action_miss a ctrl_args :
    eval_table_action (Some (a, ctrl_args)) None false a ctrl_args.

Inductive stm_big_step
  `{ext_sem : Extern_Sem} (Ψ : stm_eval_env ext_sem)
  : list Val.t -> ctx -> Stm.t -> list Val.t -> signal
    -> extern_state (tags_t:=unit) (Expression:=Exp.t) -> Prop :=
| sbs_skip ϵ c :
  ⧼ Ψ, ϵ, c, Stm.Skip ⧽ ⤋ ⧼ ϵ, Cont, extrn_state Ψ ⧽
| sbs_exit ϵ c :
  ⧼ Ψ, ϵ, c, Stm.Exit ⧽ ⤋ ⧼ ϵ, Exit, extrn_state Ψ ⧽
| sbs_ret ϵ c eo vo :
  relop (exp_big_step ϵ) eo vo ->
  ⧼ Ψ, ϵ, c, Stm.Ret eo ⧽ ⤋ ⧼ ϵ, Rtrn vo, extrn_state Ψ ⧽
| sbs_trans_final
    ϵ trns n start states parsers lbl sig :
  final_state lbl sig ->
  p⟨ ϵ, trns ⟩ ⇓ lbl ->
  ⧼ Ψ, ϵ, CParserState n start states parsers,
    Stm.Trans trns ⧽ ⤋ ⧼ ϵ, sig, extrn_state Ψ ⧽
| sbs_trans_intermediate
    ϵ₁ ϵ₂ ϵ₃ trns start states parsers ψ lbl sig state :
  get_state_block start states lbl = Some state ->
  intermediate_state lbl ->
  p⟨ ϵ₁ ++ ϵ₂, trns ⟩ ⇓ lbl ->
  ⧼ Ψ, ϵ₂, CParserState (length ϵ₂) start states parsers, state ⧽ ⤋ ⧼ ϵ₃, sig, ψ ⧽ ->
  ⧼ Ψ, ϵ₁ ++ ϵ₂, CParserState (length ϵ₂) start states parsers,
    Stm.Trans trns ⧽ ⤋ ⧼ ϵ₁ ++ ϵ₃, sig, ψ ⧽
| sbs_asgn ϵ c e₁ e₂ lv v :
  l⟨ ϵ, e₁ ⟩ ⇓ lv ->
  ⟨ ϵ, e₂ ⟩ ⇓ v ->
  ⧼ Ψ, ϵ, c, e₁ `:= e₂ ⧽ ⤋ ⧼ lv_update lv v ϵ, Cont, extrn_state Ψ ⧽
| sbs_setvalidity ϵ c b oldb e lv vs :
  l⟨ ϵ, e ⟩ ⇓ lv ->
  ⟨ ϵ, e ⟩ ⇓ Val.Lists (Lst.Header oldb) vs ->
  ⧼ Ψ, ϵ, c, Stm.SetValidity b e ⧽ ⤋ ⧼ lv_update lv (Val.Lists (Lst.Header b) vs) ϵ, Cont, extrn_state Ψ ⧽
| sbs_funct_call
    ϵ ϵ' ϵ'' c ψ f τs args
    eo vargs olv fun_clos body sig :
  functs Ψ f = Some (FDecl fun_clos body) ->
  (** Evaluate l-expression. *)
  relop (lexp_big_step ϵ) eo olv ->
  (** Evaluate arguments. *)
  args_big_step ϵ args vargs ->
  (** Copyin. *)
  copy_in vargs ϵ = Some ϵ' ->
  (** Evaluate the function body. *)
  ⧼ Ψ <| functs := fun_clos |>, ϵ', CFunction,
      tsub_stm (gen_tsub τs) body ⧽ ⤋ ⧼ ϵ'', sig, ψ ⧽ ->
  ⧼ Ψ, ϵ, c, Stm.App (Call.Funct f τs eo) args ⧽
    ⤋ ⧼ lv_update_signal olv sig (copy_out O vargs ϵ'' ϵ), Cont, ψ ⧽  
| sbs_action_call
    ϵ ϵ' ϵ'' clos c ψ a ctrl_args data_args actions
    vctrl_args vdata_args act_clos body sig :
  (** Get action from context. *)
  actions_of_ctx c actions ->
  (** Lookup action. *)
  actions a = Some (ADecl clos act_clos body) ->
  (** Evaluate control-plane arguments. *)
  Forall2 (exp_big_step ϵ) ctrl_args vctrl_args ->
  (** Evaluate data-plane arguments. *)
  args_big_step ϵ data_args vdata_args ->
  (** Copyin. *)
  copy_in vdata_args ϵ = Some ϵ' ->
  (** Evaluate the action body. *)
  ⧼ Ψ, vctrl_args ++ ϵ' ++ clos, CAction act_clos,
      body ⧽ ⤋ ⧼ ϵ'', sig, ψ ⧽ ->
  ⧼ Ψ, ϵ, c, Stm.App (Call.Action a ctrl_args) data_args ⧽
    ⤋ ⧼ copy_out O vdata_args ϵ'' ϵ, Cont, ψ ⧽
| sbs_method_call
    ϵ c ψ ext meth τs args
    eo vargs vargs' olv sig
    light_typs light_in_vals light_out_vals light_sig :
  (** Invariant for cub arguments. *)
  Forall2
    (rel_paramarg eq (fun _ _ => True))
    vargs vargs' ->
  (** Evaluate l-expression. *)
  relop (lexp_big_step ϵ) eo olv ->
  (** Evaluate arguments. *)
  args_big_step ϵ args vargs ->
  (** Embed type arguments in p4light. *)
  Forall2 (EmbedType (dummy_tags:=tt) (string_list:=[])) τs light_typs ->
  (** Embed in-arguments in p4light. *)
  Forall2
    Embed
    (List.flat_map
       (fun v => match v with PAIn v => [v] | _ => [] end)
       vargs) light_in_vals ->
  (** Evaluate the extern. *)
  exec_extern
    (extrn_env Ψ) (extrn_state Ψ)
    ext meth [] light_typs light_in_vals ψ light_out_vals light_sig ->
  (** Out-vals back to p4cub. *)
  Forall2
    Embed
    (List.flat_map
       (fun v => match v with PAOut v | PAInOut v => [v] | _ => [] end)
       vargs') light_out_vals ->
  (** Signal back to p4cub. *)
  Embed_signal sig light_sig ->
  ⧼ Ψ, ϵ, c, Stm.App (Call.Method ext meth τs eo) args ⧽
    ⤋ ⧼ lv_update_signal olv sig (copy_out_from_args vargs vargs' ϵ), sig, ψ ⧽
| sbs_invoke
    ϵ₁ ϵ₂ ϵ' eo lvo t (tbls : tenv) acts insts pats light_sets
    ψ (key : list (Exp.t * string)) actions def vs light_vals arefs
    hit a idx ctrl_args data_args :
  (** Evaluate left hand expression *)
  relop (lexp_big_step (ϵ₁ ++ ϵ₂)) eo lvo ->
  (** Lookup table. *)
  tbls t = Some (length ϵ₂, key, actions, def) ->
  (** Evaluate table key. *)
  Forall2 (exp_big_step ϵ₂) (map fst key) vs ->
  (** Evaluate table entries. *)
  Forall3 table_entry_big_step (extern_get_entries Ψ.(extrn_state) []) pats arefs ->
  (** Embed table key *)
  Forall2 Embed vs light_vals ->
  (** Embed p4cub patterns in p4light val sets. *)
  Forall2 embed_pat_valset pats light_sets ->
  (** Get action reference from control-plane with control-plane arguments. *)
  eval_table_action
    def
    (extern_match (combine light_vals (map snd key)) (combine light_sets arefs))
    hit a ctrl_args ->
  (** Find appropriate action data-plane arguments in table. *)
  Field.get a actions = Some data_args ->
  (** Get index of action name in table declaration. *)
  Field.get_index a actions = Some idx ->
  (** Evaluate action. *)
  ⧼ Ψ, ϵ₂, CApplyBlock tbls acts insts,
    Stm.App (Call.Action a ctrl_args) data_args ⧽ ⤋ ⧼ ϵ', Cont, ψ ⧽ ->
  ⧼ Ψ, ϵ₁ ++ ϵ₂, CApplyBlock tbls acts insts,
    Stm.Invoke eo t ⧽
    ⤋ ⧼ lv_update_signal
          lvo
          (Rtrn
             (Some 
             (Val.Lists
                Lst.Struct
                [Val.Bool hit; Val.Bool (negb hit);
                 Val.Bit (BinNat.N.of_nat (length actions)) (Z.of_nat idx)])))
          (ϵ₁ ++ ϵ'), Cont, ψ ⧽
| sbs_apply_control
    ϵ ϵ' ϵ'' eps_clos tbls actions control_insts
    c ext_args args vargs sig ψ
    fun_clos inst_clos tbl_clos action_clos apply_block :
  (** Lookup control instance. *)
  control_insts c
  = Some (ControlInst
            fun_clos inst_clos tbl_clos
            action_clos eps_clos apply_block) ->
  (** Evaluate arguments. *)
  args_big_step ϵ args vargs ->
  (** Copyin. *)
  copy_in vargs ϵ = Some ϵ' ->
  (** Evaluate control apply block. *)
  ⧼ Ψ <| functs := fun_clos |>, ϵ' ++ eps_clos, CApplyBlock tbl_clos action_clos inst_clos,
      apply_block ⧽ ⤋ ⧼ ϵ'', sig, ψ ⧽ ->
  ⧼ Ψ, ϵ, CApplyBlock tbls actions control_insts,
    Stm.App (Call.Inst c ext_args) args ⧽ ⤋ ⧼ copy_out O vargs ϵ'' ϵ, Cont, ψ ⧽
| sbs_apply_parser
    ϵ ϵ' ϵ'' p_eps n strt states parsers ψ p
    ext_args args vargs
    p_fun p_prsr p_strt p_states final sig :
  (** Lookup parser instance. *)
  parsers p = Some (ParserInst p_fun p_prsr p_eps p_strt p_states) ->
  (** Evaluate arguments. *)
  args_big_step ϵ args vargs ->
  (** Copyin. *)
  copy_in vargs ϵ = Some ϵ' ->
  parser_signal final sig ->
  (** Evaluate parser state machine. *)
  ⧼ Ψ <| functs := p_fun |>, ϵ' ++ p_eps,
      CParserState
        (length args) p_strt p_states p_prsr, p_strt ⧽ ⤋ ⧼ ϵ'', final, ψ ⧽ ->
  ⧼ Ψ, ϵ, CParserState n strt states parsers,
    Stm.App (Call.Inst p ext_args) args ⧽ ⤋ ⧼ copy_out O vargs ϵ'' ϵ, sig, ψ ⧽
| sbs_letin ϵ ϵ' c og te v v' s sig ψ :
  SumForall (fun τ => val_of_typ τ = Some v) (fun e => ⟨ ϵ, e ⟩ ⇓ v) te ->
  ⧼ Ψ, v :: ϵ, c, s ⧽ ⤋ ⧼ v' :: ϵ', sig, ψ ⧽ ->
  ⧼ Ψ, ϵ, c, `let og := te `in s ⧽ ⤋ ⧼ ϵ', sig, ψ ⧽
| sbs_seq_cont ϵ ϵ' ϵ'' c s₁ s₂ sig ψ ψ' :
  ⧼ Ψ, ϵ, c, s₁ ⧽ ⤋ ⧼ ϵ', Cont, ψ ⧽ ->
  ⧼ Ψ <| extrn_state := ψ |>, ϵ', c, s₂ ⧽ ⤋ ⧼ ϵ'', sig, ψ' ⧽ ->
  ⧼ Ψ, ϵ, c, s₁ `; s₂ ⧽ ⤋ ⧼ ϵ'', sig, ψ' ⧽
| sbs_seq_interrupt ϵ ϵ' c s₁ s₂ sig ψ :
  interrupt sig ->
  ⧼ Ψ, ϵ, c, s₁ ⧽ ⤋ ⧼ ϵ', sig, ψ ⧽ ->
  ⧼ Ψ, ϵ, c, s₁ `; s₂ ⧽ ⤋ ⧼ ϵ', sig, ψ ⧽
| sbs_cond ϵ ϵ' c e s₁ s₂ (b : bool) sig ψ :
  ⟨ ϵ, e ⟩ ⇓ Val.Bool b ->
  ⧼ Ψ, ϵ, c, if  b then  s₁ else  s₂ ⧽ ⤋ ⧼ ϵ', sig, ψ ⧽ ->
  ⧼ Ψ, ϵ, c, `if e `then s₁ `else s₂ ⧽ ⤋ ⧼ ϵ', sig, ψ ⧽
where "⧼ Ψ , ϵ , c , s ⧽ ⤋ ⧼ ϵ' , sig , ψ ⧽"
  := (stm_big_step Ψ ϵ c s ϵ' sig ψ) : type_scope.

Local Close Scope stm_scope.
Local Open Scope climate_scope.

Record ctrl_bs_env : Set :=
  mk_ctrl_bs_env
    { cbs_tables  : tenv;
      cbs_actions : aenv;
      cbs_epsilon : list Val.t }.

Global Instance eta_ctrl_bs_env : Settable _ :=
  settable! mk_ctrl_bs_env
  < cbs_tables ; cbs_actions ; cbs_epsilon >.

Variant ctrl_big_step
  (cbs_env : ctrl_bs_env)
  : Ctrl.t -> ctrl_bs_env -> Prop :=
  | cbs_var x te v :
    SumForall
      (fun τ => val_of_typ τ = Some v)
      (fun e => ⟨ cbs_epsilon cbs_env, e ⟩ ⇓ v)
      te ->
    ctrl_big_step
      cbs_env (Ctrl.Var x te)
      (cbs_env <| cbs_epsilon := v :: cbs_epsilon cbs_env |>)
  | cbs_action a ctrl_params data_params body :
    ctrl_big_step
      cbs_env (Ctrl.Action a ctrl_params data_params body)
      (cbs_env
         <| cbs_actions :=
         a ↦ ADecl (cbs_epsilon cbs_env) (cbs_actions cbs_env) body ,, cbs_actions cbs_env |>)
  | cbs_table t key actions def :
    ctrl_big_step
      cbs_env (Ctrl.Table t key actions def)
      (cbs_env
         <| cbs_tables :=
         t ↦ (length (cbs_epsilon cbs_env), key, actions, def) ,, cbs_tables cbs_env |>).

Definition ctrls_big_step
  : list Ctrl.t -> ctrl_bs_env -> ctrl_bs_env -> Prop :=
  FoldLeft
    (fun cd env env' => ctrl_big_step env cd env').

Record top_bs_env : Set :=
  mk_top_bs_env
    { top_functs : fenv;
      top_insts  : inst_env Val.t;
      top_decls  : top_env Val.t }.

Global Instance eta_top_bs_env : Settable _ :=
  settable! mk_top_bs_env
  < top_functs ; top_insts ; top_decls >.

Variant top_big_step
  (tbs_env : top_bs_env)
  : Top.t -> top_bs_env -> Prop :=
  | tbs_control c cparams ecparams extparams params body s :
    top_big_step
      tbs_env
      (Top.Control c cparams ecparams extparams params body s)
      (tbs_env
         <| top_decls :=
         c ↦ ControlDecl
           (top_functs tbs_env) (top_insts tbs_env) (map fst cparams) body s ,, top_decls tbs_env |>)
  | tbs_parser p cparams ecparams extparams params strt states :
    top_big_step
      tbs_env
      (Top.Parser p cparams ecparams extparams params strt states)
      (tbs_env
         <| top_decls :=
         p ↦ ParserDecl
           (top_functs tbs_env) (top_insts tbs_env) (map fst cparams) strt states ,, top_decls tbs_env |>)
  | tbs_extern ext TS cparams ecparams methods :
    top_big_step
      tbs_env
      (Top.Extern ext TS cparams ecparams methods)
      (tbs_env
         <| top_decls :=
         ext ↦ ExternDecl (top_functs tbs_env) (top_insts tbs_env) (map fst cparams) ,, top_decls tbs_env |>)
  | tbs_funct f TS arrow body :
    top_big_step
      tbs_env
      (Top.Funct f TS arrow body)
      (tbs_env <| top_functs := f ↦ FDecl (top_functs tbs_env) body ,, top_functs tbs_env |>)
  | tbs_instantiate_control c x cargs es cparams local_decls apply_blk vs cbs_env cfs cinsts :
    top_decls tbs_env c = Some (ControlDecl cfs cinsts cparams local_decls apply_blk) ->
    Forall2 (exp_big_step []) es vs ->
    ctrls_big_step
      local_decls
      {| cbs_tables  := ∅
      ; cbs_actions := ∅
      ; cbs_epsilon  := vs |}
      cbs_env ->
    top_big_step
      tbs_env
      (Top.Instantiate c x [] cargs es)
      (tbs_env
         <| top_insts :=
         x ↦ ControlInst
           cfs (bind_constructor_args cparams cargs (top_insts tbs_env) cinsts)
           (cbs_tables cbs_env) (cbs_actions cbs_env) vs apply_blk ,, top_insts tbs_env |>)
  | tbs_instantiate_parser p x cargs es pfs pinsts cparams strt states vs :
    top_decls tbs_env p = Some (ParserDecl pfs pinsts cparams strt states) ->
    Forall2 (exp_big_step []) es vs ->
    top_big_step
      tbs_env
      (Top.Instantiate p x [] cargs es)
      (tbs_env
         <| top_insts :=
         x ↦ ParserInst
           pfs (bind_constructor_args cparams cargs (top_insts tbs_env) pinsts)
           vs strt states ,, top_insts tbs_env |>)
  | tbs_instantiate_extern ext x τs cargs es extfs extinsts cparams vs :
    top_decls tbs_env ext = Some (ExternDecl extfs extinsts cparams) ->
    Forall2 (exp_big_step []) es vs ->
    top_big_step
      tbs_env
      (Top.Instantiate ext x τs cargs es)
      (tbs_env
         <| top_insts :=
         x ↦ ExternInst
           extfs
           (bind_constructor_args cparams cargs (top_insts tbs_env) extinsts)
           vs
           ,, top_insts tbs_env |>).

Notation Target_Sem := (Target (tags_t:=unit) (Expression:=Exp.t)).

Section ProgBigStep.
  Context `{target  : Target_Sem}.

  Inductive module_big_step
    (insts : inst_env Val.t) (module_name : string)
     (ϕ : extern_env) (ψ : extern_state) (input : list Val.t)
    : extern_state -> list Val.t -> signal -> Prop :=.
  (*| parser_module_big_step p_fun p_prsr ϵ ϵ' p_eps p_strt p_states
      sig final ψ' :
    (** Lookup parser instance. *)
    insts module_name = Some (ParserInst p_fun p_prsr p_eps p_strt p_states) ->
    (** Copyin. *)
    copy_in input [] = Some ϵ ->
    (** Parser terminates. *)
    parser_signal final sig ->
    (** Evaluate parser state machine. *)
    ⧼ mk_stm_eval_env target.(extern_sem) p_fun ϕ ψ, ϵ ++ p_eps,
        CParserState
          (length input) p_strt p_states p_prsr, p_strt ⧽ ⤋ ⧼ ϵ', final, ψ' ⧽ ->
    module_big_step insts module_name ϕ ψ input ψ' (copy_out O input ϵ' []) sig. *)
    

  Definition prog_big_step
    (prog : list Top.t) (ϕ : extern_env)
    (ψ : extern_state) (input_pkt : list bool)
    (ψ' : extern_state) (output_pkt : list bool) : Prop := exists fs insts ds,
    FoldLeft
      (fun d env  => top_big_step env d) prog
      (mk_top_bs_env ∅ ∅ ∅) (mk_top_bs_env fs insts ds)
    /\ target.(exec_prog)
        []
        (fun pth ψ lvs ψ' lvs' lsig => exists vs vs' sig,
             module_big_step insts (Exn.path_to_string pth) ϕ ψ vs ψ' vs sig
             /\ Forall2 Embed vs lvs
             /\ Forall2 Embed vs' lvs'
             /\ Embed_signal sig lsig)
        ψ input_pkt ψ' output_pkt.
End ProgBigStep.

Local Close Scope val_scope.
Local Close Scope climate_scope.
