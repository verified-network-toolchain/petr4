Require Import Coq.ZArith.BinInt
        Poulet4.P4cub.Syntax.CubNotations.
From Poulet4.P4cub.Semantics.Dynamic Require Import
     BigStep.Value.Value.
From Poulet4.P4cub.Semantics.Dynamic Require Export
     BigStep.ExprUtil BigStep.ValEnvUtil BigStep.InstUtil.
Import Val.ValueNotations ExprNotations
  Val.LValueNotations StmtNotations.

(** * Big-step Semantics. *)

(* TODOs:
   - Needs to use [P4light/Architecture/Target.v].
   - Handle exit signals correctly.
   - Handle results of final parser states correctly.
   - Fix parser evaluation. *)

(** * Expression evaluation. *)

Reserved Notation "⟨ ϵ , e ⟩ ⇓ v"
         (at level 80, no associativity).

Local Open Scope value_scope.
Local Open Scope expr_scope.

Inductive expr_big_step (ϵ : list Val.v)
  : Expr.e -> Val.v -> Prop :=
| ebs_bool (b : bool) :
  ⟨ ϵ, b ⟩ ⇓ b
| ebs_bit w n :
  ⟨ ϵ, w `W n ⟩ ⇓ w VW n
| ebs_int w z :
  ⟨ ϵ, w `S z ⟩ ⇓ w VS z
| ebs_var x τ v :
  nth_error ϵ x = Some v ->
  ⟨ ϵ, Expr.Var τ x ⟩ ⇓ v
| ebs_slice e hi lo v v' :
  eval_slice hi lo v = Some v' ->
  ⟨ ϵ, e ⟩ ⇓ v ->
  ⟨ ϵ, Expr.Slice e hi lo ⟩ ⇓ v'
| ebs_cast τ e v v' :
  eval_cast τ v = Some v' ->
  ⟨ ϵ, e ⟩ ⇓ v ->
  ⟨ ϵ, Expr.Cast τ e ⟩ ⇓ v'
| ebs_error err :
  ⟨ ϵ, Expr.Error err ⟩ ⇓ Val.Error err
| ebs_uop τ op e v v' :
  eval_uop op v = Some v' ->
  ⟨ ϵ, e ⟩ ⇓ v ->
  ⟨ ϵ, Expr.Uop τ op e ⟩ ⇓ v'
| ebs_bop τ op e₁ e₂ v v₁ v₂ :
  eval_bop op v₁ v₂ = Some v ->
  ⟨ ϵ, e₁ ⟩ ⇓ v₁ ->
  ⟨ ϵ, e₂ ⟩ ⇓ v₂ ->
  ⟨ ϵ, Expr.Bop τ op e₁ e₂ ⟩ ⇓ v
| ebs_member τ x e vs v ob :
  nth_error vs x = Some v ->
  ⟨ ϵ, e ⟩ ⇓ Val.Struct vs ob ->
  ⟨ ϵ, Expr.Member τ x e ⟩ ⇓ v
| ebs_struct es vs ob :
  Forall2 (expr_big_step ϵ) es vs ->
  ⟨ ϵ, Expr.Struct es ob ⟩ ⇓ Val.Struct vs ob
where "⟨ ϵ , e ⟩ ⇓ v"
  := (expr_big_step ϵ e v) : type_scope.

Local Close Scope value_scope.
Local Open Scope lvalue_scope.

(** L-expression evaluation. *)

Reserved Notation "e '⇓ₗ' lv" (at level 80, no associativity).

Inductive lexpr_big_step : Expr.e -> Val.lv -> Prop :=
| lebs_var τ x :
  Expr.Var τ x ⇓ₗ Val.Var x
| lebs_slice e hi lo lv :
  e ⇓ₗ lv ->
  Expr.Slice e hi lo ⇓ₗ Val.Slice lv hi lo
| lebs_member τ x e lv :
  e ⇓ₗ lv ->
  Expr.Member τ x e ⇓ₗ lv DOT x
where "e '⇓ₗ' lv"
  := (lexpr_big_step e lv) : type_scope.

Local Close Scope expr_scope.
Local Close Scope lvalue_scope.

(** Parser-expression evaluation. *)

Reserved Notation "'p⟨' ϵ , e ⟩ ⇓ st" (at level 80, no associativity).

Variant parser_expr_big_step (ϵ : list Val.v)
  : Parser.e -> Parser.state -> Prop :=
  | pebs_goto st :
    p⟨ ϵ, Parser.Goto st ⟩ ⇓ st
  | pebs_select e default cases v :
    ⟨ ϵ, e ⟩ ⇓ v ->
    p⟨ ϵ, Parser.Select e default cases ⟩
       ⇓ match Field.find_value (fun p => match_pattern p v) cases with
         | Some st => st
         | None    => default
         end
where "'p⟨' ϵ , e ⟩ ⇓ st"
  := (parser_expr_big_step ϵ e st) : type_scope.

(** * Statement evaluation. *)

(** Statement signals. *)
Variant signal : Set :=
  | Cont                    (** continue *)
  | Exit                    (** exit *)
  | Rtrn (v : option Val.v) (** return *)
  | Rjct                    (** reject *).

(** Evidence that control-flow
      is interrupted by an exit or return statement. *)
Variant interrupt : signal -> Prop :=
| interrupt_exit    : interrupt Exit
| interrupt_rtrn vo : interrupt (Rtrn vo)
| interrupt_rjct    : interrupt Rjct.

(** A final parser state. *)
Variant final_state : Parser.state -> Prop :=
  | final_accept : final_state Parser.Accept
  | final_reject : final_state Parser.Reject.

(** An intermediate parser state. *)
Variant intermediate_state : Parser.state -> Prop :=
  | intermediate_start  : intermediate_state Parser.Start
  | intermediate_name x : intermediate_state (Parser.Name x).

(** Context for statement evaluation,
    syntactically where a statement
    occurs within a program
    determines which environments
    are available to it. *)
Variant ctx : Set :=
  | CAction
      (available_actions : aenv) (* TODO:
                                    needs a De Bruijn
                                    extern instance closure env. *)
  | CFunction
  | CApplyBlock
      (control_plane_entries : ctrl) (* TODO: needs to be replaced with
                                        Target.v equivalent. *)
      (tables : tenv)
      (available_actions : aenv)
      (available_controls : cienv) (* TODO:
                                      needs a De Bruijn
                                      extern instance closure env. *)
  | CParserState
      (available_parsers : pienv) (* TODO:
                                     needs a De Bruijn
                                     extern instance closure env. *).

(* TODO: to be replaced with [Target.v] equivalent
   for the state of externs, packets, etc. *)
Definition extern_state : Set := unit.

Record stmt_eval_env : Set := {
    functs : fenv (** function closure. *) ;
    cntx   : ctx  (** syntactic location of statement. *);
    extrn  : extern_state }.

(*
Record parser_eval_env : Set := {
    pextrn  : extern_state;
    pfuncts : fenv;
    pstart  : Stmt.block      (** start state block. *);
    pstates : list Stmt.block (** user-defined states *);
    parsers : pienv (** parser instance closure. *);
    (* TODO: needs a DeBruijn env for extern instances. *)}.
*)

(** Statement evaluation :
    Given a statement evaluation environment [Ψ]
    and a De Bruijn value environment [ϵ],
    a statement [s] is evaluated to
    a new value environment [ϵ'],
    a signal [sig], and a new extern state [ψ]. *)
Reserved Notation "⧼ Ψ , ϵ , s ⧽ ⤋ ⧼ ϵ' , sig , ψ ⧽"
         (at level 80, no associativity).

(*
(** Parser-state-machine evaluation :
    Given a parser evaluation environment [Φ]
    and a De Bruijn value environment [ϵ],
    a parser-state-machine starting from state [curr]
    evaluates to a new value environment [ϵ'],
    a final state [final], and an extern state [ψ]. *)
Reserved Notation "'Δ' ( Φ , ϵ , curr ) ⇝ ( ϵ' , final , ψ )"
         (at level 80, no associativity).
*)

(** Fetch the next state-block to evaluate. *)
Definition get_state_block
           (strt : Stmt.s)
           (states : list Stmt.s)
           (next : Parser.state) : option Stmt.s :=
  match next with
  | Parser.Start  => Some strt
  | Parser.Name x => nth_error states x
  | _             => None
  end.

Local Open Scope stmt_scope.

Definition lv_update_signal
           (olv : option Val.lv) (sig : signal)
           (ϵ : list Val.v) : list Val.v :=
  match olv, sig with
  | Some lv, Rtrn (Some v) => lv_update lv v ϵ
  | _ , _ => ϵ
  end.

Inductive stmt_big_step
  : stmt_eval_env -> list Val.v -> Stmt.s ->
    list Val.v -> signal -> extern_state -> Prop :=
| sbs_skip Ψ ϵ :
  ⧼ Ψ, ϵ, Stmt.Skip ⧽ ⤋ ⧼ ϵ, Cont, extrn Ψ ⧽
| sbs_exit Ψ ϵ :
  ⧼ Ψ, ϵ, Stmt.Exit ⧽ ⤋ ⧼ ϵ, Exit, extrn Ψ ⧽
| sbs_return Ψ ϵ eo vo :
  relop (expr_big_step ϵ) eo vo ->
  ⧼ Ψ, ϵ, Stmt.Return eo ⧽ ⤋ ⧼ ϵ, Rtrn vo, extrn Ψ ⧽
| sbs_assign Ψ ϵ e₁ e₂ lv v :
  e₁ ⇓ₗ lv ->
  ⟨ ϵ, e₂ ⟩ ⇓ v ->
  ⧼ Ψ, ϵ, e₁ `:= e₂ ⧽ ⤋ ⧼ lv_update lv v ϵ, Cont, extrn Ψ ⧽
| sbs_call
    Ψ ψ ϵ ϵ' ϵ'' fk τs prefix_args args
    eo vargs olv fun_clos body sig :
  match fk with
  | Stmt.Funct f τs' eo'
    => τs = τs' /\ eo = eo' /\ prefix_args = []
      /\ (** Lookup function. *)
        functs Ψ f = Some (FDecl fun_clos body)
  | Stmt.Action a cargs
    => τs = [] /\ eo = None
      /\ (** Evaluate control-plane arguments. *)
        Forall2
          (expr_big_step ϵ)
          cargs prefix_args
      /\ exists actions fun_clos act_clos,
        (** Get avaialble action declarations. *)
        match cntx Ψ with
        | CAction actions
        | CApplyBlock _ _ actions _ => Some actions
        | _ => None
        end = Some actions ->
        (** Lookup action. *)
        actions a = Some (ADecl fun_clos act_clos body)
  | Stmt.Method ei m τs' eo'
    => τs = τs' /\ eo = eo' /\ prefix_args = [] (* TODO: extern lookup how? *)
  end ->
  (** Evaluate l-expression. *)
  relop lexpr_big_step eo olv ->
  (** Evaluate arguments. *)
  Forall2
    (rel_paramarg
       (expr_big_step ϵ)
       lexpr_big_step)
    args vargs ->
  (** Copyin. *)
  copy_in vargs ϵ = Some ϵ' ->
  (** Evaluate the function body. *)
  ⧼ {| functs := fun_clos
    ;  cntx   := CFunction
    ;  extrn  := extrn Ψ |},
    prefix_args ++ ϵ', tsub_s (gen_tsub τs) body ⧽ ⤋ ⧼ ϵ'', sig, ψ ⧽ ->
  ⧼ Ψ, ϵ, Stmt.Call fk args ⧽
    ⤋ ⧼ lv_update_signal olv sig (copy_out vargs ϵ'' ϵ), Cont, ψ ⧽
| sbs_apply_control
    fs entries tbls actions control_insts extrn_state
    ϵ ϵ_clos ϵ' ϵ'' c ext_args args vargs sig ψ
    fun_clos ctrl_clos tbl_clos action_clos apply_block :
  (** Lookup control instance. *)
  nth_error control_insts c
  = Some (CInst
            ϵ_clos fun_clos ctrl_clos tbl_clos
            action_clos apply_block) ->
  (** Evaluate arguments. *)
  Forall2
    (rel_paramarg
       (expr_big_step ϵ)
       lexpr_big_step)
    args vargs ->
  (** Copyin. *)
  copy_in vargs ϵ = Some ϵ' ->
  (** Evaluate control apply block. *)
  ⧼ {| functs := fun_clos
    ;  cntx   := CApplyBlock
                   entries tbl_clos
                   action_clos ctrl_clos
    ;  extrn := extrn_state |},
    ϵ' ++ ϵ_clos, apply_block ⧽ ⤋ ⧼ ϵ'', sig, ψ ⧽ ->
  ⧼ {| functs := fs
    ;  cntx   := CApplyBlock
                   entries tbls actions control_insts
    ;  extrn  := extrn_state |},
    ϵ, Stmt.Apply c ext_args args ⧽
    ⤋ ⧼ copy_out vargs ϵ'' ϵ, Cont, ψ ⧽
(*| sbs_apply_parser
    fs parser_insts ψ ψ' ϵ ϵ_clos ϵ' ϵ'' p
    ext_args args vargs
    fun_clos prsr_clos strt states final :
  (** Lookup parser instance. *)
  nth_error parser_insts p
  = Some (PInst ϵ_clos fun_clos prsr_clos strt states) ->
  (** Evaluate arguments. *)
  Forall2
    (rel_paramarg
       (expr_big_step ϵ)
       lexpr_big_step)
    args vargs ->
  (** Copyin. *)
  copy_in vargs ϵ = Some ϵ' ->
  (** Evaluate parser state machine. *)
  Δ ( {| pextrn  := ψ
      ;  pfuncts := fun_clos
      ;  pstart  := strt
      ;  pstates := states
      ;  parsers := prsr_clos |},
      ϵ' ++ ϵ_clos, Parser.Start ) ⇝ ( ϵ'', final, ψ' ) ->
  `⧼ {| functs := fs
     ;  cntx   := CParserState parser_insts
     ;  extrn  := ψ |},
     ϵ, Stmt.Apply p ext_args args `⧽
     `⤋ `⧼ copy_out vargs ϵ'' ϵ, ψ' `⧽ *)
| sbs_var Ψ ϵ ϵ' te v v' s sig ψ :
  match te with
  | inr e => ⟨ ϵ, e ⟩ ⇓ v
  | inl τ => v_of_t τ = Some v
  end ->
  ⧼ Ψ, v :: ϵ, s ⧽ ⤋ ⧼ v' :: ϵ', sig, ψ ⧽ ->
  ⧼ Ψ, ϵ, Stmt.Var te s ⧽ ⤋ ⧼ ϵ', sig, ψ ⧽
| sbs_seq Ψ ϵ ϵ' ϵ'' s₁ s₂ sig₁ sig₂ ψ ψ' :
  (* TODO: handle signals *)
  ⧼ Ψ, ϵ, s₁ ⧽ ⤋ ⧼ ϵ', sig₁, ψ ⧽ ->
  ⧼ {| functs := functs Ψ
    ; cntx    := cntx Ψ
    ; extrn   := ψ |},
    ϵ', s₂ ⧽ ⤋ ⧼ ϵ'', sig₂, ψ' ⧽ ->
  ⧼ Ψ, ϵ, Stmt.Seq s₁ s₂ ⧽ ⤋ ⧼ ϵ'', sig₂, ψ' ⧽
| sbs_cond Ψ ϵ ϵ' e s₁ s₂ (b : bool) sig ψ ψ' :
  ⟨ ϵ, e ⟩ ⇓ b ->
  ⧼ Ψ, ϵ, if b then s₁ else s₂ ⧽ ⤋ ⧼ ϵ', sig, ψ ⧽ ->
  ⧼ Ψ, ϵ, If e Then s₁ Else s₂ ⧽ ⤋ ⧼ ϵ', sig, ψ' ⧽
where "⧼ Ψ , ϵ , s ⧽ ⤋ ⧼ ϵ' , sig , ψ ⧽"
  := (stmt_big_step Ψ ϵ s ϵ' sig ψ) : type_scope.
                                        
(*with bigstep_state_machine
  : parser_eval_env -> list Val.v -> Parser.state ->
    list Val.v -> Parser.state -> extern_state -> Prop :=
| bsm_final Φ ϵ curr :
  final_state curr ->
  Δ ( Φ, ϵ, curr ) ⇝ ( ϵ, curr, pextrn Φ )
| bsm_intermediate Φ ϵ ϵ' ϵ'' curr next final block ψ ψ' :
  intermediate_state curr ->
  get_state_block (pstart Φ) (pstates Φ) curr = Some block ->
  (* TODO: fix parser eval *)
  (*δ ( Φ, ϵ, block ) ⇝ ( ϵ', next, ψ ) ->*)
  Δ ( {| pextrn  := ψ
      ;  pfuncts := pfuncts Φ
      ;  pstart  := pstart Φ
      ;  pstates := pstates Φ
      ;  parsers := parsers Φ |},
      ϵ', next ) ⇝ ( ϵ'', final, ψ' ) ->
  Δ ( Φ, ϵ', curr ) ⇝ ( ϵ'', final, ψ' )
where "'Δ' ( Φ , ϵ , curr ) ⇝ ( ϵ' , final , ψ )"
  := (bigstep_state_machine Φ ϵ curr ϵ' final ψ) : type_scope.*)

Local Close Scope stmt_scope.
