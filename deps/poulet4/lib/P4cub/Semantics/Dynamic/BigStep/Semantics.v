Require Import Coq.ZArith.BinInt
(*Poulet4.P4cub.Semantics.Climate*)
        Poulet4.P4cub.Syntax.CubNotations.
From Poulet4.P4cub.Semantics.Dynamic Require Import
     BigStep.Value.Value.
From Poulet4.P4cub.Semantics.Dynamic Require Export
     BigStep.ExprUtil BigStep.ValEnvUtil BigStep.InstUtil.
Import (*String*)
  Val.ValueNotations ExprNotations
  Val.LValueNotations StmtNotations.

(** * Big-step Semantics. *)

(* TODO: needs to use [P4light/Architecture/Target.v]. *)

(** Expression evaluation. *)

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
| ebs_struct es oe vs ob :
  relop (expr_big_step ϵ) oe (option_map Val.Bool ob) ->
  Forall2 (expr_big_step ϵ) es vs ->
  ⟨ ϵ, Expr.Struct es oe ⟩ ⇓ Val.Struct vs ob
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
  | CFunction (return_type : option Expr.t)
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

Record parser_eval_env : Set := {
    pextrn  : extern_state;
    pfuncts : fenv;
    pstart  : Parser.state_block      (** start state block. *);
    pstates : list Parser.state_block (** user-defined states *);
    parsers : pienv (** parser instance closure. *);
    (* TODO: needs a DeBruijn env for extern instances. *)}.

(** Statement evaluation :
    Given a statement evaluation environment [Ψ]
    and a De Bruijn value environment [ϵ],
    a statement [s] is evaluated to
    a new value environment [ϵ'],
    a signal [sig], and a new extern state [ψ]. *)
Reserved Notation "⧼ Ψ , ϵ , s ⧽ ⤋ ⧼ ϵ' , sig , ψ ⧽"
         (at level 80, no associativity).

(** Parser-state-machine evaluation :
    Given a parser evaluation environment [Φ]
    and a De Bruijn value environment [ϵ],
    a parser-state-machine starting from state [curr]
    evaluates to a new value environment [ϵ'],
    a final state [final], and an extern state [ψ]. *)
Reserved Notation "'Δ' ( Φ , ϵ , curr ) ⇝ ( ϵ' , final , ψ ) "
         (at level 80, no associativity).

(** Parser-state-block evaluation :
    Given a parser evaluation environment [Φ]
    and a De Bruijn value environment [ϵ],
    a single parser state block [currb]
    evaluates to a new environment [ϵ'],
    a state [next], and an extern state [ψ]. *)
Reserved Notation "'δ' ( Φ , ϵ , currb ) ⇝ ( ϵ' , next , ψ )"
         (at level 80, no associativity).

(** Fetch the next state-block to evaluate. *)
Definition get_state_block
           (strt : Parser.state_block)
           (states : list Parser.state_block)
           (next : AST.Parser.state) : option Parser.state_block :=
  match next with
  | Parser.Start  => Some strt
  | Parser.Name x => nth_error states x
  | _             => None
  end.

Local Open Scope climate_scope.
Local Open Scope stmt_scope.

Inductive stmt_big_step
  : stmt_eval_env -> list Val.v -> Stmt.s ->
    list Val.v -> signal -> extern_state -> Prop :=
| sbs_skip Ψ ϵ :
  ⧼ Ψ, ϵ, Stmt.Skip ⧽ ⤋ ⧼ ϵ, Cont, tt ⧽
| sbs_seq_cont Ψ ϵ ϵ' ϵ'' s₁ s₂ sig ψ₁ ψ₂ :
  ⧼ Ψ, ϵ, s₁ ⧽ ⤋ ⧼ ϵ', Cont, ψ₁ ⧽ ->
  ⧼ {| functs := functs Ψ
    ; cntx    := cntx Ψ
    ; extrn   := ψ₁ |},
    ϵ', s₂ ⧽ ⤋ ⧼ ϵ', sig, ψ₂ ⧽ ->
  ⧼ Ψ, ϵ, s₁ `; s₂ ⧽ ⤋ ⧼ ϵ'', sig, ψ₂ ⧽
| sbs_seq_interrupt Ψ ϵ ϵ' s₁ s₂ sig ψ :
  interrupt sig ->
  ⧼ Ψ, ϵ, s₁ ⧽ ⤋ ⧼ ϵ', sig, ψ ⧽ ->
  ⧼ Ψ, ϵ, s₁ `; s₂ ⧽ ⤋ ⧼ ϵ', sig, ψ ⧽
| sbs_vardecl Ψ ϵ eo v :
  match eo with
  | inr e => ⟨ ϵ, e ⟩ ⇓ v
  | inl τ => v_of_t τ = Some v
  end ->
  ⧼ Ψ, ϵ, Stmt.Var eo ⧽ ⤋ ⧼ v :: ϵ, Cont, tt ⧽
| sbs_assign Ψ ϵ e₁ e₂ lv v :
  e₁ ⇓ₗ lv ->
  ⟨ ϵ, e₂ ⟩ ⇓ v ->
  ⧼ Ψ, ϵ, e₁ `:= e₂ ⧽ ⤋ ⧼ lv_update lv v ϵ, Cont, tt ⧽
| sbs_exit Ψ ϵ :
  ⧼ Ψ, ϵ, Stmt.Exit ⧽ ⤋ ⧼ ϵ, Exit, tt ⧽
| sbs_return Ψ ϵ eo vo :
  relop (expr_big_step ϵ) eo vo ->
  ⧼ Ψ, ϵ, Stmt.Return eo ⧽ ⤋ ⧼ ϵ, Rtrn vo, tt ⧽
| sbs_cond Ψ ϵ ϵ' e s₁ s₂ (b : bool) sig ψ :
  ⟨ ϵ, e ⟩ ⇓ b ->
  ⧼ Ψ, ϵ, if b then s₁ else s₂ ⧽ ⤋ ⧼ ϵ', sig, ψ ⧽ ->
  ⧼ Ψ, ϵ, If e Then s₁ Else s₂ ⧽
    ⤋ ⧼ List.skipn (List.length ϵ' - List.length ϵ) ϵ', sig, ψ ⧽
(* TODO: other statements *)
where "⧼ Ψ , ϵ , s ⧽ ⤋ ⧼ ϵ' , sig , ψ ⧽"
  := (stmt_big_step Ψ ϵ s ϵ' sig ψ) : type_scope.
(*
  with bigstep_state_machine
         (pkt : Paquet.t) (fs : fenv) (ϵ : epsilon) :
         pienv -> ARCH.extern_env ->
         AST.Parser.state_block -> (F.fs string (AST.Parser.state_block)) ->
         AST.Parser.state -> epsilon -> AST.Parser.state -> Paquet.t -> Prop :=
  | bsm_accept (strt : AST.Parser.state_block)
               (states : F.fs string (AST.Parser.state_block))
               (curr : AST.Parser.state) (currb : AST.Parser.state_block)
               (ϵ' : epsilon) (pkt' : Paquet.t)
               (pis : pienv) (eis : ARCH.extern_env) :
      get_state_block strt states curr = Some currb ->
      SB (pkt, fs, ϵ, pis, eis, currb) ⇝ ⟨ϵ', accept, pkt'⟩ ->
      SM (pkt, fs, ϵ, pis, eis, strt, states, curr) ⇝ ⟨ϵ', accept, pkt'⟩
  | bsm_reject (strt : AST.Parser.state_block)
               (states : F.fs string (AST.Parser.state_block))
               (curr : AST.Parser.state) (currb : AST.Parser.state_block)
               (ϵ' : epsilon) (pkt' : Paquet.t)
               (pis : pienv) (eis : ARCH.extern_env) :
      get_state_block strt states curr = Some currb ->
      SB (pkt, fs, ϵ, pis, eis, currb) ⇝ ⟨ϵ', reject, pkt'⟩ ->
      SM (pkt, fs, ϵ, pis, eis, strt, states, curr) ⇝ ⟨ϵ', reject, pkt'⟩
  | bsm_continue (strt : AST.Parser.state_block)
                 (states : F.fs string (AST.Parser.state_block))
                 (curr : AST.Parser.state) (currb : AST.Parser.state_block)
                 (next : AST.Parser.state) (final : AST.Parser.state)
                 (ϵ' ϵ'' : epsilon) (pkt' pkt'' : Paquet.t)
                 (pis : pienv) (eis : ARCH.extern_env) :
      get_state_block strt states curr = Some currb ->
      SB (pkt, fs, ϵ, pis, eis, currb) ⇝ ⟨ϵ', next, pkt'⟩ ->
      SM (pkt', fs, ϵ', pis, eis, strt, states, next) ⇝ ⟨ϵ'', final, pkt''⟩ ->
      SM (pkt, fs, ϵ, pis, eis, strt, states, curr) ⇝ ⟨ ϵ'', final, pkt''⟩
  where  "'SM' ( pkt1 , fenv , ϵ1 , pis , eis , strt , states , curr ) ⇝ ⟨ ϵ2 , final , pkt2 ⟩"
           := (bigstep_state_machine
                 pkt1 fenv ϵ1 pis eis strt states curr ϵ2 final pkt2)

  with bigstep_state_block
         (pkt : Paquet.t) (fs : fenv) (ϵ : epsilon) :
         @pienv -> ARCH.extern_env ->
         AST.Parser.state_block -> epsilon -> AST.Parser.state -> Paquet.t -> Prop :=
  | bsb_reject (s : Stmt.s) (e : AST.Parser.e)
               (ϵ' : epsilon) (pkt' : Paquet.t)
               (pis : pienv) (eis : ARCH.extern_env) :
      ⟪ pkt, fs, ϵ, Parser pis eis, s ⟫ ⤋ ⟪ ϵ', SIG_Rjct, pkt' ⟫ ->
      SB (pkt, fs, ϵ, pis, eis, &{ state{s} transition e }&) ⇝ ⟨ϵ', reject, pkt'⟩
  | bsb_cont (s : Stmt.s) (e : AST.Parser.e)
             (st : AST.Parser.state) (ϵ' : epsilon) (pkt' : Paquet.t)
             (pis : pienv) (eis : ARCH.extern_env) :
      ⟪ pkt, fs, ϵ, Parser pis eis, s ⟫ ⤋ ⟪ ϵ', C, pkt' ⟫ ->
      ⦑ ϵ', e ⦒ ⇓ st ->
      SB (pkt, fs, ϵ, pis, eis, &{ state{s} transition e }&) ⇝ ⟨ϵ', st, pkt'⟩
  where "'SB' ( pkt1 , fenv , ϵ1 , pis , eis , currb ) ⇝ ⟨ ϵ2 , next , pkt2 ⟩"
  := (bigstep_state_block pkt1 fenv ϵ1 pis eis currb ϵ2 next pkt2). *)
