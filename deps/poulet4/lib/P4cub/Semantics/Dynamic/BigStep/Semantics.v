Set Warnings "-custom-entry-overridden".
Require Import Coq.ZArith.BinInt Poulet4.P4cub.Semantics.Climate.
From Poulet4.P4cub.Semantics.Dynamic Require Import
     BigStep.Value.Value BigStep.BSPacket.
From Poulet4.P4cub.Semantics.Dynamic Require Export
     BigStep.ExprUtil BigStep.ValEnvUtil BigStep.InstUtil.
Import String.

(* TODO : correctly handle type parameters & arguments. *)

(** * Big-Step Evaluation *)

(** Notation entries. *)
Declare Custom Entry p4evalsignal.
Declare Custom Entry p4evalcontext.

(** Expression evaluation. *)
Reserved Notation "⟨ envn , e ⟩ ⇓ v"
         (at level 40, e custom p4expr, v custom p4value).

(** L-value evaluation. *)
Reserved Notation "⧠ e ⇓ lv"
         (at level 40, e custom p4expr, lv custom p4lvalue).

(** Parser-expression evaluation. *)
Reserved Notation "⦑ envn , e ⦒ ⇓ st"
         (at level 40, e custom p4prsrexpr, st custom p4prsrstate).

(** Statement evaluation. *)
Reserved Notation "⟪ pkt1 , fenv , ϵ1 , ctx , s ⟫ ⤋ ⟪ ϵ2 , sig , pkt2 ⟫"
         (at level 40, s custom p4stmt,
          ctx custom p4evalcontext,
          sig custom p4evalsignal).

(** Control-declaration evaluation. *)
Reserved Notation "⦉ ts1 , aa1 , fns , cis , eis , ϵ1 , d ⦊ ⟱  ⦉ aa2 , ts2 ⦊"
         (at level 40, d custom p4ctrldecl).

(** Top-declaration evaluation. *)
Reserved Notation
         "⦇ p1 , c1 , e1 , f1 , pi1 , ci1 , ei1 , ϵ , d ⦈ ⟱  ⦇ ei2 , ci2 , pi2 , f2 , e2 , c2 , p2 ⦈"
         (at level 40, d custom p4topdecl).

(** Parser-state-machine evaluation. *)
Reserved Notation  "'SM' ( pkt1 , fenv , ϵ1 , pis , eis , strt , states , curr ) ⇝ ⟨ ϵ2 , final , pkt2 ⟩"
         (at level 40, strt custom p4prsrstateblock,
          curr custom p4prsrstate, final custom p4prsrstate).

(** Parser-state-block evaluation. *)
Reserved Notation "'SB' ( pkt1 , fenv , ϵ1 , pis , eis , currb ) ⇝ ⟨ ϵ2 , next , pkt2 ⟩"
         (at level 40, currb custom p4prsrstateblock, next custom p4prsrstate).

Module Step.
  Export Clmt.Notations.
  Import AllCubNotations V.ValueNotations V.LValueNotations.
  Open Scope climate_scope.

  (** Statement signals. *)
  Variant signal : Type :=
  | SIG_Cont                  (* continue *)
  | SIG_Exit                  (* exit *)
  | SIG_Rtrn (v : option V.v) (* return *)
  | SIG_Rjct                  (* reject *).

  Notation "x"
    := x (in custom p4evalsignal at level 0, x constr at level 0).
  Notation "'C'" := SIG_Cont (in custom p4evalsignal at level 0).
  Notation "'X'" := SIG_Exit (in custom p4evalsignal at level 0).
  Notation "'R' 'of' v ?"
    := (SIG_Rtrn v) (in custom p4evalsignal at level 0).
  Notation "'Void'" := (SIG_Rtrn None) (in custom p4evalsignal at level 0).
  Notation "'Fruit' v" := (SIG_Rtrn (Some v)) (in custom p4evalsignal at level 0).

  (** Evidence that control-flow
      is interrupted by an exit or return statement. *)
  Variant interrupt : signal -> Prop :=
  | interrupt_exit : interrupt SIG_Exit
  | interrupt_rtrn (vo : option V.v) : interrupt (SIG_Rtrn vo)
  | interrupt_rjct : interrupt SIG_Rjct.
  (**[]*)

  (** Context for statement evaluation. *)
  Variant ctx {tags_t : Type} : Type :=
  | CAction (available_actions : @aenv tags_t)
            (available_externs : ARCH.extern_env)
  | CVoid                         (* void function *)
  | CFunction (return_type : Expr.t) (* fruitful function *)
  | CApplyBlock (control_plane_entries : @ctrl tags_t)
                (tables : @tenv tags_t)
                (available_actions : @aenv tags_t)
                (available_controls : @cienv tags_t)
                (available_externs : ARCH.extern_env) (* control apply block *)
  | CParserState (available_parsers : @pienv tags_t)
                 (available_externs : ARCH.extern_env) (* parser state *).
  (**[]*)

  Notation "x" := x (in custom p4evalcontext at level 0, x constr at level 0).
  Notation "'Action' aa eis"
    := (CAction aa eis)
         (in custom p4evalcontext at level 0).
  Notation "'Void'" := CVoid (in custom p4evalcontext at level 0).
  Notation "'Function' t"
    := (CFunction t)
         (in custom p4evalcontext at level 0, t custom p4type).
  Notation "'ApplyBlock' cps tbls aa cis eis"
    := (CApplyBlock cps tbls aa cis eis)
         (in custom p4evalcontext at level 0).
  Notation "'Parser' pis eis"
    := (CParserState pis eis)
         (in custom p4evalcontext at level 0).

  (** Expression big-step semantics. *)
  Inductive expr_big_step {tags_t : Type} (ϵ : epsilon) : Expr.e tags_t -> V.v -> Prop :=
  (* Literals. *)
  | ebs_bool (b : bool) (i : tags_t) :
      ⟨ ϵ, BOOL b @ i ⟩ ⇓ VBOOL b
  | ebs_bit (w : N) (n : Z) (i : tags_t) :
      ⟨ ϵ, w W n @ i ⟩ ⇓ w VW n
  | ebs_int (w : positive) (z : Z) (i : tags_t) :
      ⟨ ϵ, w S z @ i ⟩ ⇓ w VS z
  | ebs_var (x : string) (τ : Expr.t) (i : tags_t) (v : V.v) :
      ϵ x = Some v ->
      ⟨ ϵ, Var x:τ @ i ⟩ ⇓ v
  | ebs_slice (e : Expr.e tags_t) (hi lo : positive)
              (i : tags_t) (v' v : V.v) :
      eval_slice hi lo v = Some v' ->
      ⟨ ϵ, e ⟩ ⇓ v ->
      ⟨ ϵ, Slice e [hi:lo] @ i ⟩ ⇓ v'
  | ebs_cast (τ : Expr.t) (e : Expr.e tags_t) (i : tags_t) (v v' : V.v) :
      eval_cast τ v = Some v' ->
      ⟨ ϵ, e ⟩ ⇓ v ->
      ⟨ ϵ, Cast e:τ @ i ⟩ ⇓ v'
  | ebs_error (err : option string) (i : tags_t) :
      ⟨ ϵ, Error err @ i ⟩ ⇓ ERROR err
  | ebs_matchkind (mk : Expr.matchkind) (i : tags_t) :
      ⟨ ϵ, Matchkind mk @ i ⟩ ⇓ MATCHKIND mk
  (* Unary Operations. *)
  | ebs_uop τ (op : Expr.uop) (e : Expr.e tags_t) (i : tags_t) (v v' : V.v) :
      eval_uop op v = Some v' ->
      ⟨ ϵ, e ⟩ ⇓ v ->
      ⟨ ϵ, UOP op e : τ @ i ⟩ ⇓ v'
  (* Binary Operations. *)
  | ebs_bop τ (op : Expr.bop) (e1 e2 : Expr.e tags_t)
            (i : tags_t) (v v1 v2 : V.v) :
      eval_bop op v1 v2 = Some v ->
      ⟨ ϵ, e1 ⟩ ⇓ v1 ->
      ⟨ ϵ, e2 ⟩ ⇓ v2 ->
      ⟨ ϵ, BOP e1 op e2 : τ @ i ⟩ ⇓ v
  (* Structs *)
  | ebs_mem τ (e : Expr.e tags_t) (x : string)
            (i : tags_t) (v v' : V.v) :
      eval_member x v = Some v' ->
      ⟨ ϵ, e ⟩ ⇓ v ->
      ⟨ ϵ, Mem e dot x : τ @ i ⟩ ⇓ v'
  | ebs_tuple (es : list (Expr.e tags_t)) (i : tags_t)
              (vs : list (V.v)) :
      Forall2 (fun e v => ⟨ ϵ, e ⟩ ⇓ v) es vs ->
      ⟨ ϵ, tup es @ i ⟩ ⇓ TUPLE vs
  | ebs_struct_lit (efs : F.fs string (Expr.e tags_t))
                (i : tags_t) (vfs : F.fs string V.v) :
      F.relfs (fun e v => ⟨ ϵ, e ⟩ ⇓ v) efs vfs ->
      ⟨ ϵ, struct { efs } @ i ⟩ ⇓ STRUCT { vfs }
  | ebs_hdr_lit (efs : F.fs string (Expr.e tags_t))
                (e : Expr.e tags_t) (i : tags_t) (b : bool)
                (vfs : F.fs string V.v) :
      F.relfs (fun e v => ⟨ ϵ, e ⟩ ⇓ v) efs vfs ->
      ⟨ ϵ, e ⟩ ⇓ VBOOL b ->
      ⟨ ϵ, hdr { efs } valid:=e @ i ⟩ ⇓ HDR { vfs } VALID:=b
  | ebs_hdr_stack (ts : F.fs string (Expr.t))
                  (hs : list (Expr.e tags_t))
                  (ni : Z) (i : tags_t)
                  (vss : list (bool * F.fs string (V.v))) :
      Forall2
        (fun e bvs =>
           let b := fst bvs in
           let vs := snd bvs in
           ⟨ ϵ, e ⟩ ⇓ HDR { vs } VALID:=b)
        hs vss ->
      ⟨ ϵ, Stack hs:ts nextIndex:=ni @ i ⟩ ⇓ STACK vss:ts NEXT:=ni
  | ebs_access (e : Expr.e tags_t) (i : tags_t)
               (index ni : Z)
               (ts : F.fs string (Expr.t))
               (vss : list (bool * F.fs string (V.v)))
               (b : bool) (vs : F.fs string (V.v)) :
      nth_error vss (Z.to_nat index) = Some (b,vs) ->
      ⟨ ϵ, e ⟩ ⇓ STACK vss:ts NEXT:=ni ->
      ⟨ ϵ, Access e[index] : ts @ i ⟩ ⇓ HDR { vs } VALID:=b
  where "⟨ ϵ , e ⟩ ⇓ v" := (expr_big_step ϵ e v).
  (**[]*)

  (** L-value evaluation. *)
  Inductive lvalue_big_step {tags_t : Type} : Expr.e tags_t -> V.lv -> Prop :=
  | lvbs_var (x : string) (τ : Expr.t) (i : tags_t) :
      ⧠ Var x:τ @ i ⇓ VAR x
  | lvbs_slice (e : Expr.e tags_t)
               (hi lo : positive) (i : tags_t) (lv : V.lv) :
      ⧠ e ⇓ lv ->
      ⧠ Slice e [hi:lo] @ i ⇓ SLICE lv [hi:lo]
  | lvbs_member τ (e : Expr.e tags_t) (x : string)
                (i : tags_t) (lv : V.lv) :
      ⧠ e ⇓ lv ->
      ⧠ Mem e dot x : τ @ i ⇓ lv DOT x
  | lvbs_access ts (e : Expr.e tags_t) (i : tags_t)
                (lv : V.lv) (n : Z) :
      let w := 32%positive in
      ⧠ e ⇓ lv ->
      ⧠ Access e[n] : ts @ i ⇓ ACCESS lv[n]
  where "⧠ e ⇓ lv" := (lvalue_big_step e lv).
  (**[]*)

  (** Parser-expression evaluation. *)
  Inductive parser_expr_big_step
            {tags_t} (ϵ : epsilon) : AST.Parser.e tags_t -> AST.Parser.state -> Prop :=
  | pebs_goto (st : AST.Parser.state) (i : tags_t) :
      ⦑ ϵ, goto st @ i ⦒ ⇓ st
  | pebs_select (e : Expr.e tags_t) (def : AST.Parser.e tags_t)
                (cases : F.fs AST.Parser.pat (AST.Parser.e tags_t))
                (i : tags_t) (v : V.v) (st_def : AST.Parser.state)
                (vcases : F.fs AST.Parser.pat AST.Parser.state) :
      ⟨ ϵ, e ⟩ ⇓ v ->
      Forall2
        (fun pe ps =>
           let p := fst pe in
           let p' := fst ps in
           let e := snd pe in
           let s := snd ps in
           p = p' /\ ⦑ ϵ, e ⦒ ⇓ s)
        cases vcases ->
      ⦑ ϵ, def ⦒ ⇓ st_def ->
      let st := match F.find_value (fun p => match_pattern p v) vcases with
                | None => st_def
                | Some st => st
                end in
      ⦑ ϵ, select e { cases } default:=def @ i ⦒ ⇓ st
  where "⦑ envn , e ⦒ ⇓ st"
          := (parser_expr_big_step envn e st).
  (**[]*)

  (** Fetch the next state-block to evaluate. *)
  Definition get_state_block {tags_t : Type}
             (strt : AST.Parser.state_block tags_t)
             (states : F.fs string (AST.Parser.state_block tags_t))
             (curr : AST.Parser.state) : option (AST.Parser.state_block tags_t) :=
    match curr with
    | ={ start }= => Some strt
    | ={ δ x }=  => F.get x states
    | _ => None end.

  (** Statement big-step semantics. *)
  Inductive stmt_big_step
            {tags_t : Type} (pkt : Paquet.t) (fs : fenv) (ϵ : epsilon) :
    ctx -> Stmt.s tags_t -> epsilon -> signal -> Paquet.t -> Prop :=
  | sbs_skip (i : tags_t) (c : ctx) :
      ⟪ pkt, fs, ϵ, c, skip @ i ⟫ ⤋ ⟪ ϵ, C, pkt ⟫
  | sbs_seq_cont (s1 s2 : Stmt.s tags_t) (i : tags_t)
                 (ϵ' ϵ'' : epsilon) (sig : signal)
                 (pkt' pkt'' : Paquet.t) (c : ctx) :
      ⟪ pkt,  fs, ϵ,  c, s1 ⟫ ⤋ ⟪ ϵ',  C, pkt' ⟫ ->
      ⟪ pkt', fs, ϵ', c, s2 ⟫ ⤋ ⟪ ϵ'', sig, pkt'' ⟫ ->
      ⟪ pkt,  fs, ϵ,  c,  s1 ; s2 @ i ⟫ ⤋ ⟪ ϵ'', sig, pkt'' ⟫
  | sbs_seq_interrupt (s1 s2 : Stmt.s tags_t) (i : tags_t)
                      (ϵ' : epsilon) (sig : signal)
                      (pkt' : Paquet.t) (c : ctx) :
      interrupt sig ->
      ⟪ pkt, fs, ϵ, c, s1 ⟫ ⤋ ⟪ ϵ', sig, pkt' ⟫ ->
      ⟪ pkt, fs, ϵ, c, s1 ; s2 @ i ⟫ ⤋ ⟪ ϵ', sig, pkt' ⟫
  | sbs_block_cont (s : Stmt.s tags_t) (ϵ' : epsilon)
                   (pkt' : Paquet.t) (c : ctx) :
      ⟪ pkt, fs, ϵ, c, s ⟫ ⤋ ⟪ ϵ', C, pkt' ⟫ ->
      ⟪ pkt, fs, ϵ, c, b{ s }b ⟫ ⤋ ⟪ ϵ ≪ ϵ', C, pkt' ⟫
  | sbs_block_interrupt (s : Stmt.s tags_t) (ϵ' : epsilon)
                        (sig : signal) (pkt' : Paquet.t) (c : ctx) :
      interrupt sig ->
      ⟪ pkt, fs, ϵ, c, s ⟫ ⤋ ⟪ ϵ', sig, pkt' ⟫ ->
      ⟪ pkt, fs, ϵ, c, b{ s }b ⟫ ⤋ ⟪ ϵ ≪ ϵ', sig, pkt' ⟫
  | sbs_vardecl (x : string) (eo : Expr.t + Expr.e tags_t)
                (i : tags_t) (v : V.v) (c : ctx) :
      match eo with
      | inr e => ⟨ ϵ, e ⟩ ⇓ v
      | inl τ => vdefault τ = Some v
      end ->
      ⟪ pkt, fs, ϵ, c, var x with eo @ i ⟫ ⤋ ⟪ x ↦ v ,, ϵ, C, pkt ⟫
  | sbs_assign (e1 e2 : Expr.e tags_t) (i : tags_t)
               (lv : V.lv) (v : V.v) (ϵ' : epsilon) (c : ctx) :
      lv_update lv v ϵ = ϵ' ->
      ⧠ e1 ⇓ lv ->
      ⟨ ϵ, e2 ⟩ ⇓ v ->
      ⟪ pkt, fs, ϵ, c, asgn e1 := e2 @ i ⟫ ⤋ ⟪ ϵ', C, pkt ⟫
  | sbs_exit (i : tags_t) (c : ctx) :
      ⟪ pkt, fs, ϵ, c, exit @ i ⟫ ⤋ ⟪ ϵ, X, pkt ⟫
  | sbs_retvoid (i : tags_t) :
      ⟪ pkt, fs, ϵ, Void, return None @ i ⟫ ⤋ ⟪ ϵ, Void, pkt ⟫
  | sbs_retfruit (τ : Expr.t) (e : Expr.e tags_t)
                 (i : tags_t) (v : V.v) :
      ⟨ ϵ, e ⟩ ⇓ v ->
      let eo := Some e in
      ⟪ pkt, fs, ϵ, Function τ, return eo @ i ⟫ ⤋ ⟪ ϵ, Fruit v, pkt ⟫
  | sbs_cond_true (guard : Expr.e tags_t)
                  (tru fls : Stmt.s tags_t) (i : tags_t)
                  (ϵ' : epsilon) (sig : signal) (c : ctx) :
      ⟨ ϵ, guard ⟩ ⇓ TRUE ->
      ⟪ pkt, fs, ϵ, c, tru ⟫ ⤋ ⟪ ϵ', sig, pkt ⟫ ->
      ⟪ pkt, fs, ϵ, c, if guard then tru else fls @ i ⟫
        ⤋ ⟪ ϵ', sig, pkt ⟫
  | sbs_cond_false (guard : Expr.e tags_t)
                   (tru fls : Stmt.s tags_t) (i : tags_t)
                   (ϵ' : epsilon) (sig : signal) (c : ctx) :
      ⟨ ϵ, guard ⟩ ⇓ FALSE ->
      ⟪ pkt, fs, ϵ, c, fls ⟫ ⤋ ⟪ ϵ', sig, pkt ⟫ ->
      ⟪ pkt, fs, ϵ, c, if guard then tru else fls @ i ⟫
        ⤋ ⟪ ϵ', sig, pkt ⟫
  | sbs_action_call (args : Expr.args tags_t)
                    (argsv : V.argsv)
                    (a : string) (i : tags_t)
                    (body : Stmt.s tags_t)
                    (aa aclosure : aenv) (fclosure : fenv)
                    (closure ϵ' ϵ'' ϵ''' : epsilon)
                    (exts : ARCH.extern_env) (c : ctx) :
      match c with
      | CAction aa _
      | CApplyBlock _ _ aa _ _ => Some aa
      | _ => None
      end = Some aa ->
      (* Looking up action. *)
      aa a = Some (ADecl closure fclosure aclosure exts body) ->
      (* Argument evaluation. *)
      F.relfs
        (rel_paramarg
           (fun e v  => ⟨ ϵ, e ⟩ ⇓ v)
           (fun e lv => ⧠ e ⇓ lv))
        args argsv ->
      (* Copy-in. *)
      copy_in argsv ϵ closure = ϵ' ->
      (* Action evaluation *)
      ⟪ pkt, fclosure, ϵ', Action aclosure exts, body ⟫ ⤋ ⟪ ϵ'', Void, pkt ⟫ ->
      (* Copy-out *)
      copy_out argsv ϵ'' ϵ = ϵ''' ->
      ⟪ pkt, fs, ϵ, c, calling a with args @ i ⟫ ⤋ ⟪ ϵ''', C, pkt ⟫
  | sbs_void_call (args : Expr.args tags_t)
                  (argsv : V.argsv)
                  (f : string) (i : tags_t)
                  (body : Stmt.s tags_t) (fclosure : fenv)
                  (closure ϵ' ϵ'' ϵ''' : epsilon) (c : ctx) :
      (* Looking up function. *)
      fs f = Some (FDecl closure fclosure body) ->
      (* Argument evaluation. *)
      F.relfs
        (rel_paramarg
           (fun e v  => ⟨ ϵ, e ⟩ ⇓ v)
           (fun e lv => ⧠ e ⇓ lv))
        args argsv ->
      (* Copy-in. *)
      copy_in argsv ϵ closure = ϵ' ->
      (* Function evaluation *)
      ⟪ pkt, fclosure, ϵ', Void, body ⟫ ⤋ ⟪ ϵ'', Void, pkt ⟫ ->
      (* Copy-out *)
      copy_out argsv ϵ'' ϵ = ϵ''' ->
      ⟪ pkt, fs, ϵ, c, call f <[]> (args) @ i ⟫ ⤋ ⟪ ϵ''', C, pkt ⟫
  | sbs_fruit_call (args : Expr.args tags_t)
                   (argsv : V.argsv)
                   (f : string) (τ : Expr.t)
                   (e : Expr.e tags_t) (i : tags_t)
                   (v : V.v) (lv : V.lv)
                   (body : Stmt.s tags_t) (fclosure : fenv)
                   (closure ϵ' ϵ'' ϵ''' ϵ'''' : epsilon) (c : ctx) :
      (* Looking up function. *)
      fs f = Some (FDecl closure fclosure body) ->
      (* Argument evaluation. *)
      F.relfs
        (rel_paramarg
           (fun e v => ⟨ ϵ, e ⟩ ⇓ v)
           (fun e lv => ⧠ e ⇓ lv))
        args argsv ->
      (* Copy-in. *)
      copy_in argsv ϵ closure = ϵ' ->
      (* Lvalue Evaluation. *)
      ⧠ e ⇓ lv ->
      (* Function evaluation. *)
      ⟪ pkt, fclosure, ϵ', Function τ, body ⟫ ⤋ ⟪ ϵ'', Fruit v, pkt ⟫ ->
      (* Copy-out. *)
      copy_out argsv ϵ'' ϵ = ϵ''' ->
      (* Assignment to lvalue. *)
      lv_update lv v ϵ''' = ϵ'''' ->
      ⟪ pkt, fs, ϵ, c,
        let e := call f <[]> (args) @ i ⟫ ⤋ ⟪ ϵ'''', C, pkt ⟫
  | sbs_ctrl_apply (args : Expr.args tags_t) (eargs : F.fs string string)
                   (argsv : V.argsv) (x : string) (i : tags_t)
                   (body : Stmt.s tags_t) (fclosure : fenv) (cis cis' : cienv)
                   (tbl tblclosure : tenv) (aa aclosure : aenv)
                   (cpes : ctrl) (exts eis : ARCH.extern_env)
                   (closure ϵ' ϵ'' ϵ''' : epsilon) (pkt' : Paquet.t) :
      (* TODO: evaluate with extern instance arguments *)
      (* Instance lookup. *)
      cis x =
      Some (CInst closure fclosure cis' tblclosure aclosure exts body) ->
      (* Argument evaluation. *)
      F.relfs
        (rel_paramarg
           (fun e v => ⟨ ϵ, e ⟩ ⇓ v)
           (fun e lv => ⧠ e ⇓ lv))
        args argsv ->
      (* Copy-in. *)
      copy_in argsv ϵ closure = ϵ' ->
      (* Apply block evaluation. *)
      ⟪ pkt, fclosure, ϵ', ApplyBlock cpes tblclosure aclosure cis' exts,  body ⟫
        ⤋ ⟪ ϵ'', Void, pkt' ⟫ ->
      (* Copy-out. *)
      copy_out argsv ϵ'' ϵ = ϵ''' ->
      ⟪ pkt, fs, ϵ, ApplyBlock cpes tbl aa cis eis, apply x with eargs & args @ i ⟫
        ⤋ ⟪ ϵ''', C, pkt' ⟫
  | sbs_prsr_accept_apply (args : Expr.args tags_t) (eargs : F.fs string string)
                          (argsv : V.argsv) (x : string) (i : tags_t)
                          (strt : AST.Parser.state_block tags_t)
                          (states : F.fs string (AST.Parser.state_block tags_t))
                          (fclosure : fenv) (pis pis' : pienv)
                          (exts eis : ARCH.extern_env)
                          (closure ϵ' ϵ'' ϵ''' : epsilon) (pkt' : Paquet.t) :
      (* TODO: evaluate with extern instance arguments *)
      (* Instance lookup *)
      pis x = Some (PInst closure fclosure pis' exts strt states) ->
      (* Argument evaluation *)
      F.relfs
        (rel_paramarg
           (fun e v => ⟨ ϵ, e ⟩ ⇓ v)
           (fun e lv => ⧠ e ⇓ lv))
        args argsv ->
      (* Copy-in *)
      copy_in argsv ϵ closure = ϵ' ->
      (* state machine evaluation *)
      SM (pkt, fclosure, ϵ', pis', exts, strt, states, ={start}=)
       ⇝ ⟨ϵ'', ={accept}=, pkt'⟩ ->
      (* copy-out *)
      copy_out argsv ϵ'' ϵ = ϵ''' ->
      ⟪ pkt, fs, ϵ, Parser pis eis, apply x with eargs & args @ i ⟫ ⤋ ⟪ ϵ''', C, pkt' ⟫
  | sbs_prsr_reject_apply (args : Expr.args tags_t) (eargs : F.fs string string)
                          (argsv : V.argsv) (x : string) (i : tags_t)
                          (strt : AST.Parser.state_block tags_t)
                          (states : F.fs string (AST.Parser.state_block tags_t))
                          (fclosure : fenv) (pis pis' : pienv)
                          (closure ϵ' ϵ'' ϵ''' : epsilon)
                          (pkt' : Paquet.t) (exts eis : ARCH.extern_env) :
      (* TODO: evaluate with extern instance arguments *)
      (* Instance lookup *)
      pis x = Some (PInst closure fclosure pis' exts strt states) ->
      (* Argument evaluation *)
      F.relfs
        (rel_paramarg
           (fun e v => ⟨ ϵ, e ⟩ ⇓ v)
           (fun e lv => ⧠ e ⇓ lv))
        args argsv ->
      (* Copy-in *)
      copy_in argsv ϵ closure = ϵ' ->
      (* state machine evaluation *)
      SM (pkt, fclosure, ϵ', pis', exts, strt, states, ={start}=) ⇝ ⟨ϵ'', reject, pkt'⟩ ->
      (* copy-out *)
      copy_out argsv ϵ'' ϵ = ϵ''' ->
      ⟪ pkt, fs, ϵ, Parser pis eis, apply x with eargs & args @ i ⟫ ⤋ ⟪ ϵ''', SIG_Rjct, pkt' ⟫
  | sbs_invoke (x : string) (i : tags_t)
               (es : entries)
               (ky : list (Expr.e tags_t * Expr.matchkind))
               (acts : list (string))
               (vky : list (V.v * Expr.matchkind))
               (a : string) (args : Expr.args tags_t)
               (ϵ' : epsilon) (sig : signal)
               (cp : ctrl) (ts : tenv) (aa : aenv)
               (cis : cienv) (eis : ARCH.extern_env) :
      (* Get control-plane entries. *)
      cp x = Some es ->
      (* Get appropriate table. *)
      ts x = Some {|Control.table_key:=ky; Control.table_actions:=acts|} ->
      (* Evaluate key. *)
      Forall2 (fun '(k,_) '(v,_) => ⟨ ϵ, k ⟩ ⇓ v) ky vky ->
      (* Get action and arguments.
         Black box, need extra assumption for soundness. *)
      es vky acts = (a,args) ->
      (* Evaluate associated action. *)
      ⟪ pkt, fs, ϵ, ApplyBlock cp ts aa cis eis, calling a with args @ i ⟫
        ⤋ ⟪ ϵ', sig, pkt ⟫ ->
      ⟪ pkt, fs, ϵ, ApplyBlock cp ts aa cis eis, invoke x @ i ⟫ ⤋ ⟪ ϵ', sig, pkt ⟫
  | sbs_extern_method_call (x mthd : string) (i : tags_t)
                           (args : Expr.args tags_t)
                           (eo : option (Expr.e tags_t)) (lvo : option V.lv)
                           (argsv : F.fs string (paramarg V.v V.lv))
                           disp (** dispatch method *)
                           (cls cls'' : Clmt.t string ValuePacket.E) (pkt' : Paquet.t)
                           (exts : ARCH.extern_env) (c : ctx) :
      match c with
      | CParserState _ exts
      | CAction _ exts
      | CApplyBlock _ _ _ _ exts => Some exts
      | _ => None
      end = Some exts ->
      (* Get extern instance. *)
      exts x =
      Some {| ARCH.closure := cls;
              ARCH.dispatch_method := disp; |} ->
      (* Evaluate arguments. *)
      F.relfs
        (rel_paramarg
           (fun e v => ⟨ ϵ, e ⟩ ⇓ v)
           (fun e lv => ⧠ e ⇓ lv))
        args argsv ->
      (* Evaluate lvalue. *)
      relop (fun e lv => ⧠ e ⇓ lv) eo lvo ->
      (** Copy-in. *)
      let cls' := copy_in argsv ϵ cls in
      (* Evaluate extern method call. *)
      disp mthd {|paramargs:=argsv; rtrns:=lvo|} cls' pkt = (inl cls'', pkt') ->
      (* Copy-out. *)
      let ϵ' := copy_out argsv cls'' ϵ in
      ⟪ pkt, fs, ϵ, c,
        extern x calls mthd <[]> (args) gives eo @ i ⟫ ⤋ ⟪ ϵ', C, pkt' ⟫
  where "⟪ pkt1 , fs , ϵ1 , ctx , s ⟫ ⤋ ⟪ ϵ2 , sig , pkt2 ⟫"
          := (stmt_big_step pkt1 fs ϵ1 ctx s ϵ2 sig pkt2)

  with bigstep_state_machine
         {tags_t : Type} (pkt : Paquet.t) (fs : fenv) (ϵ : epsilon) :
         pienv -> ARCH.extern_env ->
         AST.Parser.state_block tags_t -> (F.fs string (AST.Parser.state_block tags_t)) ->
         AST.Parser.state -> epsilon -> AST.Parser.state -> Paquet.t -> Prop :=
  | bsm_accept (strt : AST.Parser.state_block tags_t)
               (states : F.fs string (AST.Parser.state_block tags_t))
               (curr : AST.Parser.state) (currb : AST.Parser.state_block tags_t)
               (ϵ' : epsilon) (pkt' : Paquet.t)
               (pis : pienv) (eis : ARCH.extern_env) :
      get_state_block strt states curr = Some currb ->
      SB (pkt, fs, ϵ, pis, eis, currb) ⇝ ⟨ϵ', accept, pkt'⟩ ->
      SM (pkt, fs, ϵ, pis, eis, strt, states, curr) ⇝ ⟨ϵ', accept, pkt'⟩
  | bsm_reject (strt : AST.Parser.state_block tags_t)
               (states : F.fs string (AST.Parser.state_block tags_t))
               (curr : AST.Parser.state) (currb : AST.Parser.state_block tags_t)
               (ϵ' : epsilon) (pkt' : Paquet.t)
               (pis : pienv) (eis : ARCH.extern_env) :
      get_state_block strt states curr = Some currb ->
      SB (pkt, fs, ϵ, pis, eis, currb) ⇝ ⟨ϵ', reject, pkt'⟩ ->
      SM (pkt, fs, ϵ, pis, eis, strt, states, curr) ⇝ ⟨ϵ', reject, pkt'⟩
  | bsm_continue (strt : AST.Parser.state_block tags_t)
                 (states : F.fs string (AST.Parser.state_block tags_t))
                 (curr : AST.Parser.state) (currb : AST.Parser.state_block tags_t)
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
         {tags_t : Type} (pkt : Paquet.t) (fs : fenv) (ϵ : epsilon) :
         @pienv tags_t -> ARCH.extern_env ->
         AST.Parser.state_block tags_t -> epsilon -> AST.Parser.state -> Paquet.t -> Prop :=
  | bsb_reject (s : Stmt.s tags_t) (e : AST.Parser.e tags_t)
               (ϵ' : epsilon) (pkt' : Paquet.t)
               (pis : pienv) (eis : ARCH.extern_env) :
      ⟪ pkt, fs, ϵ, Parser pis eis, s ⟫ ⤋ ⟪ ϵ', SIG_Rjct, pkt' ⟫ ->
      SB (pkt, fs, ϵ, pis, eis, &{ state{s} transition e }&) ⇝ ⟨ϵ', reject, pkt'⟩
  | bsb_cont (s : Stmt.s tags_t) (e : AST.Parser.e tags_t)
             (st : AST.Parser.state) (ϵ' : epsilon) (pkt' : Paquet.t)
             (pis : pienv) (eis : ARCH.extern_env) :
      ⟪ pkt, fs, ϵ, Parser pis eis, s ⟫ ⤋ ⟪ ϵ', C, pkt' ⟫ ->
      ⦑ ϵ', e ⦒ ⇓ st ->
      SB (pkt, fs, ϵ, pis, eis, &{ state{s} transition e }&) ⇝ ⟨ϵ', st, pkt'⟩
  where "'SB' ( pkt1 , fenv , ϵ1 , pis , eis , currb ) ⇝ ⟨ ϵ2 , next , pkt2 ⟩"
  := (bigstep_state_block pkt1 fenv ϵ1 pis eis currb ϵ2 next pkt2).


  (** Control declaration big-step semantics. *)
  Inductive ctrldecl_big_step
            {tags_t : Type} (tbls : tenv) (aa : aenv)
            (fns : fenv) (cis : @cienv tags_t) (eis : ARCH.extern_env) (ϵ : epsilon)
    : Control.d tags_t -> aenv -> tenv -> Prop :=
  | cdbs_action (a : string) (params : Expr.params)
                (body : Stmt.s tags_t) (i : tags_t) :
      let aa' := Clmt.bind a (ADecl ϵ fns aa eis body) aa in
      ⦉ tbls, aa, fns, cis, eis, ϵ, action a (params) {body} @ i ⦊
        ⟱  ⦉ aa', tbls ⦊
  | cdbs_table (t : string)
               (kys : list
                        (Expr.e tags_t * Expr.matchkind))
               (actns : list (string))
               (i : tags_t) :
      let tbl := {|Control.table_key:=kys; Control.table_actions:=actns|} in
      ⦉ tbls, aa, fns, cis, eis, ϵ, table t key:=kys actions:=actns @ i ⦊
        ⟱  ⦉ aa, t ↦ tbl,, tbls ⦊
  | cdbs_seq (d1 d2 : Control.d tags_t) (i : tags_t)
             (aa' aa'' : aenv) (tbls' tbls'' : tenv) :
      ⦉ tbls,  aa,  fns, cis, eis, ϵ, d1 ⦊ ⟱  ⦉ aa',  tbls'  ⦊ ->
      ⦉ tbls', aa', fns, cis, eis, ϵ, d2 ⦊ ⟱  ⦉ aa'', tbls'' ⦊ ->
      ⦉ tbls,  aa,  fns, cis, eis, ϵ, d1 ;c; d2 @ i ⦊
        ⟱  ⦉ aa'', tbls'' ⦊
  where "⦉ ts1 , aa1 , fns , cis , eis , ϵ1 , d ⦊ ⟱  ⦉ aa2 , ts2 ⦊"
          := (ctrldecl_big_step ts1 aa1 fns cis eis ϵ1 d aa2 ts2).
  (**[]*)

  Module TP := TopDecl.
  
  (** Top-level declaration big-step semantics. *)
  Inductive topdecl_big_step {tags_t : Type}
            (ps : penv) (cs : cenv) (es : eenv)
            (fns : fenv) (pis : pienv) (cis : cienv)
            (eis : ARCH.extern_env) (ϵ : epsilon)
    : TopDecl.d tags_t -> ARCH.extern_env -> cienv -> pienv ->
      fenv -> @eenv tags_t -> cenv -> penv -> Prop :=
  | dbs_instantiate_ctrl (c x : string) (i : tags_t)
                         (cargs : Expr.constructor_args tags_t)
                         (vargs : F.fs string (V.v + cinst))
                         (ctrlclosure : cenv) (fclosure : fenv)
                         (ciclosure cis' : cienv) (eis' : ARCH.extern_env)
                         (body : Control.d tags_t) (applyblk : Stmt.s tags_t)
                         (closure ϵ' ϵ'' : epsilon) (tbls : tenv) (aa : aenv) :
      cs c =
      Some (CDecl ctrlclosure closure fclosure ciclosure eis body applyblk) ->
      F.relfs
        (fun carg v =>
           match carg,v with
           | Expr.CAExpr e, inl v     => ⟨ ϵ, e ⟩ ⇓ v
           | Expr.CAName c, inr cinst => cis c = Some cinst
           | _, _ => False
           end) cargs vargs ->
      F.fold (fun x v '(ϵ,ins) =>
                match v with
                | inl v     => ( x ↦ v,, ϵ , ins)
                | inr cinst => (ϵ, Clmt.bind x cinst ins)
                end) vargs (closure,ciclosure) = (ϵ',cis') ->
      ⦉ ∅, ∅, fclosure, cis, eis, ϵ', body ⦊ ⟱  ⦉ aa, tbls ⦊ ->
      let cis'' :=
          Clmt.bind x (CInst ϵ'' fclosure cis tbls aa eis applyblk) cis' in
      ⦇ ps, cs, es, fns, pis, cis, eis, ϵ, Instance x of c <[]> (cargs) @ i ⦈
        ⟱  ⦇ eis, cis'', pis, fns, es, cs, ps ⦈
  | dbs_instantiate_prsr (p x : string) (i : tags_t)
                         (cargs : Expr.constructor_args tags_t)
                         (vargs : F.fs string (V.v + pinst))
                         (prsrclosure : penv) (fclosure : fenv)
                         (piclosure pis' : pienv) (eis' : ARCH.extern_env)
                         (strt : AST.Parser.state_block tags_t)
                         (states : F.fs string (AST.Parser.state_block tags_t))
                         (closure ϵ' ϵ'' : epsilon) :
      ps p =
      Some (PDecl prsrclosure closure fclosure piclosure eis strt states) ->
      F.relfs
        (fun carg v =>
           match carg,v with
           | Expr.CAExpr e, inl v     => ⟨ ϵ, e ⟩ ⇓ v
           | Expr.CAName c, inr pinst => pis p = Some pinst
           | _, _ => False
           end) cargs vargs ->
      F.fold (fun x v '(ϵ,ins) =>
                match v with
                | inl v     => ( x ↦ v,, ϵ , ins)
                | inr pinst => (ϵ, Clmt.bind x pinst ins)
                end) vargs (closure,piclosure) = (ϵ',pis') ->
      let pis'' :=
          Clmt.bind x (PInst ϵ'' fclosure pis eis strt states) pis' in
      ⦇ ps, cs, es, fns, pis, cis, eis, ϵ, Instance x of p <[]>(cargs) @ i ⦈
        ⟱  ⦇ eis, cis, pis'', fns, es, cs, ps ⦈
  | dbs_instantiate_extn (e x : string) (i : tags_t)
                         (cargs : Expr.constructor_args tags_t)
                         (vargs : F.fs string (V.v + ARCH.P4Extern))
                         (extnclosure : eenv) (fclosure : fenv)
                         (eis' : ARCH.extern_env)
                         disp (** TODO: get dispatch method
                                        from architecture. *)
                         (* dispatch method *)
                         (closure ϵ' ϵ'' : epsilon) :
      es e =
      Some (EDecl extnclosure closure fclosure eis) ->
      F.relfs
        (fun carg v =>
           match carg,v with
           | Expr.CAExpr e, inl v     => ⟨ ϵ, e ⟩ ⇓ v
           | Expr.CAName c, inr einst => eis e = Some einst
           | _, _ => False
           end) cargs vargs ->
      (*F.fold (fun x v '(ϵ,ins) =>
                match v with
                | Left v => ( x ↦ v,, ϵ , ins)
                | Right einst => (ϵ, Clmt.bind x einst ins)
                end) vargs (closure,eiclosure) = (ϵ',eis') ->*)
      let eis'' :=
          Clmt.bind x {| ARCH.closure := ϵ';
                        ARCH.dispatch_method := disp |} eis' in
      ⦇ ps, cs, es, fns, pis, cis, eis, ϵ, Instance x of e<[]>(cargs) @ i ⦈
        ⟱  ⦇ eis'', cis, pis, fns, es, cs, ps ⦈
  | tpbs_control_decl (c : string) (cparams : Expr.constructor_params)
                      (eparams : F.fs string string)
                      (params : Expr.params) (body : Control.d tags_t)
                      (apply_blk : Stmt.s tags_t) (i : tags_t) :
      let cs' := Clmt.bind c (CDecl cs ϵ fns cis eis body apply_blk) cs in
      ⦇ ps, cs, es, fns, pis, cis, eis, ϵ,
        control c (cparams)(eparams)(params) apply { apply_blk } where { body } @ i ⦈
        ⟱  ⦇ eis, cis, pis, fns, es, cs', ps ⦈
  | tpbs_parser_decl (p : string) (cparams : Expr.constructor_params)
                     (eparams : F.fs string string)
                     (params : Expr.params) (strt : AST.Parser.state_block tags_t)
                     (states : F.fs string (AST.Parser.state_block tags_t))
                     (i : tags_t) :
      (* TODO: need parser/extern declaration environment
         as well as instantiation cases for parsers & externs *)
      let ps' := Clmt.bind p (PDecl ps ϵ fns pis eis strt states) ps in
      ⦇ ps, cs, es, fns, pis, cis, eis, ϵ,
        parser p (cparams)(eparams)(params) start := strt { states } @ i ⦈
        ⟱  ⦇ eis, cis, pis, fns, es, cs, ps' ⦈
(*  | tpbs_extern_decl (e : string) (i : tags_t)
                     (cparams : Expr.constructor_params)
                     (methods : F.fs string Expr.arrowT) :
      let es' := Clmt.bind e (EDecl es ϵ fns eis) es in
      ⦇ ps, cs, es, fns, pis, cis, eis, ϵ,
        extern e (cparams) { methods } @ i ⦈
        ⟱  ⦇ eis, cis, pis, fns, es', cs , ps ⦈ *)
  | tpbs_fruit_function (f : string) (params : Expr.params)
                        (τ : Expr.t) (body : Stmt.s tags_t) (i : tags_t) :
      let fns' := Clmt.bind f (FDecl ϵ fns body) fns in
      ⦇ ps, cs, es, fns, pis, cis, eis, ϵ, fn f <[]> (params) -> τ { body } @ i ⦈
        ⟱  ⦇ eis, cis, pis, fns', es, cs, ps ⦈
  | tpbs_void_function (f : string) (params : Expr.params)
                       (body : Stmt.s tags_t) (i : tags_t) :
      let fns' := Clmt.bind f (FDecl ϵ fns body) fns in
      ⦇ ps, cs, es, fns, pis, cis, eis, ϵ, void f <[]> (params) { body } @ i ⦈
        ⟱  ⦇ eis, cis, pis, fns', es, cs, ps ⦈
  | tpbs_seq (d1 d2 : TopDecl.d tags_t) (i : tags_t) (pis' pis'' : pienv)
             (cis' cis'' : cienv) (eis' eis'' : ARCH.extern_env)
             (fns' fns'' : fenv) (cs' cs'' : cenv)
             (ps' ps'' : penv) (es' es'' : eenv) :
      ⦇ ps,  cs,  es,  fns,  pis,  cis,  eis,  ϵ, d1 ⦈
        ⟱  ⦇ eis',  cis',  pis',  fns',  es',  cs',  ps'  ⦈ ->
      ⦇ ps', cs', es', fns', pis', cis', eis', ϵ, d2 ⦈
        ⟱  ⦇ eis'', cis'', pis'', fns'', es'', cs'', ps'' ⦈ ->
      ⦇ ps,  cs,  es,  fns,  pis,  cis,  eis,  ϵ, d1 ;%; d2 @ i ⦈
        ⟱  ⦇ eis'', cis'', pis'', fns'', es'', cs'', ps'' ⦈
  where "⦇ p1 , c1 , e1 , f1 , pi1 , ci1 , ei1 , ϵ , d ⦈ ⟱  ⦇ ei2 , ci2 , pi2 , f2 , e2 , c2 , p2 ⦈"
          := (topdecl_big_step
                p1 c1 e1 f1 pi1 ci1 ei1 ϵ d ei2 ci2 pi2 f2 e2 c2 p2).
  (**[]*)

  (** Pipeline:
      Given an input program,
      available extern-method dispatchers, execute program. 

      Stage 1: Evaluate (top-level) declarations.
      Stage 2: Collect parsers, controls, & packages to evaluate.
            - Requires knowing the names of these instances.
      Stage 3: Evaluate pipeline.
   *)

  (** Description of pipelines. *)
  Record pipeline :=
    { prsrs : list string;
      ctrls : list string }.

  (** Evaluating a parser instance. *)
  (* TODO: reject state? *)
  Variant parser_instance_big_step
            {tags_t: Type} : pinst -> Paquet.t -> Paquet.t -> Prop :=
  | pibs (ϵ ϵ': epsilon) (fs: fenv) (pis: pienv) (eis: ARCH.extern_env)
         (pkt pkt': Paquet.t) (strt: AST.Parser.state_block tags_t)
         (states : F.fs string (AST.Parser.state_block tags_t)) :
      SM (pkt, fs, ϵ, pis, eis, strt, states, start) ⇝ ⟨ϵ', accept, pkt'⟩ ->
      parser_instance_big_step
        (PInst ϵ fs pis eis strt states) pkt pkt'.
  (**[]*)

  (** Evaluating a control instance. *)
  Definition control_instance_big_step
             {tags_t: Type} (cp: @ctrl tags_t)
             '((CInst ϵ fs cis tbls aa eis apply_blk) : @cinst tags_t)
             (pkt pkt' : Paquet.t) : Prop :=
    exists (ϵ' : epsilon),
      ⟪ pkt, fs, ϵ, ApplyBlock cp tbls aa cis eis, apply_blk⟫ ⤋  ⟪ ϵ', C, pkt' ⟫.
  (**[]*)
  
  (** Entire program pipeline. *)
  Definition pipeline_big_step
            {tags_t: Type} (cp: ctrl) (pl: pipeline)
            (prog : TopDecl.d tags_t) (pkt pkt'' : Paquet.t) : Prop :=
    exists (pkt' : Paquet.t)
      (ps: penv) (cs: cenv) (es: eenv) (fs: fenv)
      (pis: pienv) (cis: cienv) (eis: ARCH.extern_env),
      (* Evaluate declarations to obtain instances. *)
      ⦇∅,∅,∅,∅,∅,∅,∅,∅,prog⦈ ⟱  ⦇eis,cis,pis,fs,es,cs,ps⦈ /\
      (** Gather parser instances for pipeline. *)
      let pl_prsrs := Clmt.gather pis $ prsrs pl in
      let pl_ctrls := Clmt.gather cis $ ctrls pl in
      (** Parser Pipeline. *)
      FoldLeft parser_instance_big_step pl_prsrs pkt pkt' /\
      FoldLeft (control_instance_big_step cp) pl_ctrls pkt' pkt''.
End Step.
