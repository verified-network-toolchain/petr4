Set Warnings "-custom-entry-overridden".
Require Import Coq.Strings.String
        Coq.Lists.List Coq.PArith.BinPos.
Require Import Poulet4.P4cub.BigStep.Value.Value
        Poulet4.P4cub.BigStep.ValEnvUtil
        Poulet4.P4cub.Syntax.Auxilary
        Poulet4.P4cub.Envn.
Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.Monads.Monad Poulet4.Monads.Error.
Require Poulet4.Bitwise Poulet4.P4cub.BigStep.ExprUtil.

Open Scope monad_scope.
Open Scope string_scope.
Open Scope list_scope.

Set Universe Polymorphism.

Module P := P4cub.
Module E := P.Expr.
Import P.P4cubNotations.
Module V := Val.
Import V.ValueNotations.
Import V.LValueNotations.
Module PR := P4cub.Parser.

Section parser_to_p4automaton.

  Variable tags_t : Type.
  
  Inductive state_operation :=
  | SONil
  | SOSeq (s1 s2 : state_operation)
  | SOExtract
      (typ: E.t)
      (into_lv: V.lv)
  | SOVarDecl (x : string) (τ : E.t)
  | SOAsgn (lhs rhs : E.e tags_t)
  | SOBlock (s : state_operation)
  (* function calls? other extern method calls? *).
  (**[]*)

  Section compile.
    (*Variables (pkt_name hdr_name: string).*)
    
    (*Definition compile_expression (expr: E.e tags_t) : E.e tags_t :=
      expr.*)
    Inductive compile_error := 
    | CEBadLValue (e: E.e tags_t)
    | CEBadExternArgs (args: E.arrowE tags_t)
    | CEUnsupportedExtern (name: string)
    | CEUnsupportedStmt (s: P4cub.Stmt.s tags_t)
    | CEUnsupportedExpr (e: E.e tags_t)
    | CEInconceivable (msg: string).

    Fixpoint eval_lvalue (e : E.e tags_t) : @error_monad compile_error V.lv :=
      match e with
      | <{ Var x:_ @ _ }> => mret l{ VAR x }l
      | <{ Mem e:_ dot x @ _ }>
        => lv <<| eval_lvalue e ;; l{ lv DOT x }l
      | <{ Access e[n] @ _ }>
        => lv <<| eval_lvalue e ;; l{ lv[n] }l
      | _ => err (CEBadLValue e)
      end.

    (*Definition compile_lvalue (lv : V.lv) : V.lv :=
      lv.*)
    (**[]*)

    Fixpoint compile_statement
             (stmt: P4cub.Stmt.s tags_t) : @error_monad compile_error state_operation :=
      match stmt with
      | -{ skip @ _ }- =>
        mret SONil
      | -{ s1; s2 @ _ }- =>
        f1 <- compile_statement s1 ;;
        f2 <<| compile_statement s2 ;;
        SOSeq f1 f2
      | -{ var x:τ @ _ }- => mret $ SOVarDecl x τ
      | -{ asgn e1 := e2:_ @ _ }- => mret $ SOAsgn e1 e2
      | -{ extern extern_lit calls func with args gives x @ _ }- =>
        if func == "extract" then
          match args with
          | ((_, P4cub.PAOut (t, e)) :: nil) =>
            into_lv <<| eval_lvalue e ;; SOExtract t into_lv
          | _=> err $ CEBadExternArgs (P4cub.Arrow args x)
          end
        else
          err $ CEUnsupportedExtern func
      | _ => err $ CEUnsupportedStmt stmt end.
    
    Definition compile_state_block
               (stblk : PR.state_block tags_t)
      : @error_monad compile_error (state_operation * (PR.e tags_t)) :=
      match stblk with
      | &{ state { s } transition e }& =>
        so <<| compile_statement s ;;
        (so, e)
      end.

    Definition compile_state_blocks
               (stblks : F.fs string (PR.state_block tags_t))
      : @error_monad compile_error (F.fs string (state_operation * (PR.e tags_t))) :=
      let cfld fld :=
          let '(x, stblk) := fld in
          sot <<| compile_state_block stblk ;; (x, sot) in
      sequence $ List.map cfld stblks.
  End compile.

  Inductive P4Automaton_State :=
  | START
  | ST_VAR (x : string).

  Fixpoint operation_size (op : state_operation) : nat :=
    match op with
    | SONil => 0
    | SOSeq op1 op2 => (operation_size op1) + (operation_size op2)
    | SOExtract τ _ => SynDefs.width_of_typ τ
    | SOVarDecl _ _ => 0
    | SOAsgn _ _ => 0
    | SOBlock op => operation_size op end.

  Definition P4Automaton_size
             (strt : state_operation * (PR.e tags_t))
             (states : F.fs string (state_operation * (PR.e tags_t)))
             (st : P4Automaton_State) : nat :=
    match st with
    | START => operation_size (fst strt)
    | ST_VAR x =>
      match F.get x states with
      | Some stvar => operation_size (fst stvar)
      | None => 0 end
    end.
    
  Theorem P4Automaton_Size_Cap : forall strt states st, 0%nat < P4Automaton_size strt states st.
  Admitted.

  Fixpoint interp_expr (ϵ : epsilon) (expr : E.e tags_t) : @error_monad compile_error V.v :=
    match expr with
    | <{ BOOL b @ _ }> => mret ~{ VBOOL b }~
    | <{ w W n @ _ }> => mret ~{ w VW n }~
    | <{ w S n @ _ }> => mret ~{ w VS n }~
    | <{ Var x : _ @ _ }> => 
      lift_opt_error (CEInconceivable (String.append "missing variable " x)) (Env.find x ϵ)
    | <{ Slice e : _ [ h : l ] @ _ }> =>
      v <- interp_expr ϵ e ;;
      lift_opt_error (CEInconceivable "bad slice") $ ExprUtil.eval_slice h l v
    | <{ Cast e : τ @ _ }> =>
      v <- interp_expr ϵ e ;;
      lift_opt_error (CEInconceivable "bad cast") $ ExprUtil.eval_cast τ v
    | <{ UOP op e : _ @ _ }> =>
      v <- interp_expr ϵ e ;;
      lift_opt_error (CEUnsupportedExpr expr) $ ExprUtil.eval_uop op v
    | <{ BOP e1 : _ op e2 : _ @ _ }> =>
      v1 <- interp_expr ϵ e1 ;;
      v2 <- interp_expr ϵ e2 ;;
      lift_opt_error (CEUnsupportedExpr expr) $ ExprUtil.eval_bop op v1 v2
    | <{ tup es @ _ }> =>
      vs <<| sequence (List.map (interp_expr ϵ) es) ;;
      ~{ TUPLE vs }~
    | <{ struct { fs } @ i }> =>
      vs <<| sequence (List.map (fun '(f, (_,e)) => v <<| interp_expr ϵ e ;; (f,v)) fs) ;;
      ~{ STRUCT { vs } }~
    | <{ hdr { fs } valid := b @ i }> =>
      b <- interp_expr ϵ b ;;
      vs <- sequence (List.map (fun '(f, (_, e)) => v <<| interp_expr ϵ e ;; (f,v)) fs) ;;
      match b with
      | ~{ VBOOL b }~  => mret ~{ HDR { vs } VALID := b }~
      | _ => err (CEInconceivable "bad valid assignment") end
    | <{ Mem e : _ dot x @ _ }> =>
      v <- interp_expr ϵ e ;;
      lift_opt_error (CEUnsupportedExpr expr) $ ExprUtil.eval_member x v
    | <{ Error x @ _ }> =>
      mret ~{ ERROR x }~
    | <{ Matchkind x @ _ }> =>
      mret ~{ MATCHKIND x }~
    | <{ Stack hdrs : ts [ size ] nextIndex := i @ _ }> =>
      vs <<| sequence (List.map (fun e =>
                                 v <- interp_expr ϵ e ;;
                                 match v with
                                 | ~{ HDR { vs } VALID := b }~ =>
                                   mret (b, vs)
                                 | _ => err (CEInconceivable "bad header stack assignment") end
                              ) hdrs) ;;
      ~{ STACK vs : ts [ size ] NEXT := i }~
    | <{ Access e [ n ] @ _ }> =>
      v <- interp_expr ϵ e ;;
      match v with
      | ~{ STACK vs : _ [ _ ]  NEXT := _ }~ =>
        v <<| lift_opt_error (CEInconceivable "bad stack index") (List.nth_error vs (BinInt.Z.to_nat n)) ;;
        let '(b, fs) := v in
        ~{ HDR { fs } VALID := b }~
      | _ => err (CEUnsupportedExpr expr) end    
    end.

  Fixpoint interp_extract (τ : E.t) (pkt : list bool) : option V.v :=
    let f (acc : (list bool) * (list (option (string * V.v)))) (x : string * E.t) :=
        let '(pkt, fs) := acc in
        let '(n, τ) := x in
        let w := SynDefs.width_of_typ τ in
        let pkt1 := List.firstn w pkt in
        let pkt2 := List.skipn w pkt in
        let pair :=
            v <<| interp_extract τ pkt1 ;; (n, v) in
        (pkt2, fs ++ [pair]) in
    match τ with
    | {{ Bool }} =>
      b <<| List.nth_error pkt 0%nat ;;
      ~{ VBOOL b }~
    | {{ bit < w > }} =>
      let w' := Pos.to_nat w in
      let pkt' := List.firstn w' pkt in
      let n := BinInt.Z.of_nat (Poulet4.Bitwise.to_nat pkt') in
      Some ~{ w VW n }~
    | {{ int < w > }} =>
      let w' := Pos.to_nat (w - 1) in
      let sign := List.nth_error pkt 0%nat in
      let pkt := skipn 1%nat pkt in
      let pkt' := List.firstn (w'-1) pkt in
      let n := BinInt.Z.of_nat (Poulet4.Bitwise.to_nat pkt') in
      let n :=
          if sign
          then
            BinInt.Z.of_nat ((BinInt.Z.to_nat n) -
                             (Pos.to_nat (Coq.PArith.BinPosDef.Pos.pred_double w)))
          else n in
      Some ~{ w VS n }~
    | {{ error }} => None
    | {{ matchkind }} => None
    | {{ tuple _ }} => None
    | {{ struct { fs } }} =>
      fs <<| sequence (snd (List.fold_left f fs (pkt, []))) ;;
      ~{ STRUCT { fs } }~
    | {{ hdr { fs }  }} =>
      fs <<| sequence (snd (List.fold_left f fs (pkt, []))) ;;
      ~{ HDR { fs } VALID := true }~
    | {{ stack _ [ _ ] }} => None end.

  Fixpoint interp_operation
           (pkt : list bool)
           (e : epsilon)
           (operation : state_operation) : option epsilon :=
    match operation with
    | SONil => Some e
    | SOSeq op1 op2 =>
      e <- interp_operation pkt e op1 ;;
      interp_operation pkt e op2
    | SOExtract τ lv =>
      v <<| interp_extract τ pkt ;;
      lv_update lv v e
    | SOVarDecl x τ =>
      let v := vdefault τ in
      let lv := Val.LVVar x in
      Some (lv_update lv v e)
    | SOAsgn lhs rhs =>
      v <- strip_error (interp_expr e rhs) ;;
      lv <<| strip_error (eval_lvalue lhs) ;;
      lv_update lv v e
    | SOBlock op => interp_operation pkt e op end.

  Definition P4Automaton_update
             (strt : state_operation * (PR.e tags_t))
             (states : F.fs string (state_operation * (PR.e tags_t)))
             (st : P4Automaton_State)
             (pkt : list bool)
             (e : option epsilon) : option epsilon :=
    e <- e ;;
    match st with
    | START => interp_operation pkt e (fst strt)
    | ST_VAR x =>
      stvar <- F.get x states ;;
      interp_operation pkt e (fst stvar)  end.

  Fixpoint interp_transition
           (ϵ : epsilon)
           (t : PR.e tags_t) : P4Automaton_State + bool :=
    let fix frec (pes : F.fs PR.pat (PR.e tags_t))
        : F.fs PR.pat (P4Automaton_State + bool) :=
        match pes with
        | [] => []
        | (p, t) :: pes => (p, interp_transition ϵ t) :: frec pes
        end in
    match t with
    | p{ goto ={ start }= @ _ }p => inl START
    | p{ goto ={ accept }= @ _ }p => inr true
    | p{ goto ={ reject }= @ _ }p => inr false
    | p{ goto ={ δ x }= @ _ }p => inl (ST_VAR x)
    | p{ select se { cs } default := def @ _ }p =>
      match interp_expr ϵ se with
      | inr _ => inr false
      | inl v =>
        match F.find_value
                (fun p => match_pattern p v)
                (frec cs) with
        | None => interp_transition ϵ def
        | Some r => r
        end
      end
    end.
  (**[]*)
  
  Definition P4Automaton_transitions
             (strt : state_operation * (PR.e tags_t))
             (states : F.fs string (state_operation * (PR.e tags_t)))
             (st : P4Automaton_State)
             (e : option epsilon) : P4Automaton_State + bool :=
    match e with
      | Some e =>
        match st with
        | START => interp_transition e (snd strt)
        | ST_VAR x =>
          match F.get x states with
          | Some stvar => interp_transition e (snd stvar)
          | None => inr false end
        end
      | None => inr false end.

  Inductive myopt (A: Type) :=
  | MSome (a: A)
  | MNone.

  Definition parser_to_p4automaton
      (strt : PR.state_block tags_t)
      (states : F.fs string (PR.state_block tags_t))
      : @error_monad compile_error p4automaton
    :=
    let strt := compile_state_block strt in
    let states := compile_state_blocks states in
    match strt, states with
    | inl strt, inl states =>
      inl (MkP4Automaton
              (option epsilon)
              P4Automaton_State
              (P4Automaton_size strt states)
              (P4Automaton_update strt states)
              (P4Automaton_transitions strt states)
              (P4Automaton_Size_Cap strt states))
    | inr e, _ =>     inr e
    | inl _, inr e => inr e end.

  Fixpoint topdecl_to_p4automata (d : P4cub.TopDecl.d tags_t) : list (@error_monad compile_error p4automaton) :=
    match d with
    | %{ parser p ( cparams ) ( params ) start := strt { states } @ i }% =>
      [parser_to_p4automaton strt states]
    | %{ d1 ;%; d2 @ i }%  => (topdecl_to_p4automata d1) ++ (topdecl_to_p4automata d2)
    | _ => [err (CEInconceivable "cannot convert nonparser to automata")] end.

  (* TODOS:
     1) implement extract operation semantics = fix types of packet monad thing *)

End parser_to_p4automaton.
