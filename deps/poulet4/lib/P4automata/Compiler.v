Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import Poulet4.P4cub.AST.
Require Import Poulet4.P4cub.Value.
Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.P4cub.BigStep.
Require Import Poulet4.Monads.Option.
Require Import Poulet4.Monads.Monad.
Require Coq.ZArith.BinInt.

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
Import V.ValueEquality.
Module PS := P4cub.Parser.ParserState.

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
  (* functon calls? other extern method calls? *).
  (**[]*)

  Inductive simple_match :=
  | SimpleMatchEquals (l r: E.e tags_t)
  | SimpleMatchAnd (l r: simple_match)
  | SimpleMatchDontCare
  .

  Section compile.
    (*Variables (pkt_name hdr_name: string).*)
    
    (*Definition compile_expression (expr: E.e tags_t) : E.e tags_t :=
      expr.*)

    Fixpoint eval_lvalue (e : E.e tags_t) : option V.lv :=
      match e with
      | <{ Var x:_ @ _ }> => Some l{ VAR x }l
      | <{ Mem e:_ dot x @ _ }>
        => lv <<| eval_lvalue e ;; l{ lv DOT x }l
      | <{ Access e[n] @ _ }>
        => lv <<| eval_lvalue e ;; l{ lv[n] }l
      | _ => None
      end.

    (*Definition compile_lvalue (lv : V.lv) : V.lv :=
      lv.*)
    (**[]*)

    Fixpoint compile_statement
             (stmt: P4cub.Stmt.s tags_t) : option state_operation :=
      match stmt with
      | -{ skip @ _ }- =>
        Some SONil
      | -{ s1; s2 @ _ }- =>
        f1 <- compile_statement s1 ;;
        f2 <<| compile_statement s2 ;;
        SOSeq f1 f2
      | -{ var x:τ @ _ }- => Some $ SOVarDecl x τ
      | -{ asgn e1 := e2:_ @ _ }- => Some $ SOAsgn e1 e2
      | -{ extern extern_lit calls func with args gives _ @ _ }- =>
        if func == "extract" then
          match args with
          | ((_, P4cub.PAOut (t, e)) :: nil) =>
            into_lv <<| eval_lvalue e ;; SOExtract t into_lv
          | _=> None
          end
        else
          None
      | _ => None end.

    Definition trans_t : Type := list (simple_match * (string + bool)).

    Fixpoint compile_transition
      (trans: P4cub.Parser.ParserState.e tags_t) : option trans_t :=
      match trans with
      | p{ goto start @ _ }p =>
        Some ((SimpleMatchDontCare, inl "start") :: nil)
      | p{ goto accept @ _ }p =>
        Some ((SimpleMatchDontCare, inr true) :: nil)
      | p{ goto reject @ _ }p =>
        Some ((SimpleMatchDontCare, inr false) :: nil)
      | p{ goto δ st @ _ }p =>
        Some ((SimpleMatchDontCare, inl st) :: nil)
      | p{ select select_exp { cases } default:=def @ _ }p =>
        let fix f cases :=
          match cases with
          | nil =>
            compile_transition def
          | (case_exp, case_trans) :: cases' =>
            let* child_clauses := compile_transition case_trans in
            let augmented_clauses :=
              map (
                fun '(clause, target) =>
                (SimpleMatchAnd (SimpleMatchEquals select_exp case_exp)
                                clause,
                 target)
              ) child_clauses in
            let* tail := f cases' in
            Some (augmented_clauses ++ tail)
          end in
         f cases
      end
    .
    
    Definition compile_state_block
               (stblk : PS.state_block tags_t)
      : option (state_operation * trans_t) :=
      match stblk with
      | &{ state { s } transition e }& =>
        so <- compile_statement s ;;
        tr <<| compile_transition e ;; (so, tr)
      end.

    Definition compile_state_blocks
               (stblks : F.fs string (PS.state_block tags_t))
      : option (F.fs string (state_operation * trans_t)) :=
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
    | SOExtract τ _ => E.width_of_typ τ
    | SOVarDecl _ _ => 0
    | SOAsgn _ _ => 0
    | SOBlock op => operation_size op end.

  Definition P4Automaton_size
             (strt : state_operation * trans_t)
             (states : F.fs string (state_operation * trans_t))
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

  Fixpoint interp_expr (ϵ : Step.epsilon) (expr : E.e tags_t) : option V.v :=
    match expr with
    | <{ BOOL b @ _ }> => Some ~{ VBOOL b }~
    | <{ w W n @ _ }> => Some ~{ w VW n }~
    | <{ w S n @ _ }> => Some ~{ w VS n }~
    | <{ Var x : _ @ _ }> => ϵ x
    | <{ Slice e : _ [ h : l ] @ _ }> =>
      v <- interp_expr ϵ e ;;
      Step.eval_slice h l v
    | <{ Cast e : τ @ _ }> =>
      v <- interp_expr ϵ e ;;
      Step.eval_cast τ v
    | <{ UOP op e : _ @ _ }> =>
      v <- interp_expr ϵ e ;;
      Step.eval_uop op v
    | <{ BOP e1 : _ op e2 : _ @ _ }> =>
      v1 <- interp_expr ϵ e1 ;;
      v2 <- interp_expr ϵ e2 ;;
      Step.eval_bop op v1 v2
    | <{ tup es @ _ }> =>
      vs <<| sequence (List.map (interp_expr ϵ) es) ;;
      ~{ TUPLE vs }~
    | <{ rec { fs } @ i }> =>
      vs <<| sequence (List.map (fun '(f, (_,e)) => v <<| interp_expr ϵ e ;; (f,v)) fs) ;;
      ~{ REC { vs } }~
    | <{ hdr { fs } valid := b @ i }> =>
      b <- interp_expr ϵ b ;;
      vs <- sequence (List.map (fun '(f, (_, e)) => v <<| interp_expr ϵ e ;; (f,v)) fs) ;;
      match b with
      | ~{ VBOOL b }~  => Some ~{ HDR { vs } VALID := b }~
      | _ => None end
    | <{ Mem e : _ dot x @ _ }> =>
      v <- interp_expr ϵ e ;;
      Step.eval_member x v
    | <{ Error x @ _ }> =>
      Some ~{ ERROR x }~
    | <{ Matchkind x @ _ }> =>
      Some ~{ MATCHKIND x }~
    | <{ Stack hdrs : ts [ size ] nextIndex := i @ _ }> =>
      vs <<| sequence (List.map (fun e =>
                                 v <- interp_expr ϵ e ;;
                                 match v with
                                 | ~{ HDR { vs } VALID := b }~ =>
                                   Some (b, vs)
                                 | _ => None end
                              ) hdrs) ;;
      ~{ STACK vs : ts [ size ] NEXT := i }~
    | <{ Access e [ n ] @ _ }> =>
      v <- interp_expr ϵ e ;;
      match v with
      | ~{ STACK vs : _ [ _ ]  NEXT := _ }~ =>
        v <<| List.nth_error vs (BinInt.Z.to_nat n) ;;
        let '(b, fs) := v in
        ~{ HDR { fs } VALID := b }~
      | _ => None end    
    end.

  Fixpoint interp_operation
           (pkt : list bool)
           (e : Step.epsilon)
           (operation : state_operation) : Step.epsilon :=
    match operation with
    | SONil => e
    | SOSeq op1 op2 => interp_operation pkt (interp_operation pkt e op2) op2
    | SOExtract τ lv =>
      (* let '(v, _) := Poulet4.P4cub.Paquet.ValuePacket.read_inc τ pkt in
      match v with
      | inl v => Step.lv_update lv v e
      | inr _ =>  e end *) e
    | SOVarDecl x τ =>
      let v := V.vdefault τ in
      let lv := Val.LVVar x in
      Step.lv_update lv v e
    | SOAsgn lhs rhs =>
      let v := interp_expr e rhs in
      let lv := eval_lvalue lhs in
      match (v, lv) with
      | (Some v, Some lv) => Step.lv_update lv v e
      | (_, _) => e end
    | SOBlock op => interp_operation pkt e op end.

  Definition P4Automaton_update
             (strt : state_operation * trans_t)
             (states : F.fs string (state_operation * trans_t))
             (st : P4Automaton_State)
             (pkt : list bool)
             (e : Step.epsilon) : Step.epsilon :=
    match st with
    | START => interp_operation pkt e (fst strt)
    | ST_VAR x =>
      match F.get x states with
      | Some stvar => interp_operation pkt e (fst stvar)
      | None => e end
    end.

  Fixpoint interp_match (e : Step.epsilon) (m : simple_match) : bool :=
    match m with
    | SimpleMatchEquals l r =>
      match (interp_expr e l), (interp_expr e r) with
      | Some b1, Some b2 => eqbv b1 b2
      | _, _ => false end
    | SimpleMatchAnd l r =>
      andb (interp_match e l) (interp_match e r)
    | SimpleMatchDontCare => true end.

  Fixpoint interp_transition (e : Step.epsilon) (t : trans_t) : P4Automaton_State + bool :=
    match t with
    | (m, st) :: t =>
      if interp_match e m
      then match st with
           | inl "start" => inl START
           | inl x => inl (ST_VAR x)
           | inr b => inr b end
      else interp_transition e t
    | [] => inr false end.

  Definition P4Automaton_transitions
             (strt : state_operation * trans_t)
             (states : F.fs string (state_operation * trans_t))
             (st : P4Automaton_State)
             (e : Step.epsilon) : P4Automaton_State + bool :=
    match st with
    | START => interp_transition e (snd strt)
    | ST_VAR x =>
      match F.get x states with
      | Some stvar => interp_transition e (snd stvar)
      | None => inr false end
    end.

  Definition parser_to_p4automaton
      (strt : PS.state_block tags_t)
      (states : F.fs string (PS.state_block tags_t))
    :=
    let strt := compile_state_block strt in
    let states := compile_state_blocks states in
    match (strt, states) with
    | (Some strt, Some states) =>
      Some (MkP4Automaton
              Step.epsilon
              P4Automaton_State
              (P4Automaton_size strt states)
              (P4Automaton_update strt states)
              (P4Automaton_transitions strt states)
              (P4Automaton_Size_Cap strt states))
    | (_, _) => None end.

  Fixpoint topdecl_to_p4automata (d : P4cub.TopDecl.d tags_t) : list (option p4automaton) :=
    match d with
    | %{ parser p ( cparams ) ( params ) start := strt { states } @ i }% =>
      [parser_to_p4automaton strt states]
    | %{ d1 ;%; d2 @ i }%  => (topdecl_to_p4automata d1) ++ (topdecl_to_p4automata d2)
    | _ => [None] end.

  (* TODOS:
     1) implement extract operation semantics = fix types of packet monad thing *)

End parser_to_p4automaton.
