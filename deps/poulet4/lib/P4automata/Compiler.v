Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import Poulet4.P4cub.AST.
Require Import Poulet4.P4cub.Value.
Require Import Poulet4.Monads.Monad.
Require Import Poulet4.Monads.Option.
Require Import Poulet4.Monads.State.
Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.P4cub.BigStep.

Open Scope monad_scope.
Open Scope string_scope.
Open Scope list_scope.

Module P := P4cub.
Module E := P.Expr.
Import P.P4cubNotations.
Module V := Val.
Import V.ValueNotations.
Import V.LValueNotations.
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
      (stmt: P4cub.Stmt.s tags_t)
      : option state_operation
    :=
      match stmt with
      | -{ skip @ _ }- =>
        Some SONil
      | -{ s1; s2 @ _ }- =>
        f1 <- compile_statement s1 ;;
        f2 <<| compile_statement s2 ;;
        SOSeq f1 f2
      | -{ var x:τ @ _ }- => Some $ SOVarDecl x τ
      | -{ asgn e1 := e2:_ @ _ }-
        => (*lv <<| eval_lvalue e1 ;;
          [SOAsgn (compile_lvalue lv) $ compile_expression e2]*)
        Some $ SOAsgn e1 e2
      | -{ extern extern_lit calls func with args gives _ @ _ }- =>
        (*if extern_lit == pkt_name then*)
          if func == "extract" then
            match args with
            (* Exactly one argument for "extract" *)
            | ((_, P4cub.PAOut (t, e)) :: nil) =>
              into_lv <<| eval_lvalue e ;; SOExtract t into_lv
            | _=> None
            end
          else
            None
    (*else
          None*)
      | _ => None
      end
    .

    Definition trans_t : Type := list (simple_match * (string + bool)).

    Fixpoint compile_transition
      (trans: P4cub.Parser.ParserState.e tags_t) : option trans_t :=
      match trans with
      | p{ goto start @ _ }p => None (* TODO: Implement this. *)
      | p{ goto accept @ _ }p =>
        Some ((SimpleMatchDontCare, inr true) :: nil)
      | p{ goto reject @ _ }p =>
        Some ((SimpleMatchDontCare, inr false) :: nil)
      | p{ goto δ st @ _ }p =>
        Some ((SimpleMatchDontCare, inl st) :: nil)
      | p{ select select_exp { cases } default:=def @ _ }p =>
        (*let select_exp' := compile_expression select_exp in*)
        let fix f cases :=
          match cases with
          | nil =>
            compile_transition def
          | (case_exp, case_trans) :: cases' =>
            let* child_clauses := compile_transition case_trans in
            (*let case_exp' := compile_expression case_exp in*)
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

    (*Search (list (?A * ?B) -> list ?A * list ?B).*)

    (*Fixpoint compile_updates
      (states: Field.fs string (P4cub.Parser.ParserState.state_block tags_t))
      : option (F.fs (string * list state_operation))
    :=
      match states with
      | nil =>
        Some nil
      | (name, &{ state { stmt } transition _ }&) :: states' =>
        let* tail := compile_updates states' in
        let* head := compile_statements stmt in
        Some ((name, head) :: tail)
      end
    .*)

    (*Fixpoint compile_transitions
      (states: Field.fs string (P4cub.Parser.ParserState.state_block tags_t))
      : option (list (string * list (simple_match * (string + bool))))
    :=
      match states with
      | nil =>
        Some nil
      | st :: states' =>
        let '(name, P4cub.Parser.ParserState.State _ trans) := st in
        let* tail := compile_transitions states' in
        let* head := compile_transition trans in
        Some ((name, head) :: tail)
      end
    .*)

  End compile.

  Inductive P4Automaton_State :=
  | START
  | ST_VAR (x : string).

  Definition P4Automaton_size
             (strt : state_operation * trans_t)
             (states : F.fs string (state_operation * trans_t))
             (st : P4Automaton_State) : nat :=
    0. (* TODO *)

  Theorem P4Automaton_Size_Cap : forall strt states st, 0 < P4Automaton_size strt states st.
  Admitted.

  Definition P4Automaton_update
             (strt : state_operation * trans_t)
             (states : F.fs string (state_operation * trans_t))
             (st : P4Automaton_State)
             (pkt : list bool)
             (e : Step.epsilon) : Step.epsilon :=
    e.

  Definition P4Automaton_transitions
             (strt : state_operation * trans_t)
             (states : F.fs string (state_operation * trans_t))
             (st : P4Automaton_State)
             (e : Step.epsilon) : P4Automaton_State + bool :=
    inr false.

  Check compile_state_block.

  Definition parser_to_p4automaton
    (prsr: P4cub.TopDecl.d tags_t)
    : option p4automaton
  :=
    match prsr with
    | %{ parser p ( _ ) ( _ ) start := strt { states } @ i }% =>
      strt <- compile_state_block strt ;;
      states <<| compile_state_blocks states ;;
      MkP4Automaton
        unit (* TODO: Step.epsilon causes universal consistency error *)
        P4Automaton_State
        (P4Automaton_size strt states)
        (fun _ _ st => st) (* TODO: should be P4Automaton_update strt states *)
        (fun _ _ => inr false) (* TODO: should be P4Automaton_transitions strt states *)
        (P4Automaton_Size_Cap strt states)
    | _ => None end.
    (* | P4cub.TopDecl.TPParser p cparams params strt states tags => (* AST.v change *)
      match params with
      | (pkt_name, P4cub.PAIn pkt_type) ::
        (hdr_name, P4cub.PAOut hdr_type) :: _ =>
        let updates := compile_updates hdr_name states in
        let transitions := compile_transitions states in
        match updates, transitions with
        | Some updates, Some transitions =>
          Some {|
              emb_updates := updates;
              emb_transitions := transitions;
            |}
        | _, _ => None end                  
      | _ =>
        None
      end
    | _ =>
      None
    end *)

End parser_to_p4automaton.
