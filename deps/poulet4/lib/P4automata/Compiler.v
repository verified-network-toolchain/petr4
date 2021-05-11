Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import Poulet4.P4cub.AST.
Require Import Poulet4.P4cub.Value.
Require Import Poulet4.Monads.Monad.
Require Import Poulet4.Monads.Option.
Require Import Poulet4.Monads.State.
Require Import Poulet4.P4automata.P4automaton.

Open Scope monad_scope.
Open Scope string_scope.
Open Scope list_scope.

Module P := P4cub.
Module E := P.Expr.
Import P.P4cubNotations.
Module V := Val.
Import V.ValueNotations.
Import V.LValueNotations.

Section parser_to_p4automaton.

  Variable tags_t : Type.

  Definition simple_expression : Type := unit + E.e tags_t.

  Definition simple_lvalue : Type := unit + V.lv.
  
  Inductive state_operation :=
  | StateOperationNil
  | StateOperationExtract
      (typ: E.t)
      (into_lv: simple_lvalue)
  | SOVarDecl (x : string) (τ : E.t)
  | SOAsgn (lv : simple_lvalue) (e : simple_expression)
  | SOBlock (so : list state_operation)
  (* functon calls? other extern method calls? *).
  (**[]*)

  Inductive simple_match :=
  | SimpleMatchEquals (l r: simple_expression)
  | SimpleMatchAnd (l r: simple_match)
  | SimpleMatchDontCare
  .

  Section compile.
    Variables (pkt_name hdr_name: string).
    
    Definition compile_expression (expr: E.e tags_t) : simple_expression :=
      match expr with
      | <{ Var x:_ @ _ }> =>
        if x == hdr_name then inl tt else inr expr
      | _ => inr expr
      end.

    Fixpoint eval_lvalue (e : E.e tags_t) : option V.lv :=
      match e with
      | <{ Var x:_ @ _ }> => Some l{ VAR x }l
      | <{ Mem e:_ dot x @ _ }>
        => lv <<| eval_lvalue e ;; l{ lv DOT x }l
      | <{ Access e[n] @ _ }>
        => lv <<| eval_lvalue e ;; l{ lv[n] }l
      | _ => None
      end.

    Definition compile_lvalue (lv : V.lv) : simple_lvalue :=
      match lv with
      | l{ VAR x }l =>
        if x == hdr_name then inl tt else inr lv
      | _ => inr lv
      end.
    (**[]*)

    Fixpoint compile_statements
      (stmt: P4cub.Stmt.s tags_t)
      : option (list state_operation)
    :=
      match stmt with
      | -{ skip @ _ }- =>
        Some nil
      | -{ s1; s2 @ _ }- =>
        f1 <- compile_statements s1 ;;
        f2 <<| compile_statements s2 ;; f1 ++ f2
      | -{ var x:τ @ _ }- => Some [SOVarDecl x τ]
      | -{ asgn e1 := e2:_ @ _ }-
        => lv <<| eval_lvalue e1 ;;
          [SOAsgn (compile_lvalue lv) $ compile_expression e2]
      | -{ extern extern_lit calls func with args gives _ @ _ }- =>
        if extern_lit == pkt_name then
          if func == "extract" then
            match args with
            | ((_, P4cub.PAOut (t, e)) :: nil) =>
              into_lv <<| eval_lvalue e ;;
              StateOperationExtract t (compile_lvalue into_lv) :: nil
            | _=> None
            end
          else
            None
        else
          None
      | _ => None
      end
    .

    Fixpoint compile_updates
      (states: Field.fs string (P4cub.Parser.ParserState.state_block tags_t))
      : option (list (string * list state_operation))
    :=
      match states with
      | nil =>
        Some nil
      | (name, &{ state { stmt } transition _ }&) :: states' =>
        let* tail := compile_updates states' in
        let* head := compile_statements stmt in
        Some ((name, head) :: tail)
      end
    .

    Fixpoint compile_transition
      (trans: P4cub.Parser.ParserState.e tags_t)
      : option (list (simple_match * (string + bool)))
    :=
      match trans with
      | p{ goto start @ _ }p => None (* TODO: Implement this. *)
      | p{ goto accept @ _ }p =>
        Some ((SimpleMatchDontCare, inr true) :: nil)
      | p{ goto reject @ _ }p =>
        Some ((SimpleMatchDontCare, inr false) :: nil)
      | p{ goto δ st @ _ }p =>
        Some ((SimpleMatchDontCare, inl st) :: nil)
      | p{ select select_exp { cases } default:=def @ _ }p =>
        let select_exp' := compile_expression select_exp in
        let fix f cases :=
          match cases with
          | nil =>
            compile_transition def
          | (case_exp, case_trans) :: cases' =>
            let* child_clauses := compile_transition case_trans in
            let case_exp' := compile_expression case_exp in
            let augmented_clauses :=
              map (
                fun '(clause, target) =>
                (SimpleMatchAnd (SimpleMatchEquals select_exp' case_exp')
                                clause,
                 target)
              ) child_clauses in
            let* tail := f cases' in
            Some (augmented_clauses ++ tail)
          end in
         f cases
      end
    .

    Fixpoint compile_transitions
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
    .

  End compile.

  Record embedded_p4automaton := MkEmbeddedP4Automaton {
    emb_updates: list (string * list state_operation);
    emb_transitions: list (string * list (simple_match * (string + bool)));
  }.

  Definition parser_to_p4automaton
    (prsr: P4cub.TopDecl.d tags_t)
    : option embedded_p4automaton
  :=
    match prsr with
    | P4cub.TopDecl.TPParser _ _ params _ states _ => (* AST.v change *)
      match params with
      | (pkt_name, P4cub.PAIn pkt_type) ::
        (hdr_name, P4cub.PAOut hdr_type) :: _ =>
        let* updates := compile_updates pkt_name hdr_name states in
        let* transitions := compile_transitions hdr_name states in
        Some {|
          emb_updates := updates;
          emb_transitions := transitions;
        |}
      | _ =>
        None
      end
    | _ =>
      None
    end
  .

End parser_to_p4automaton.
