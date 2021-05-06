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

Section parser_to_p4automaton.

  Variable tags_t : Type.

  Inductive simple_expression :=
  | SimpleExpressionHeader
  | SimpleExpressionMember (e: simple_expression) (m: string)
  .

  Inductive simple_lvalue :=
  | SimpleLvalueHeader
  | SimpleLvalueMember (e: simple_lvalue) (m: string)
  .

  Inductive state_operation :=
  | StateOperationNil
  | StateOperationExtract
      (typ: P4cub.Expr.t)
      (into: simple_lvalue)
  .

  Inductive simple_match :=
  | SimpleMatchEquals (l r: simple_expression)
  | SimpleMatchAnd (l r: simple_match)
  | SimpleMatchDontCare
  .

  Section compile.
    Variables (pkt_name hdr_name: string).

    Fixpoint compile_expression
      (expr: P4cub.Expr.e tags_t)
      : option simple_expression
    :=
      match expr with
      | P4cub.Expr.EVar _ name _ =>
        if name == hdr_name then
          Some SimpleExpressionHeader
        else
          None
      | P4cub.Expr.EExprMember name _ expr _ =>
        let* child := compile_expression expr in
        Some (SimpleExpressionMember child name)
      | _ =>
        None
      end
    .

    Fixpoint compile_lvalue
      (expr: P4cub.Expr.e tags_t)
      : option simple_lvalue
    :=
      match expr with
      | P4cub.Expr.EVar _ name _ =>
        if name == hdr_name then
          Some SimpleLvalueHeader
        else
          None
      | P4cub.Expr.EExprMember name _ expr _ =>
        let* child := compile_lvalue expr in
        Some (SimpleLvalueMember child name)
      | _ =>
        None
      end
    .

    Fixpoint compile_statements
      (stmt: P4cub.Stmt.s tags_t)
      : option (list state_operation)
    :=
      match stmt with
      | P4cub.Stmt.SSkip _ =>
        Some nil
      | P4cub.Stmt.SSeq s1 s2 _ =>
        let* f1 := compile_statements s1 in
        let* f2 := compile_statements s2 in
        Some (f1 ++ f2)
      | P4cub.Stmt.SExternMethodCall extern func args _ =>
        if extern == pkt_name then
          if func == "extract" then
            match args with
            | P4cub.Arrow ((_, P4cub.PAOut (t, e)) :: nil) _ =>
              let* into := compile_lvalue e in
              Some (StateOperationExtract t into :: nil)
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
      | state :: states' =>
        let '(name, P4cub.Parser.ParserState.State stmt _) := state in
        let* tail := compile_updates states' in
        let* head := compile_statements stmt in
        Some ((name, head) :: tail)
      end
    .

    Section NotationSection.
    Import P4cub.P4cubNotations.

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
        let* select_exp' := compile_expression select_exp in
        let fix f cases :=
          match cases with
          | nil =>
            compile_transition def
          | (case_exp, case_trans) :: cases' =>
            let* child_clauses := compile_transition case_trans in
            let* case_exp' := compile_expression case_exp in
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
    End NotationSection.

    Fixpoint compile_transitions
      (states: Field.fs string (P4cub.Parser.ParserState.state_block tags_t))
      : option (list (string * list (simple_match * (string + bool))))
    :=
      match states with
      | nil =>
        Some nil
      | state :: states' =>
        let '(name, P4cub.Parser.ParserState.State _ trans) := state in
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
    (parser: P4cub.TopDecl.d tags_t)
    : option embedded_p4automaton
  :=
    match parser with
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
