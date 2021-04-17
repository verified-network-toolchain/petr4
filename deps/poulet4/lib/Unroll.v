Require Import Coq.Strings.String.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.

Require Import Poulet4.Syntax.
Require Import Poulet4.Monads.Monad.
Require Import Poulet4.Monads.Option.
Require Import Poulet4.Step.
Require Import Poulet4.P4String.

Import ListNotations.

Open Scope list_scope.
Open Scope string_scope.
Open Scope nat_scope.

Section Unroll.
  Context (tags_t: Type).
  Context (tags_dummy: tags_t).

  Notation P4String := (P4String.t tags_t).
  Notation program := (@program tags_t).
  Notation Declaration := (@Declaration tags_t).
  Notation ParserState := (@ParserState tags_t).

  Definition CFG : Type :=
    prod (list (prod P4String ParserState)) (list (prod P4String (list P4String))).

  Definition cfg_states (cfg : CFG) : list (prod P4String ParserState) :=
    fst cfg.

  Definition cfg_edges (cfg : CFG) : list (prod P4String (list P4String)) :=
    snd cfg.

  Definition DomMap : Type :=
    list (prod P4String (list P4String)).

  Definition Loop : Type :=
    prod (option string) (prod (list P4String) (list P4String)).

  Definition loop_hdr (loop : Loop) : option string :=
    fst loop.

  Definition loop_states (loop : Loop) : list P4String :=
    fst (snd loop).

  Definition loop_exits (loop : Loop) : list P4String :=
    snd (snd loop).

  (* TODO: implement CFG construction *)
  Definition to_cfg (states : list ParserState) : CFG :=
    ([], []).

  (* TODO *)
  Definition ParserWF (states : list ParserState) : Prop :=
    forall (st : ParserState),
      In st states ->
      False.

  (* TODO *)
  Theorem ToCFGCorrect : False.
  Admitted.

  Definition of_cfg (cfg : CFG) : list ParserState :=
    List.map (snd) (cfg_states cfg).

  Definition pred_cond_from_cfg
            (state : P4String)
            (pred : P4String)
            (edge : prod P4String (list P4String)) : bool :=
    P4String.equivb pred (fst edge) &&
    List.existsb (fun s => P4String.equivb s state) (snd edge).
  
  Definition is_pred (cfg : CFG) (state : P4String) (pred : P4String) : bool :=
    List.existsb (pred_cond_from_cfg state pred) (cfg_edges cfg).
  
  Definition get_preds  (cfg : CFG) (state : P4String) : list P4String :=
    let states := List.map fst (cfg_states cfg) in
    List.filter (is_pred cfg state) states.

  (* TODO: implement algorithm for computing dominators in a CFG *)
  Definition get_dom_map (cfg : CFG) : DomMap :=
    [].

  (* TODO: look into integrating the verified implementation of Tarjan's
     strongly-connected components algorithm from here:
     http://www-sop.inria.fr/marelle/Tarjan/ *)
  Definition get_sccs (cfg : CFG) : list Loop :=
    [].

  (* TODO: implement check of strongly-connected component property *)
  Definition non_trivial (cfg : CFG) (scc : Loop) : bool :=
    false.

  (* TODO: implement check of strongly-connected component property *)
  Definition is_natural (cfg : CFG) (doms : DomMap) (scc : Loop) : bool :=
    false.

  (* TODO *)
  Definition is_irreducible (cfg : CFG) (doms : DomMap) : bool :=
    false.

  (* TODO *)
  Definition Reachable (p q : P4String) (cfg : CFG) : Prop :=
    False.
  
  Definition StronglyConnected (scc : list P4String) (cfg : CFG) : Prop :=
    forall (p : P4String) (q : P4String),
      In p (List.map fst (cfg_states cfg)) ->
      In q (List.map fst (cfg_states cfg)) ->
      Reachable p q cfg.

  (* TODO *)
  Definition Natural (scc : list P4String) (cfg : CFG) : Prop := False.

  (* TODO *)
  Definition Trivial (scc : list P4String) : Prop := False.
  
  Definition Reducible (cfg : CFG) (doms : DomMap) : Prop :=
    forall (scc : list P4String),
      (forall state : P4String, In state scc -> In state (List.map fst (cfg_states cfg))) ->
      StronglyConnected scc cfg ->
      Natural scc cfg \/ Trivial scc.
  
  (* TODO *)
  Definition unroll_parser (unrolls : nat) (states : list ParserState) : list ParserState :=
    let cfg := to_cfg states in
    let doms := get_dom_map cfg in
    if is_irreducible cfg doms then states else
    states.

  Definition unroll_decl (unrolls : nat) (d : Declaration) : Declaration :=
    match d with
    | DeclParser t n tps ps cps ls ss =>
      DeclParser t n tps ps cps ls (unroll_parser unrolls ss)
    | _ => d end.
  
  Definition unroll_prog (unrolls : nat) (prog : program) : program :=
    match prog with
    | Program ds => Program (List.map (unroll_decl unrolls) ds) end.

End Unroll.
