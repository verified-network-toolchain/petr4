Require Import Syntax.
Require Import Monads.Monad.
Require Import Monads.Option.
Require Import Step.
Require Import Strings.String.
Require Import P4String.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.

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
  Definition unroll_parser (unrolls : nat) (states : list ParserState) : list ParserState :=
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
