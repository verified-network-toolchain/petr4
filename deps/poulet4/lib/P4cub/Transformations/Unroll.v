Require Import Coq.Strings.String.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.

Require Import Poulet4.P4cub.Syntax.AST.
Import Field.
Import P4cub.P4cubNotations.

Import ListNotations.

Open Scope list_scope.
Open Scope string_scope.
Open Scope nat_scope.

Section Unroll.
  Context (tags_t: Type).
  Context (tags_dummy: tags_t).
  Notation tpdecl := (P4cub.TopDecl.d tags_t).
  Notation ParserState := (P4cub.Parser.state_block tags_t).

  Definition CFG : Type :=
    prod (list (prod string ParserState)) (list (prod string (list string))).

  Definition cfg_states (cfg : CFG) : list (prod string ParserState) :=
    fst cfg.

  Definition cfg_edges (cfg : CFG) : list (prod string (list string)) :=
    snd cfg.

  Definition DomMap : Type :=
    list (prod string (list string)).

  Definition Loop : Type :=
    prod (option string) (prod (list string) (list string)).

  Definition loop_hdr (loop : Loop) : option string :=
    fst loop.

  Definition loop_states (loop : Loop) : list string :=
    fst (snd loop).

  Definition loop_exits (loop : Loop) : list string :=
    snd (snd loop).

  (* TODO: implement CFG construction *)
  Definition to_cfg (states : Field.fs string ParserState) : CFG :=
    (states, []).

  (* TODO *)
  Definition ParserWF (states : list ParserState) : Prop :=
    forall (st : ParserState),
      In st states ->
      False.

  (* TODO *)
  Theorem ToCFGCorrect : False.
  Admitted.

  Definition of_cfg (cfg : CFG) : fs string ParserState :=
    (cfg_states cfg).

  Definition pred_cond_from_cfg
            (st : string)
            (pred : string)
            (edge : prod string (list string)) : bool :=
    (String.eqb pred (fst edge)) &&
    List.existsb (fun s => String.eqb s st) (snd edge).
  
  Definition is_pred (cfg : CFG) (st : string) (pred : string) : bool :=
    List.existsb (pred_cond_from_cfg st pred) (cfg_edges cfg).
  
  Definition get_preds  (cfg : CFG) (st : string) : list string :=
    let states := List.map fst (cfg_states cfg) in
    List.filter (is_pred cfg st) states.

  (* TODO: implement algorithm for computing dominators in a CFG *)
  Definition get_dom_map (cfg : CFG) : DomMap :=
    [].

  (* TODO: look into integrating the verified implementation of Tarjan's
     strongly-connected components algorithm from here:
     http://www-sop.inria.fr/marelle/Tarjan/ *)
  Definition get_sccs (cfg : CFG) : list Loop :=
    [].

  (* TODO: implement check of strongly-connected component property *)
  Definition nontrivial (cfg : CFG) (scc : Loop) : bool :=
    false.

  (* TODO: implement check of strongly-connected component property *)
  Definition is_natural (cfg : CFG) (doms : DomMap) (scc : Loop) : bool :=
    false.

  Definition add_loop_header (cfg : CFG) (doms : DomMap) (loop : Loop) : Loop :=
    loop.

  Definition extract_nested (cfg : CFG) (doms : DomMap) (acc : list Loop) (loop : Loop) : list Loop :=
    acc.

  Definition find_upper_bound (unrolls : nat) (loop : Loop) : Loop :=
    loop.

  Definition sort (loops : list Loop) : list Loop := loops.

  Definition start_in_loop (cfg : CFG) (loops : list Loop) : bool :=
    false.

  Definition unstart_cfg (cfg : CFG) : CFG := cfg.

  Definition unstart_loop (loop : Loop) : Loop := loop.

  Definition index_loop (acc : list (nat * Loop) * nat) (loop : Loop) : list (nat * Loop) * nat :=
    ((snd acc, loop) :: (fst acc), (snd acc) + 1).

  Definition unroll_loop (acc : CFG * list (nat * Loop)) (idx : nat) : CFG * list (nat * Loop) :=
    acc.
  
  (* TODO *)
  (* NOTE: punting on reducibility; for now, assume everything is reducible and later investigate
     irreducible -> reducible transformation. This also means that we dont need SCC checking anymore.*)
  Definition unroll_parser (unrolls : nat) (sts : Field.fs string ParserState) : Field.fs string ParserState :=
    let cfg := to_cfg sts in
    let doms := get_dom_map cfg in
    let loops := get_sccs cfg in
    let loops := List.filter (nontrivial cfg ) loops in
    let loops := List.filter (is_natural cfg doms) loops in
    let loops := List.map (add_loop_header cfg doms) loops in
    let loops := List.fold_left (extract_nested cfg doms) [] loops in
    let loops := sort loops in
    let (cfg, loops)  := if (start_in_loop cfg loops)
                      then (unstart_cfg cfg, List.map unstart_loop loops)
                      else (cfg, loops) in
    let loops := List.map (fun l => find_upper_bound unrolls l) loops in
    let (loops, _) := List.fold_left index_loop loops ([], 0) in
    let loops := List.rev loops in
    let idxs := List.map fst loops in
    let (cfg, _) := List.fold_left unroll_loop idxs (cfg, loops) in
    of_cfg cfg.

  (* Rudy: I changed AST.v, this code compiles
     but may not be correct now that the start state
     are separate from the list of states. *)
  Fixpoint unroll_program (unrolls : nat) (d : tpdecl) : tpdecl :=
    match d with
    | %{ parser p (cparams) (params) start:=start_state { sts } @ i }% =>
      let sts := unroll_parser unrolls sts in
      %{ parser p (cparams) (params) start:=start_state { sts  } @ i }%
    | %{ d1 ;%; d2 @ i }% =>
      let d1 := unroll_program unrolls d1 in
      let d2 := unroll_program unrolls d2 in
      %{ d1 ;%; d2 @ i }%
    | _ => d end.
End Unroll.
