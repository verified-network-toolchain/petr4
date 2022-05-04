From Poulet4 Require Import
     P4light.Syntax.Syntax P4light.Transformations.SimplExpr.
From Poulet4 Require Export
     Monads.Result Utils.Util.StringUtil.
Require Import Coq.Lists.List.
Import StringUtil ListNotations.

Require Import String.
Open Scope string_scope.
Import Result ResultNotations.

Module NameGen.

  Definition t := nat.

  Definition name := "h'".

  Definition init := 0.

  Definition get_new (x : t) :=
    (name ++ string_of_nat x, S x).

End NameGen.


Section Nameless.
  Variable (tags_t : Type).
  Fixpoint hoist_expression (g : NameGen.t) (e : @Expression tags_t) : (NameGen.t * list (@Declaration tags_t) * @Expression tags_t) :=
    let '(MkExpression tags expr typ dir) := e in
    let new_expr := fun expr => MkExpression tags expr typ dir in
    match expr with
    | ExpNamelessInstantiation typ args =>
      let f := fun e '(g, hoists, es) =>
          let '(g',hoist, e') := hoist_expression g e in
          (g', List.app hoist hoists, e' :: es)
      in
      let '(g', rec_hoist, args') := List.fold_right f (g,[],[]) args in
      let (fresh_string, g'') := NameGen.get_new g' in
      let fresh_name := {| P4String.str := fresh_string;
                           P4String.tags := tags |} in
      let hoist := DeclInstantiation tags typ args' fresh_name [] in
      let expr' := ExpName (Typed.BareName fresh_name) NoLocator in
      (g'', List.app rec_hoist [hoist], new_expr expr')
    | _ => (g, [],e)
    end.

  Definition hoist_expression_inner (e : @Expression tags_t) (acc : (NameGen.t * list (@Declaration tags_t) * list (@Expression tags_t))) :=
    let '(g, hoists, es) := acc in
    let '(g', hoist, e') := hoist_expression g e in
    (g', List.app hoist hoists, e' :: es).

  Definition hoist_expression_list (g : NameGen.t) : (list (@Expression tags_t)) -> (NameGen.t * list (@Declaration tags_t) * list (@Expression tags_t)) :=
    List.fold_right hoist_expression_inner (g, [],[]).

  Definition hoist_decl (g : NameGen.t) (d : @Declaration tags_t) : result (NameGen.t * list (@Declaration tags_t)) :=
    match d with
    | DeclInstantiation tags type args name init =>
      let '(g', hoist, new_args) := hoist_expression_list g args in
      let d' := DeclInstantiation tags type new_args name init in
      ok (g, List.app hoist [d'])
    | _ => ok (g, [d])
    end.

  Definition hoist_decl_inner (d : @Declaration tags_t) (acc : result (NameGen.t * list (@Declaration tags_t))) : result (NameGen.t * list (@Declaration tags_t)) :=
    let* (g, ds) := acc in
    let+ (g', hoisted) := hoist_decl g d in
    (g, List.app hoisted ds).

  Definition hoist_nameless_instantiations (p : @program tags_t) : result (@program tags_t) :=
    let '(Program decls) := p in
    let+ (_,hoisted_decls) := List.fold_right (hoist_decl_inner) (ok (NameGen.init,[])) decls in
    Program hoisted_decls.

End Nameless.
