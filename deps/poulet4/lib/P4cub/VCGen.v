Require Import Coq.Program.Basics.
Require Export Poulet4.P4cub.Syntax.AST.
Require Export Poulet4.P4Arith.
Require Export Poulet4.P4cub.Envn.
Require Export Poulet4.P4cub.BigStep.InstUtil.
Require Export Poulet4.P4cub.BigStep.BigStep.
Require Export Poulet4.P4cub.BigStep.Semantics.
Require Export Poulet4.P4cub.BigStep.Value.Value.

Require Import Coq.Arith.EqNat.
Require Import String.
Open Scope string_scope.

Import Env.EnvNotations.

(** Compile to GCL *)
Module GCL.
  Module P := P4cub.
  Module ST := P.Stmt.
  Module CD := P.Control.ControlDecl.
  Module E := P.Expr.
  Module F := P.F.

  Variable tags_t : Type.

  Inductive t : Type :=
  | GSkip (i : tags_t)
  | GAssign (type : E.t) (lhs rhs : E.e tags_t) (i : tags_t)
  | GConditional (guard : E.e tags_t) (tru_blk fls_blk : t) (i : tags_t)
  | GSeq (c1 c2 : t)
  | GAssume (phi : E.e tags_t)
  | GAssert (phi : E.e tags_t).

  Print option.
  Definition obind {A B : Type} (o : option A) (f : A -> option B) : option B :=
    match o with
    | None => None
    | Some x => f x
    end.
  Definition omap {A B : Type} (f : A ->  B)  (o : option A) : option B :=
    match o with
    | None => None
    | Some x => Some (f x)
    end.
  Definition liftO2 {A B C : Type} (f : A -> B -> C) (o1 : option A) (o2 : option B) : option C :=
    obind o1 (fun x1 => obind o2 (fun x2 => Some (f x1 x2))).

  Definition union {A : Type} (oo : option (option A)) : option A :=
    match oo with
    | Some (Some x) => Some x
    | _ => None
    end.

  Definition bindO2 {A B C : Type} (f : A -> B -> option C) (o1 : option A) (o2 : option B) : option C :=
    union (liftO2 f o1 o2).

  Infix "<$>" := omap (at level 80, right associativity).
  Notation "'let**' p ':=' c1 'in' c2" := (omap (fun p => c2) c1)
                 (at level 61, p as pattern, c1 at next level, right associativity).

  (** NOTE: the arument n is an unrolling hack for now. If you need to the n such  *)
  (** that ir_to_gcl terminates, just assum exists n. ir_to_gcl n != None. *)
  Print List.
  Record block_ctx : Type :=
    mkCtx { stack : list string; (* The current block stack *)
            may_have_exited: bool;
            may_have_returned: bool;
          }.

  Definition incr (ctx : block_ctx) (name : string) : block_ctx :=
    {| stack := name :: ctx.(stack);
       may_have_exited := ctx.(may_have_exited);
       may_have_returned := false;
    |}
  .
  Definition current (ctx : block_ctx) : option string :=
    match ctx.(stack) with
    | [] => None
    | name :: _ => Some name
    end.

  Definition decr_ctx (f : string) (old_ctx : block_ctx) (ret : t * block_ctx)  : option (t * block_ctx) :=
    match ret with
    | (g, ctx) =>
      match ctx.(stack) with
      | [] => None
      | idx :: idxs =>
        if String.eqb idx f
        then let ctx' := {| stack := idxs;
                            may_have_exited := old_ctx.(may_have_exited) || ctx.(may_have_exited);
                            may_have_returned := old_ctx.(may_have_returned);
                         |} in
             Some (g, ctx')
        else None
      end
    end.

  Definition exit (i : tags_t) : E.e tags_t := E.EVar E.TBool "exit" i.
  Definition etrue (i : tags_t) : E.e tags_t := E.EBool true i.
  Definition efalse (i : tags_t) : E.e tags_t := E.EBool false i.

  Definition update_exit (ctx : block_ctx) (b : bool) :=
    {| stack := ctx.(stack);
       may_have_exited := b;
       may_have_returned := ctx.(may_have_returned)
    |}.

  Fixpoint list_eq {A : Type} (eq : A -> A -> bool) (s1 s2 : list A) : bool  :=
    match s1,s2 with
    | [], [] => true
    | _, [] => false
    | [], _ => false
    | x::xs, y::ys => andb (eq x y) (list_eq eq xs ys)
    end.

  Definition ctx_cond (tctx fctx : block_ctx) : option block_ctx :=
    if list_eq String.eqb tctx.(stack) fctx.(stack)
    then Some {| stack := tctx.(stack);
                 may_have_exited := tctx.(may_have_exited) || fctx.(may_have_exited);
                 may_have_returned := tctx.(may_have_returned) || fctx.(may_have_returned)
              |}
    else None.

  Definition cond (guard : E.e tags_t) (i : tags_t) (tres fres : (t * block_ctx)) : option (t * block_ctx) :=
    let (tg, tctx) := tres in
    let (fg, fctx) := fres in
    let* ctx := ctx_cond tctx fctx in
    Some (GConditional guard tg fg i, ctx).

  Definition retvar_name (ctx : block_ctx) : string :=
    fold_right (String.append) "" ctx.(stack).

  Definition retvar (ctx : block_ctx) (i : tags_t) : E.e tags_t :=
    E.EVar E.TBool (retvar_name ctx) i.

  Definition seq (i : tags_t) (res1 res2 : (t * block_ctx)) : t * block_ctx :=
    let (g1, ctx1) := res1 in
    let (g2, ctx2) := res2 in
    let g :=
        if ctx1.(may_have_returned)
        then GSeq g1 (GConditional (retvar ctx1 i) (GSkip i) g2 i)
        else GSeq g1 g2 in
    (g, ctx2).

  Fixpoint zip {A B : Type} (xs : list A) (ys : list B) : option (list (A * B)) :=
    match xs, ys with
    | [],[] => Some []
    | [], _ => None
    | _, [] => None
    | x::xs, y::ys =>
      cons (x,y) <$> zip xs ys
    end.

  Fixpoint ored {A : Type} (xs : list (option A)) : option (list A) :=
    match xs with
    | [] => Some []
    | (Some x) :: xs => cons x <$> ored xs
    | None :: _ => None
    end.

  Module Translate.
    Variable instr : (string -> tags_t -> list (E.t * E.e tags_t * E.matchkind) -> list (EquivUtil.string * t) -> t).

    Fixpoint to_gcl (n : nat)
             (ctx : block_ctx)
             (cienv : @cienv tags_t)
             (aenv : @aenv tags_t)
             (tenv : @tenv tags_t)
             (fenv : fenv)
             (s : ST.s tags_t)
             {struct n} : option (t * block_ctx) :=
      match n with
      | 0 => None
      | S n0 =>
        match s with
        | ST.SSkip i =>
          Some (GSkip i, ctx)

        | ST.SVardecl _ _ i =>
          (** TODO: Handle scoping, using var decls as a signal *)
          Some (GSkip i, ctx)

        | ST.SAssign type lhs rhs i =>
          Some (GAssign type lhs rhs i, ctx)

        | ST.SConditional _ guard tru_blk fls_blk i =>
          let tru_blk' := to_gcl n0 ctx cienv aenv tenv fenv tru_blk in
          let fls_blk' := to_gcl n0 ctx cienv aenv tenv fenv fls_blk in
          bindO2 (cond guard i) tru_blk' fls_blk'

        | ST.SSeq s1 s2 i =>
          let g1_opt := to_gcl n0 ctx cienv aenv tenv fenv s1 in
          let g2_opt := to_gcl n0 ctx cienv aenv tenv fenv s2 in
          liftO2 (seq i) g1_opt g2_opt

        | ST.SBlock s =>
          (* TODO handle variable scope *)
          to_gcl n0 ctx cienv aenv tenv fenv s

        | ST.SFunCall f args i =>
          let* fdecl := Env.find f fenv in
          match fdecl with
          | FDecl ε fenv' body =>
            (** TODO copy-in/copy-out *)
            (** TODO handle scope *)
            let* rslt := to_gcl n0 (incr ctx f) cienv aenv tenv fenv' body in
            decr_ctx f ctx rslt
          end
        | ST.SActCall a args i =>
          let* adecl := Env.find a aenv in
          match adecl with
          | ADecl ε fenv' aenv' externs body =>
            (** TODO handle copy-in/copy-out *)
            (** TODO handle scope *)
            let* rslt := to_gcl n0 (incr ctx a) cienv aenv' tenv fenv' body in
            decr_ctx a ctx rslt
          end
        | ST.SApply ci args i =>
          let* cinst := Env.find ci cienv in
          match cinst with
          | CInst closure fenv' cienv' tenv' aenv' externs' apply_blk =>
            let* rslt := to_gcl n0 (incr ctx ci) cienv' aenv' tenv' fenv' apply_blk in
            decr_ctx ci ctx rslt
          end
        | ST.SReturnVoid i =>
          Some (GAssign E.TBool (retvar ctx i) (etrue i) i, ctx)

        | ST.SReturnFruit typ expr i =>
          Some (GAssign E.TBool (retvar ctx i) (etrue i) i, ctx)

        | ST.SExit i =>
          Some (GAssign E.TBool (exit i) (etrue i) i, update_exit ctx true)

        | ST.SInvoke t i =>
          let* tdecl := Env.find t tenv in
          match tdecl with
          | CD.Table keys actions =>
            let act_to_gcl := fun a =>
              let* adecl := Env.find a aenv in
              match adecl with
              | ADecl _ fenv' aenv' externs body =>
                (** TODO handle copy-in/copy-out *)
                let** (g, _) := to_gcl n0 (incr ctx a) cienv aenv tenv fenv body in
                g
              end
            in
            let* acts := ored (map act_to_gcl actions) in
            let** named_acts := zip actions acts in
            pair (instr t i keys named_acts) ctx
          end
        | ST.SExternMethodCall _ _ _ i =>
          None
        end
      end.
