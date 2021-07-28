Require Import Coq.Program.Basics.
Require Export Poulet4.P4cub.Syntax.AST.
Require Export Poulet4.P4Arith.
Require Export Poulet4.P4cub.Envn.
Require Export Poulet4.P4cub.BigStep.InstUtil.
Require Export Poulet4.P4cub.BigStep.BigStep.
Require Export Poulet4.P4cub.BigStep.Semantics.
Require Export Poulet4.P4cub.BigStep.Value.Value.

Import Env.EnvNotations.

(** * VCS *)
Module GCL.
  Module P := P4cub.
  Module ST := P.Stmt.
  Module E := P.Expr.
  Module F := P.F.

  Variable tags_t : Type.

  Inductive ir : Type :=
  | IRSkip (i : tags_t)
  | IRAssign (type : E.t) (lhs rhs : E.e tags_t) (i : tags_t)
  | IRConditional (guard : E.e tags_t) (tru_blk fls_blk : ir) (i : tags_t)
  | IRSeq (c1 c2 : ir)
  | IRAssume (phi : E.e tags_t)
  | IRAssert (phi : E.e tags_t)
  | IRFunCall (f : string) (args : ST.E.arrowE tags_t) (body : ir) (i : tags_t).

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

  Infix "<$>" := omap (at level 80, right associativity).

  Print fdecl.
  Print ST.SFunCall.
  Print Env.consume.

  Print fenv.
  Print fold_right.


  Print fdecl.
  Inductive inln_fdecl :=
  | FDeclInln (s : ST.s tags_t).

  Definition inln_fenv := Env.t string inln_fdecl.
  Fixpoint ir_ify_inline (s : ST.s tags_t) : option ir :=
    match s with
    | ST.SSkip i => Some (IRSkip i)
    | ST.SVardecl _ _ i => Some (IRSkip i)
    | ST.SAssign type lhs rhs i =>
      Some (IRAssign type lhs rhs i)
    | ST.SConditional guard_type guard tru_blk fls_blk i =>
      let tru_blk' := ir_ify_inline tru_blk in
      let fls_blk' := ir_ify_inline fls_blk in
      liftO2 (fun t f => IRConditional guard t f i) tru_blk' fls_blk'
    | ST.SSeq s1 s2 i =>
      let ir1 := ir_ify_inline s1 in
      let ir2 := ir_ify_inline s2 in
      liftO2 IRSeq ir1 ir2
    | ST.SBlock s =>
      ir_ify_inline s
    | _ => None
    end.

  Fixpoint ir_ify (fenv : inln_fenv) (s : ST.s tags_t) {struct s}: option ir :=
    match s with
    | ST.SSkip i => Some (IRSkip i)
    | ST.SVardecl _ _ i => Some (IRSkip i)
    | ST.SAssign type lhs rhs i =>
      Some (IRAssign type lhs rhs i)
    | ST.SConditional guard_type guard tru_blk fls_blk i =>
      let tru_blk' := ir_ify fenv tru_blk in
      let fls_blk' := ir_ify fenv fls_blk in
      liftO2 (fun t f => IRConditional guard t f i) tru_blk' fls_blk'
    | ST.SSeq s1 s2 i =>
      let ir1 := ir_ify fenv s1 in
      let ir2 := ir_ify fenv s2 in
      liftO2 IRSeq ir1 ir2
    | ST.SBlock s =>
      ir_ify fenv s
    | ST.SFunCall f args i =>
      let (fopt, fenv') := (Env.consume f fenv) in
      fopt >>= fun fdecl =>
      match fdecl with
      | (FDeclInln body) =>
        let ir_bod := ir_ify_inline body in
        (fun b => IRFunCall f args b i) <$> ir_bod
      end
    | ST.SActCall f args i =>
      Some (IRSkip i)
    | ST.SApply x args i =>
      Some (IRSkip i)

    | ST.SReturnVoid i =>
      Some (IRSkip i)
    | ST.SReturnFruit typ expr i =>
      Some (IRSkip i)
    | ST.SExit i =>
      Some (IRSkip i)
    | ST.SInvoke x i =>
      Some (IRSkip i)

    | ST.SExternMethodCall _ _ _ i =>
      Some (IRSkip i)
    end.
