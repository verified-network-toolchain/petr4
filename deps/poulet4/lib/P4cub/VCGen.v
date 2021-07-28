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
  (* | IRAssume (phi : E.e tags_t) *)
  (* | IRAssert (phi : E.e tags_t) *)
  | IRFunCall (f : string) (args : ST.E.arrowE tags_t) (fenv : @fenv tags_t) (body : ST.s tags_t) (i : tags_t).

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
  Print aenv.
  Print adecl.
  Fixpoint ir_ify (fenv : fenv) (s : ST.s tags_t) {struct s}: option ir :=
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
      let (fopt, _) := (Env.consume f fenv) in
      fopt >>= fun fdecl =>
      match fdecl with
      | (FDecl _ fenv body) =>
        Some (IRFunCall f args fenv body i)
      end
    | ST.SActCall a args i =>
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

  Fixpoint size (ir : ir) : nat * nat :=
    match ir with
    | IRSkip i => (0, 0)
    | IRAssign type lhs rhs i => (0, 1)
    | IRConditional guard tru_blk fls_blk i =>
      let (fenv_sz_tru, ast_sz_tru) := size tru_blk in
      let (fenv_sz_fls, ast_sz_fls) := size fls_blk in
      (fenv_sz_tru + fenv_sz_fls, ast_sz_tru + 1 + ast_sz_fls)
    | IRSeq ir1 ir2 =>
      let (fenv_sz1, ast_sz1) := size ir1 in
      let (fenv_sz2, ast_sz2) := size ir2 in
      (max fenv_sz1 fenv_sz2, ast_sz1 + ast_sz2)
    | IRFunCall _ _ fenv _ _ =>
      (length fenv, 1)
    end.

  Definition p_lt (m1 : (nat * nat)) (m2 : (nat * nat)) : Prop :=
    let (x1, y1) := m1 in
    let (x2, y2) := m2 in
    x1 < x2 \/ (x1 = x2 /\ y1 < y2).

  Set Printing All.
  Program Fixpoint ir_to_gcl (ir : ir) {measure (size ir) p_lt } : option t :=
    match ir with
    | IRSkip i => Some (GSkip i)
    | IRAssign type lhs rhs i =>
      Some (GAssign type lhs rhs i)
    | IRConditional guard tru_blk fls_blk i =>
      let tru_blk' := ir_to_gcl tru_blk in
      let fls_blk' := ir_to_gcl fls_blk in
      liftO2 (fun t f => GConditional guard t f i) tru_blk' fls_blk'
    | IRSeq s1 s2 =>
      let ir1 := ir_to_gcl s1 in
      let ir2 := ir_to_gcl s2 in
      liftO2 GSeq ir1 ir2
    | IRFunCall f args fenv body i =>
      let (_, fenv') := Env.consume f fenv in
      ir_ify fenv' body >>= ir_to_gcl
    (* | IRActCall a args i => *)
    (*   Some (GSkip i) *)
    (* | IRApply x args i => *)
    (*   Some (GSkip i) *)

    (* | IRReturnVoid i => *)
    (*   Some (GSkip i) *)
    (* | IRReturnFruit typ expr i => *)
    (*   Some (GSkip i) *)
    (* | IRExit i => *)
    (*   Some (GSkip i) *)
    (* | IRInvoke x i => *)
    (*   Some (GSkip i) *)

    (* | IRExternMethodCall _ _ _ i => *)
    (*   Some (GSkip i) *)
    end.

  Next Obligation.
    unfold p_lt.
    simpl.
    destruct (size tru_blk).
    destruct (size fls_blk).
    destruct n1.
    - right.
      * split.
        + auto.
        + intuition.
    - left. intuition.
  Qed.

  Next Obligation.
    unfold p_lt.
    simpl.
    destruct (size tru_blk).
    destruct (size fls_blk).
    destruct n.
    - right. intuition.
    - left. intuition.
  Qed.
