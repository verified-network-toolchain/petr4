(** This file is based on FirstOrder.v from mirrorsolve but avoids
    using dependently typed syntax.  *)
Require Import Coq.Strings.String.
Require Import Poulet4.P4flat.Sig.
Require Import Poulet4.Monads.Monad.
Require Import Poulet4.Monads.Option.
Require Import Coq.Classes.EquivDec.
Require Import Poulet4.Utils.AList.

Section FOL.
  Variable (var: Type).
  Context `{Equivalence var eq}.
  Context `{EqDec var eq}.
  Variables (sort_sym fun_sym rel_sym: vocab).
  Context `{@EqDec fun_sym eq eq_equivalence}.
  Context `{@EqDec rel_sym eq eq_equivalence}.
  Context `{@EqDec sort_sym eq eq_equivalence}.
  Variable (sig: signature sort_sym fun_sym rel_sym).

  (* First-order terms (either functions or variables). *)
  Inductive tm: Type :=
  | TVar (v: var)
  | TFun (f: fun_sym)
         (args: list tm).

  Definition ctx :=
    AList var sort_sym eq.

  Definition check_tm (c: ctx) (t: tm) : option sort_sym :=
    match t with
    | TVar v =>
        AList.get c v
    | TFun f args =>
        let* '(arg_sorts, ret_sort) := AList.get sig.(sig_funs) f in
        mret ret_sort
    end.

  (* Quantifier-free formulas. *)
  Inductive fm: Type :=
  (* True and False *)
  | FTrue
  | FFalse
  (* Equality *)
  | FEq (t1 t2: tm)
  (* A relation (with arguments) *)
  | FRel (r: rel_sym)
         (args: list tm)
  (* Negation, disjunction, conjunction, and implication *)
  | FNeg (f: fm)
  | FOr (f1 f2: fm)
  | FAnd (f1 f2: fm)
  | FImpl (f1 f2: fm).

  Fixpoint tm_subst (x: var) (e: tm) (t: tm) : tm :=
    match t with
    | TVar v =>
        if v == x then e else t
    | TFun f args =>
        TFun f (List.map (tm_subst x e) args)
    end.

  Fixpoint fm_subst (x: var) (e: tm) (f: fm) : fm :=
    match f with
    | FTrue
    | FFalse => f
    | FEq t1 t2 =>
        FEq (tm_subst x e t1)
            (tm_subst x e t2)
    | FRel r args =>
        FRel r (List.map (tm_subst x e) args)
    | FNeg f =>
        FNeg (fm_subst x e f)
    | FOr f1 f2 =>
        FOr (fm_subst x e f1)
            (fm_subst x e f2)
    | FAnd f1 f2 =>
        FAnd (fm_subst x e f1)
             (fm_subst x e f2)
    | FImpl f1 f2 =>
        FImpl (fm_subst x e f1)
              (fm_subst x e f2)
    end.

End FOL.

Arguments TVar {var fun_sym}.
Arguments TFun {var fun_sym}.
Arguments FEq {var fun_sym rel_sym}.
Arguments FRel {var fun_sym rel_sym}.
Arguments FNeg {var fun_sym rel_sym}.
Arguments FOr {var fun_sym rel_sym}.
Arguments FAnd {var fun_sym rel_sym}.
Arguments FImpl {var fun_sym rel_sym}.
Arguments tm_subst {var _ _ fun_sym} x e t.
Arguments fm_subst {var _ _ fun_sym rel_sym} x e f.

Fixpoint tm_map_vars {V W fun_sym} (m: V -> W) (t: tm V fun_sym) : tm W fun_sym :=
  match t with
  | TVar v => TVar (m v)
  | TFun f args => TFun f (List.map (tm_map_vars m) args)
  end.

Fixpoint fm_map_vars {V W fun_sym rel_sym} (m: V -> W) (f: fm V fun_sym rel_sym) : fm W fun_sym rel_sym :=
  match f with
  | FTrue _ _ _ => FTrue _ _ _
  | FFalse _ _ _ => FFalse _ _ _
  | FEq t1 t2 => FEq (tm_map_vars m t1) (tm_map_vars m t2)
  | FRel r args => FRel r (List.map (tm_map_vars m) args)
  | FNeg f => fm_map_vars m f
  | FOr f1 f2 => FOr (fm_map_vars m f1) (fm_map_vars m f2)
  | FAnd f1 f2 => FAnd (fm_map_vars m f1) (fm_map_vars m f2)
  | FImpl f1 f2 => FImpl (fm_map_vars m f1) (fm_map_vars m f2)
  end.
