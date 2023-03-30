(** This file is based on FirstOrder.v from mirrorsolve but avoids
    using dependently typed syntax.  *)
Require Import Coq.Strings.String.
Require Import Poulet4.P4flat.Sig.
Require Import Poulet4.Monads.Monad.
Require Import Poulet4.Monads.Option.
Require Import Poulet4.Monads.Result.
Require Import Coq.Classes.EquivDec.
Require Import Poulet4.Utils.AList.
Require Import Poulet4.Utils.Util.ListUtil.

Local Open Scope string_scope.
Local Open Scope bool_scope.

Section FOL.
  Variable (var: Type).
  Variable (var_to_string: var -> string).
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

  Definition ctx_get : ctx -> var -> result string sort_sym :=
    fun c v =>
      from_opt (AList.get c v)
               ("Variable not found in ctx.").

  Definition check_ctx (c: ctx) :=
    List.forallb (fun '(v, sort) => sig_check_sort sig sort) c.

  Fixpoint check_tm (c: ctx) (t: tm) (s: sort_sym) : bool :=
    match t with
    | TVar v =>
        match ctx_get c v with
        | Ok s' => s' ==b s
        | Error _ => false
        end
    | TFun f args =>
        match sig_get_fun sig f with
        | Ok (arg_sorts, ret_sort) =>
            (ret_sort ==b s) &&
              (fix check_tms ts ss :=
                 match ts, ss with
                 | t :: ts, s :: ss =>
                     check_tm c t s && check_tms ts ss
                 | [], [] => true
                 | _, _ => false
                 end) args arg_sorts
        | Error _ => false
        end
    end.

  Definition check_tms c :=
    fix check_tms ts ss :=
      match ts, ss with
      | t :: ts, s :: ss =>
          check_tm c t s && check_tms ts ss
      | [], [] => true
      | _, _ => false
      end.

  Definition type_tm (c: ctx) (t: tm) : result string sort_sym :=
    match t with
    | TVar v =>
        ctx_get c v
    | TFun f args =>
        let* '(arg_sorts, ret_sort) := sig_get_fun sig f in
        if check_tms c args arg_sorts
        then mret ret_sort
        else Error "Ill-sorted argument to function symbol."
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

  Fixpoint check_fm (c: ctx) (f: fm) : bool :=
    match f with
    | FTrue => true
    | FFalse => true
    | FEq t1 t2 =>
        match let* sort1 := type_tm c t1 in
              let* sort2 := type_tm c t2 in
              mret (sort1 ==b sort2) with
        | Ok b => b
        | Error _ => false
        end
    | FRel r args =>
        match let* 'arg_sorts := sig_get_rel sig r in
              mret (check_tms c args arg_sorts) with
        | Ok b => b
        | Error _ => false
        end
    | FNeg f => check_fm c f
    | FOr f1 f2 => check_fm c f1 && check_fm c f2
    | FAnd f1 f2 => check_fm c f1 && check_fm c f2
    | FImpl f1 f2 => check_fm c f1 && check_fm c f2
    end.

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
