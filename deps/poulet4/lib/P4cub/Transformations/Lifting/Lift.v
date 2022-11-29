From Coq Require Import Strings.String
  NArith.BinNat Arith.PeanoNat.
From Poulet4 Require Import
     P4cub.Syntax.AST P4cub.Syntax.Auxiliary
     P4cub.Syntax.CubNotations P4cub.Syntax.Shift
     P4cub.Syntax.IndPrincip
     P4cub.Transformations.Lifting.Statementize
     Utils.ForallMap.
Import ListNotations AllCubNotations Nat.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Goal forall e es,
    shift_pairs shift_e [(e,es)] = [(e,es)].
Proof.
  intros; cbn; rewrite shift_e_0 , shift_elist_0. reflexivity.
Qed.

Goal forall e1 e2 es1 es2,
    shift_pairs shift_e [(e2,es2);(e1,es1)]
    = [(shift_e (Shifter (length es2) (length es1)) e2,
         shift_list shift_e (Shifter 0 (length es1)) es2);
       (shift_e (Shifter 0 (length es2)) e1, es1)].
Proof.
  intros; unravel.
  rewrite add_0_r, shift_elist_0, shift_e_0.
  reflexivity.
Qed.

Goal forall e1 e2 e3 es1 es2 es3,
    shift_pairs shift_e [(e3,es3);(e2,es2);(e1,es1)]
    = [(shift_e (Shifter (length es3) (length es2 + length es1)) e3,
            shift_list shift_e (Shifter 0 (length es2 + length es1)) es3);
       (shift_e (Shifter 0 (length es3)) (shift_e (Shifter (length es2) (length es1)) e2),
         shift_list shift_e (Shifter 0 (length es1)) es2);
       (shift_e (Shifter 0 (length es3 + length es2)) e1, es1)].
Proof.
  intros; unravel.
  rewrite add_0_r, shift_elist_0, shift_e_0, shift_e_add.
  reflexivity.
Qed.
       
Inductive Lift_e
  : Expr.e -> Expr.e -> list Expr.e -> Prop :=
| Lift_bool (b : bool) :
  Lift_e b b []
| Lift_var t og x :
  Lift_e (Expr.Var t og x) (Expr.Var t og x) []
| Lift_bit w n :
  Lift_e (w `W n) (Expr.Var (Expr.TBit w) "" 0) [w `W n]
| Lift_int w z :
  Lift_e (w `S z) (Expr.Var (Expr.TInt w) "" 0) [w `S z]
| Lift_member t x e e' es :
  Lift_e e e' es ->
  Lift_e (Expr.Member t x e) (Expr.Member t x e') es
| Lift_uop t o e e' es :
  Lift_e e e' es ->
  Lift_e (Expr.Uop t o e) (Expr.Var t "" 0) (Expr.Uop t o e' :: es)
| Lift_slice hi lo e e' es :
  Lift_e e e' es ->
  Lift_e
    (Expr.Slice hi lo e)
    (Expr.Var (Expr.TBit (Npos hi - Npos lo + 1)%N) "" 0)
    (Expr.Slice hi lo e' :: es)
| Lift_cast t e e' es :
  Lift_e e e' es ->
  Lift_e (Expr.Cast t e) (Expr.Var t "" 0) (Expr.Cast t e' :: es)
| Lift_index t e1 e2 e1' e2' es1 es2 :
  Lift_e e1 e1' es1 ->
  Lift_e e2 e2' es2 ->
  Lift_e
    (Expr.Index t e1 e2)
    (Expr.Index
       t
       (shift_e (Shifter 0 (length es2)) e1')
       (shift_e (Shifter (length es2) (length es1)) e2'))
    (shift_list shift_e (Shifter 0 (length es1)) es2 ++ es1)
| Lift_bop t o e1 e2 e1' e2' es1 es2 :
  Lift_e e1 e1' es1 ->
  Lift_e e2 e2' es2 ->
  Lift_e
    (Expr.Bop t o e1 e2)
    (Expr.Var t "" 0)
    (Expr.Bop
       t o
       (shift_e (Shifter 0 (length es2)) e1')
       (shift_e (Shifter (length es2) (length es1)) e2')
       :: shift_list shift_e (Shifter 0 (length es1)) es2 ++ es1)
| Lift_lists ls es es' ess :
  Forall3 Lift_e es es' ess ->
  Lift_e
    (Expr.Lists ls es)
    (Expr.Var (t_of_lists ls es) "" 0)
    (Expr.Lists ls (map fst (shift_pairs shift_e (combine es' ess)))
       :: concat (map snd (shift_pairs shift_e (combine es' ess)))).

Variant Lift_arg :
  Expr.arg -> Expr.arg -> list Expr.e -> Prop :=
  | Lift_pain e e' es :
    Lift_e e e' es ->
    Lift_arg (PAIn e) (PAIn e') es
  | Lift_paout e e' es :
    Lift_e e e' es ->
    Lift_arg (PAOut e) (PAOut e') es
  | Lift_painout e e' es :
    Lift_e e e' es ->
    Lift_arg (PAInOut e) (PAInOut e') es.

Variant Lift_trans :
  Parser.trns -> Parser.trns -> list Expr.e ->  Prop :=
  | Lift_direct lbl :
    Lift_trans (Parser.Direct lbl) (Parser.Direct lbl) []
  | Lift_select e e' es d cases :
    Lift_e e e' es ->
    Lift_trans
      (Parser.Select e d cases)
      (Parser.Select e' d cases) es.

Variant Lift_fun_kind :
  Stmt.fun_kind -> Stmt.fun_kind -> list Expr.e -> Prop :=
  | Lift_funct_none f τs :
    Lift_fun_kind (Stmt.Funct f τs None) (Stmt.Funct f τs None) []
  | Lift_method_none ext mtd τs :
    Lift_fun_kind
      (Stmt.Method ext mtd τs None)
      (Stmt.Method ext mtd τs None) []
  | Lift_funct_some f τs e e' es :
    Lift_e e e' es ->
    Lift_fun_kind
      (Stmt.Funct f τs (Some e))
      (Stmt.Funct f τs (Some e')) es
  | Lift_method_some ext mtd τs e e' es :
    Lift_e e e' es ->
    Lift_fun_kind
      (Stmt.Method ext mtd τs (Some e))
      (Stmt.Method ext mtd τs (Some e')) es
  | Lift_action_call a cargs cargs' ess :
    Forall3 Lift_e cargs cargs' ess ->
    Lift_fun_kind
      (Stmt.Action a cargs)
      (Stmt.Action a (map fst (shift_pairs shift_e (combine cargs' ess))))
      (concat (map snd (shift_pairs shift_e (combine cargs' ess)))).

Inductive Lift_s : Stmt.s -> Stmt.s -> Prop :=
| Lift_skip :
  Lift_s Stmt.Skip Stmt.Skip
| Lift_exit :
  Lift_s Stmt.Exit Stmt.Exit
| Lift_invoke t :
  Lift_s (Stmt.Invoke t) (Stmt.Invoke t)
| Lift_return_none :
  Lift_s (Stmt.Return None) (Stmt.Return None)
| Lift_return_some e e' es :
  Lift_e e e' es ->
  Lift_s
    (Stmt.Return (Some e))
    (Unwind es (Stmt.Return (Some e')))
| Lift_transition e e' es :
  Lift_trans e e' es ->
  Lift_s
    (Stmt.Transition e)
    (Unwind es (Stmt.Transition e'))
| Lift_asgn e1 e2 e1' e2' es1 es2 :
  Lift_e e1 e1' es1 ->
  Lift_e e2 e2' es2 ->
  Lift_s
    (e1 `:= e2)
    (Unwind
       (shift_list shift_e (Shifter 0 (length es1)) es2 ++ es1)
       (shift_e (Shifter 0 (length es2)) e1'
          `:= shift_e (Shifter (length es2) (length es1)) e2'))
| Lift_call fk fk' fkes args args' argsess :
  Lift_fun_kind fk fk' fkes ->
  Forall3 Lift_arg args args' argsess ->
  Lift_s
    (Stmt.Call fk args)
    (Unwind
       (shift_list shift_e (Shifter 0 (length (concat argsess))) fkes
          ++ concat (map snd (shift_pairs shift_arg (combine args' argsess))))
       (Stmt.Call
           (shift_fun_kind (Shifter (length fkes) (length (concat argsess))) fk')
           (map (shift_arg $ Shifter 0 (length fkes))
              (map fst (shift_pairs shift_arg (combine args' argsess))))))
(*| Lift_apply x exts args args' argsess :
  Forall3 Lift_arg arg args' argsess ->
  Lift_s
    (Stmt.Apply x exts args)
    (Unwind
       (map snd (shift_pairs shift_arg (combine args' argsess)))
       (Stmt.Apply x exts
          (map fst (shift_pairs shift_arg (combine args' argsess)))))*)
| Lift_seq s1 s2 s1' s2' :
  Lift_s s1 s1' ->
  Lift_s s2 s2' ->
  Lift_s (s1 `; s2) (s1' `; s2')
| Lift_if e e' s1 s2 s1' s2' es :
  Lift_e e e' es ->
  Lift_s s1 s1' ->
  Lift_s s2 s2' ->
  Lift_s
    (If e Then s1 Else s2)
    (Unwind
       es
       (If e'
          Then shift_s (Shifter 0 (length es)) s1'
          Else shift_s (Shifter 0 (length es)) s2'))
| Lift_var_typ og t s s' :
  Lift_s s s' ->
  Lift_s (Stmt.Var og (inl t) s) (Stmt.Var og (inl t) s')
| Lift_var_exp og e e' s s' es :
  Lift_e e e' es ->
  Lift_s s s' ->
  Lift_s
    (Stmt.Var og (inr e) s)
    (Unwind
       es
       (Stmt.Var og (inr e') (shift_s (Shifter 1 (length es)) s'))).
