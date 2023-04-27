Require Import Coq.Strings.String Coq.NArith.BinNat.
From Poulet4 Require Import
     P4cub.Syntax.AST P4cub.Syntax.Auxiliary
     P4cub.Syntax.CubNotations P4cub.Syntax.Shift
     Utils.ForallMap P4cub.Transformations.Lifting.LiftList.
Import ListNotations.

Open Scope nat_scope.
Open Scope string_scope.

(** [lift_e e = (l, e')],
    where e' is a lifted expression,
    & l is a list of lifted expressions. *)
Fixpoint lift_exp (e : Exp.t) {struct e}
  : Exp.t * list Exp.t :=
  match e with
  | Exp.Bool _
  | Exp.Error _
  | Exp.Var _ _ _ => (e, [])
  | Exp.Bit _ _ =>
      (Exp.Var (typ_of_exp e) "lifted_bit" 0, [e])
  | Exp.VarBit _ _ _ =>
      (Exp.Var (typ_of_exp e) "lifted_varbit" 0, [e])
  | Exp.Int _ _ =>
      (Exp.Var (typ_of_exp e) "lifted_int" 0, [e])
  | Exp.Member t x e
    => let '(e, inits) := lift_exp e in
      (Exp.Member t x e, inits)
  | Exp.Uop t op e =>
      let '(e, inits) := lift_exp e in
      (Exp.Var t "lifted_uop" 0, Exp.Uop t op e :: inits)
  | Exp.Slice hi lo e =>
      let '(e, inits) := lift_exp e in
      (Exp.Var (Typ.Bit (Npos hi - Npos lo + 1)%N) "lifted_slice" 0, Exp.Slice hi lo e :: inits)
  | Exp.Cast t e =>
      let '(e, inits) := lift_exp e in
      (Exp.Var t "lifted_cast" 0, Exp.Cast t e :: inits)
  | Exp.Index t e1 e2 =>
      let '(e1, l1) := lift_exp e1 in
      let '(e2, l2) := lift_exp e2 in
      let '(e1',e2',l2') := shift_couple shift_exp shift_exp e1 e2 l1 l2 in
      (Exp.Index t e1' e2', (l2' ++ l1)%list)
  | Exp.Bop t op e1 e2 => 
      let '(e1, l1) := lift_exp e1 in
      let '(e2, l2) := lift_exp e2 in
      let '(e1',e2',l2') := shift_couple shift_exp shift_exp e1 e2 l1 l2 in
      (Exp.Var t "lifted_bop" 0,
        Exp.Bop t op e1' e2' :: l2' ++ l1)
  | Exp.Lists l es =>
      let '(es', les) := shift_pairs shift_exp $ List.map lift_exp es in
      (Exp.Var (typ_of_lists l es) "lifted_lists" 0, Exp.Lists l es' :: concat les)
  end.

Definition lift_exp_list : list Exp.t -> list Exp.t * list Exp.t :=
  lift_A_list shift_exp lift_exp.

Definition lift_arg (arg : paramarg Exp.t Exp.t)
  : paramarg Exp.t Exp.t * list Exp.t :=
  match arg with
  | PAIn e =>
      let '(e, le) := lift_exp e in (PAIn e, le)
  | PAOut e =>
      let '(e, le) := lift_exp e in (PAOut e, le)
  | PAInOut e =>
      let '(e, le) := lift_exp e in (PAInOut e, le)
  end.

Definition lift_args : Exp.args -> Exp.args * list Exp.t :=
  lift_A_list shift_arg lift_arg.

Definition lift_args_list
  : list Exp.args -> list Exp.args * list Exp.t :=
  lift_A_list (shift_list shift_arg) lift_args.

Fixpoint Unwind (es : list Exp.t) (s : Stm.t) : Stm.t :=
  match es with
  | [] => s
  | e :: es => Unwind es (`let "unwound_var" := inr e `in s)%stm
  end.

Definition lift_trns (e : Trns.t)
  : Trns.t * list Exp.t :=
  match e with
  | Trns.Direct _ => (e,[])
  | Trns.Select e d cases
    => let '(e,le) := lift_exp e in
      (Trns.Select e d cases, le)
  end.

Definition lift_call (fk : Call.t)
  : Call.t * list Exp.t :=
  match fk with
  | Call.Funct _ _ None
  | Call.Method _ _ _ None
  | Call.Inst _ _ => (fk,[])
  | Call.Funct f τs (Some e)
    => let '(e,le) := lift_exp e in (Call.Funct f τs (Some e), le)
  | Call.Method x m τs (Some e)
    => let '(e,le) := lift_exp e in (Call.Method x m τs (Some e), le)
  | Call.Action a es
    => let '(es,les) := lift_exp_list es in (Call.Action a es, les)
  end.

Local Open Scope stm_scope.

Fixpoint lift_stm (s : Stm.t) : Stm.t :=
  match s with
  | Stm.Skip
  | Stm.Exit
  | Stm.Invoke None _
  | Stm.Ret None => s
  | Stm.Ret (Some e)
    => let '(e, le) := lift_exp e in
      Unwind le $ Stm.Ret $ Some e
  | Stm.Trans e =>
      let '(e, le) := lift_trns e in
      Unwind le $ Stm.Trans $ e
  | e1 `:= e2
    => let '(e1, le1) := lift_exp e1 in
      let '(e2, le2) := lift_exp e2 in
      let '(e1', e2', le2') := shift_couple shift_exp shift_exp e1 e2 le1 le2 in
      Unwind (le2' ++ le1) (e1' `:= e2')
  | Stm.Invoke (Some e) t
    => let '(e, le) := lift_exp e in
      Unwind le $ Stm.Invoke (Some e) t
  | Stm.App fk args
    => let '(fk,lfk) := lift_call fk in
      let '(args,largs) := lift_args args in
      let '(args, fk, lfk) := shift_couple (fun c a => map (shift_arg c a)) shift_call args fk largs lfk in
      Unwind (lfk ++ largs) (Stm.App fk args)
  | `let og := inl t `in s => `let og := inl t `in lift_stm s
  | `let og := inr e `in s =>
      let '(e,le) := lift_exp e in
      Unwind le $
        `let og := inr e `in
        shift_stm 1 (length le) $ lift_stm s
  | s₁ `; s₂ => lift_stm s₁ `; lift_stm s₂
  | `if e `then s₁ `else s₂ =>
      let '(e,le) := lift_exp e in
      Unwind
        le $ `if e `then shift_stm 0 (length le) $ lift_stm s₁
        `else shift_stm 0 (length le) $ lift_stm s₂
  end.

Local Close Scope stm_scope.

Definition lift_ctrl (cd : Ctrl.t) : list Ctrl.t * nat :=
  match cd with
  | Ctrl.Var x (inl t) => ([Ctrl.Var x $ inl t], 0)
  | Ctrl.Var x (inr e) =>
      let '(e, es) := lift_exp e in
      ((List.map (Ctrl.Var "" ∘ inr) es ++ [Ctrl.Var x $ inr e])%list, List.length es)
  | Ctrl.Action a cps dps body
    => ([Ctrl.Action a cps dps $ lift_stm body], 0)
  | Ctrl.Table t key acts def =>
      let '(es,mks) := List.split key in
      let '(acts,argss) := List.split acts in
      let '(es,ees) := lift_exp_list es in
      let '(argss,argsss) := lift_args_list argss in
      let '(def,defes) :=
        omap_effect
          []
          (fun '(a,es) => prod_map_fst (pair a) $ lift_exp_list es)
          def in
      let '(def,es,argss,ees,argsss) :=
        shift_triple
          (fun c a => option_map (prod_map_snd (List.map (shift_exp c a))))
          (fun c a => List.map (shift_exp c a))
          (fun c a => List.map (List.map (shift_arg c a)))
          def es argss defes ees argsss in
      ((List.map (Ctrl.Var "" ∘ inr) argsss
          ++ List.map (Ctrl.Var "" ∘ inr) ees
          ++ List.map (Ctrl.Var "" ∘ inr) defes
          ++ [Ctrl.Table
                t
                (List.combine es mks)
                (List.combine acts argss)
                def])%list,
        List.length ees + List.length argsss)
  end.

Fixpoint lift_ctrls (cds : list Ctrl.t) : list Ctrl.t * nat :=
  match cds with
  | [] => ([], 0)
  | d :: ds =>
      let '(d, n) := lift_ctrl d in
      let '(ds, ns) := lift_ctrls ds in
      ((d ++ shift_ctrls 0 n ds)%list, n + ns)
  end.

Definition lift_top (td : Top.t) : Top.t := 
  match td with 
  | Top.Instantiate _ _ _ _ _
  | Top.Extern _ _ _ _ _ => td
  | Top.Control c cparams expr_cparams eps params body apply_blk =>
      let (ds, n) := lift_ctrls body in
      Top.Control
        c cparams expr_cparams eps params ds
        $ shift_stm 0 n $ lift_stm apply_blk  
  | Top.Parser p cparams expr_cparams eps params start states =>
      Top.Parser
        p cparams expr_cparams eps params
        (lift_stm start) $ map lift_stm states
  | Top.Funct f tparams signature body =>
      Top.Funct f tparams signature $ lift_stm body
  end.

Definition lift_program : list Top.t -> list Top.t :=
  map lift_top.
