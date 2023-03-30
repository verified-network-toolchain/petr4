From Poulet4 Require Import Utils.Envn
     P4cub.Syntax.AST P4cub.Syntax.CubNotations.
Import String.

Definition infer_or_nop (fs : list Typ.t) (mem : nat) (t : Typ.t) :=
  match nth_error fs mem with
  | None => t
  | Some t => t
  end.

Fixpoint inf_exp  (e : Exp.t) : Exp.t :=
  match e with
  | Exp.Bool _
  | Exp.Bit _ _
  | Exp.VarBit _ _ _
  | Exp.Int _ _
  | Exp.Error _
  | Exp.Var _ _ _ => e
  | Exp.Slice hi lo e =>
      Exp.Slice hi lo $ inf_exp e
  | Exp.Cast t e =>
      Exp.Cast t $ inf_exp e
  | Exp.Uop rt op e =>
      Exp.Uop rt op $ inf_exp e
  | Exp.Bop rt op e1 e2 =>
      Exp.Bop rt op (inf_exp e1) $ inf_exp e2
  | Exp.Lists l es => Exp.Lists l $ List.map inf_exp es
  | Exp.Index t e1 e2 => Exp.Index t (inf_exp e1) $ inf_exp e2
  | Exp.Member (Typ.Struct _ fs as argtype) mem arg =>
      let t := infer_or_nop fs mem argtype in
      Exp.Member t mem (inf_exp arg)
  | Exp.Member t mem arg => Exp.Member t mem $ inf_exp arg
  end.

Definition inf_arg : paramarg Exp.t Exp.t -> paramarg Exp.t Exp.t :=
  paramarg_map_same inf_exp.

Definition inf_call (c : Call.t) : Call.t :=
  match c with
  | Call.Funct f τs ret    => Call.Funct f τs $ option_map inf_exp ret
  | Call.Method e m τs ret => Call.Method e m τs $ option_map inf_exp ret
  | Call.Action a cargs    => Call.Action a $ map inf_exp cargs
  | Call.Inst _ _          => c
  end.

Definition inf_trns  (transition : Trns.t) :=
  match transition with
  | Trns.Direct s =>
      Trns.Direct s
  | Trns.Select discriminee default cases =>
      Trns.Select
        (inf_exp discriminee)
        default cases
  end.

Fixpoint inf_stm  (s : Stm.t) : Stm.t :=
  match s with
  | Stm.Skip
  | Stm.Exit          => s
  | Stm.Ret e      => Stm.Ret $ option_map inf_exp e
  | Stm.Trans e  => Stm.Trans $ inf_trns e
  | (lhs `:= rhs)%stm => (inf_exp lhs `:= inf_exp rhs)%stm
  | Stm.Invoke e t
    => Stm.Invoke (option_map inf_exp e) t
  | Stm.App fk args
    => Stm.App (inf_call fk) $ map inf_arg args
  | (`let x := e `in s)%stm => (`let x := map_sum id inf_exp e `in inf_stm s)%stm
  | (s1 `; s2)%stm => (inf_stm s1 `; inf_stm s2)%stm
  | (`if g `then tru `else fls)%stm
    => (`if inf_exp g `then inf_stm tru `else inf_stm fls)%stm
  end.

Definition inf_Cd  (d : Ctrl.t) :=
  match d with
  | Ctrl.Var og te =>
      Ctrl.Var og $ map_sum id inf_exp te
  | Ctrl.Action a cps dps body =>
      Ctrl.Action a cps dps $ inf_stm body
  | Ctrl.Table t key acts def =>
      Ctrl.Table
        t (map (fun '(e,mk) => (inf_exp e, mk)) key)
        (map (fun '(a,args) => (a, map inf_arg args)) acts)
        $ option_map (fun '(x,es) => (x, map inf_exp es)) def
  end.

Definition inf_top  (d : Top.t) : Top.t :=
  match d with
  | Top.Extern _ _ _ _ _ => d
  | Top.Instantiate cname iname type_args cargs expr_cargs =>
      let expr_cargs' := map inf_exp expr_cargs in
      Top.Instantiate cname iname type_args cargs expr_cargs'
  | Top.Control cname cparams expr_cparams eparams params body apply_blk =>
      let body' := map inf_Cd body in
      let apply_blk' := inf_stm apply_blk in
      Top.Control cname cparams expr_cparams eparams params body' apply_blk'
  | Top.Parser pn cps expr_cparams eps ps strt sts =>
      let start' := inf_stm strt in
      let states' := map inf_stm sts in
      Top.Parser pn cps expr_cparams eps ps start' states'
  | Top.Funct f tparams params body =>
      let body' := inf_stm body in
      Top.Funct f tparams params body'
  end.
