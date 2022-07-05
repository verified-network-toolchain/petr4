From Poulet4 Require Import Utils.Envn
     P4cub.Syntax.AST P4cub.Syntax.CubNotations.
Import String AllCubNotations.

Definition infer_or_nop (fs : list Expr.t) (mem : nat) (t : Expr.t) :=
  match nth_error fs mem with
  | None => t
  | Some t => t
  end.

Fixpoint inf_e  (e : Expr.e) : Expr.e :=
  match e with
  | Expr.Bool _
  | Expr.Bit _ _
  | Expr.Int _ _
  | Expr.Error _
  | Expr.Var _ _ => e
  | Expr.Slice e hi lo =>
      Expr.Slice (inf_e e) hi lo
  | Expr.Cast t e =>
      Expr.Cast t (inf_e e)
  | Expr.Uop rt op e =>
      Expr.Uop rt op (inf_e e)
  | Expr.Bop rt op e1 e2 =>
      Expr.Bop rt op (inf_e e1) (inf_e e2)
  | Expr.Struct es ob => Expr.Struct (map inf_e es) ob
  | Expr.Member (Expr.TStruct fs _ as argtype) mem arg =>
      let t := infer_or_nop fs mem argtype in
      Expr.Member t mem (inf_e arg)
  | Expr.Member t mem arg => Expr.Member t mem (inf_e arg)
  end.

Definition inf_arg : paramarg Expr.e Expr.e -> paramarg Expr.e Expr.e :=
  paramarg_map_same inf_e.

Definition inf_fun_kind (fk : Stmt.fun_kind) : Stmt.fun_kind :=
  match fk with
  | Stmt.Funct f τs ret    => Stmt.Funct f τs $ option_map inf_e ret
  | Stmt.Method e m τs ret => Stmt.Method e m τs $ option_map inf_e ret
  | Stmt.Action a cargs    => Stmt.Action a $ map inf_e cargs
  end.

Definition inf_transition  (transition : Parser.e) :=
  match transition with
  | Parser.Goto s =>
      Parser.Goto s
  | Parser.Select discriminee default cases =>
      Parser.Select
        (inf_e discriminee)
        default cases
  end.

Fixpoint inf_s  (s : Stmt.s) : Stmt.s :=
  match s with
  | Stmt.Skip
  | Stmt.Exit => s
  | Stmt.Invoke t es => Stmt.Invoke t $ map inf_e es
  | Stmt.Return e      => Stmt.Return $ option_map inf_e e
  | Stmt.Transition e  => Stmt.Transition $ inf_transition e
  | (lhs `:= rhs)%stmt => (inf_e lhs `:= inf_e rhs)%stmt
  | Stmt.Call fk args
    => Stmt.Call (inf_fun_kind fk) $ map inf_arg args
  | Stmt.Apply ci ext_args args =>
      let args' := map inf_arg args in
      Stmt.Apply ci ext_args args
  | Stmt.Var e s => Stmt.Var (map_sum id inf_e e) $ inf_s s
  | (s1 `; s2)%stmt => (inf_s s1 `; inf_s s2)%stmt
  | (If g Then tru Else fls)%stmt
    => (If inf_e g Then inf_s tru Else inf_s fls)%stmt
  end.

Definition inf_carg
           (carg : TopDecl.constructor_arg)
  : TopDecl.constructor_arg :=
  match carg with
  | TopDecl.CAName _ => carg
  | TopDecl.CAExpr e => inf_e e
  end.

Definition inf_Cd  (d : Control.d) :=
  match d with
  | Control.Action a cps dps body =>
      Control.Action a cps dps $ inf_s body
  | Control.Table _ _ _ => d
  end.

Definition inf_d  (d : TopDecl.d) : TopDecl.d :=
  match d with
    | TopDecl.Extern _ _ _ _ => d
  | TopDecl.Instantiate cname type_args cargs =>
      let cargs' := map inf_carg cargs in
      TopDecl.Instantiate cname type_args cargs'
  | TopDecl.Control cname cparams eparams params body apply_blk =>
      let body' := map inf_Cd body in
      let apply_blk' := inf_s apply_blk in
      TopDecl.Control cname cparams eparams params body' apply_blk'
  | TopDecl.Parser pn cps eps ps strt sts =>
      let start' := inf_s strt in
      let states' := map inf_s sts in
      TopDecl.Parser pn cps eps ps start' states'
  | TopDecl.Funct f tparams params body =>
      let body' := inf_s body in
      TopDecl.Funct f tparams params body'
  end.
