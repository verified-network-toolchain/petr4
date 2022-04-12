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
  | Expr.Struct es e =>
      Expr.Struct (map inf_e es) (option_map inf_e e)
  | Expr.Member (Expr.TStruct fs _ as argtype) mem arg =>
      let t := infer_or_nop fs mem argtype in
      Expr.Member t mem (inf_e arg)
  | Expr.Member t mem arg => Expr.Member t mem (inf_e arg)
  end.

Definition inf_arg (pa : paramarg Expr.e Expr.e) :=
  match pa with
  | PAIn e => PAIn (inf_e e)
  | PAOut e => PAOut (inf_e e)
  | PAInOut e => PAInOut (inf_e e)
  end.

Definition inf_arrowE  (ar : Expr.arrowE) :=
  let args := paramargs ar in
  let ret := rtrns ar in
  let args' := map inf_arg args in
  let ret' := option_map inf_e ret in
  {| paramargs := args'; rtrns := ret' |}.

Definition inf_s  (s : Stmt.s) : Stmt.s :=
  match s with
  | Stmt.Invoke _ => s
  | (lhs `:= rhs)%stmt =>
      (inf_e lhs `:= inf_e rhs)%stmt
  | Stmt.MethodCall extern_name method_name typ_args args =>
      let args' := inf_arrowE args in
      Stmt.MethodCall extern_name method_name typ_args args'
  | Stmt.FunCall f typ_args args =>
      let args' := inf_arrowE args in
      Stmt.FunCall f typ_args args'
  | Stmt.ActCall a cargs dargs =>
      Stmt.ActCall a (map inf_e cargs) (map inf_arg dargs)
  | Stmt.Apply ci ext_args args =>
      let args' := map inf_arg args in
      Stmt.Apply ci ext_args args
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

Fixpoint inf_block (b : Stmt.block) : Stmt.block :=
  match b with
  | Stmt.Skip
  | Stmt.Exit => b
  | Stmt.Var e b => Stmt.Var (map_sum id inf_e e) b
  | (If g {` tru `} Else {` fls `} `; b)%block =>
      (If inf_e g {` inf_block tru `} Else {` inf_block fls `} `; inf_block b)%block
  | (s1 `; s2)%block => (inf_s s1 `; inf_block s2)%block
  | Stmt.Block b1 b2 =>
      Stmt.Block (inf_block b1) $ inf_block b2
  | Stmt.Return e => Stmt.Return $ option_map inf_e e
  | Stmt.Transition e => Stmt.Transition $ inf_transition e
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
      Control.Action a cps dps $ inf_block body
  | Control.Table t keys acts =>
      Control.Table
        t (List.map (fun '(e,mk) => (inf_e e, mk)) keys) acts
  end.

Definition inf_d  (d : TopDecl.d) : TopDecl.d :=
  match d with
    | TopDecl.Extern _ _ _ _ => d
  | TopDecl.Instantiate cname type_args cargs =>
      let cargs' := map inf_carg cargs in
      TopDecl.Instantiate cname type_args cargs'
  | TopDecl.Control cname cparams eparams params body apply_blk =>
      let body' := map inf_Cd body in
      let apply_blk' := inf_block apply_blk in
      TopDecl.Control cname cparams eparams params body' apply_blk'
  | TopDecl.Parser pn cps eps ps strt sts =>
      let start' := inf_block strt in
      let states' := map inf_block sts in
      TopDecl.Parser pn cps eps ps start' states'
  | TopDecl.Funct f tparams params body =>
      let body' := inf_block body in
      TopDecl.Funct f tparams params body'
  end.
