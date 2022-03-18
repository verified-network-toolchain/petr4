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
(**[]*)

Definition inf_arg (pa : paramarg Expr.e Expr.e) :=
  match pa with
  | PAIn e => PAIn (inf_e e)
  | PAOut e => PAOut (inf_e e)
    | PAInOut e => PAInOut (inf_e e)
  | PADirLess e => PAInOut (inf_e e)
  end.

Definition inf_arrowE  (ar : Expr.arrowE) :=
  let args := paramargs ar in
  let ret := rtrns ar in
  let args' := map inf_arg args in
  let ret' := option_map inf_e ret in
  {| paramargs := args'; rtrns := ret' |}.

Fixpoint inf_s  (s : Stmt.s) : Stmt.s :=
  match s with
  | Stmt.Skip
  | Stmt.Exit
  | Stmt.Invoke _ => s
  | Stmt.Var e =>
      Stmt.Var $ map_sum id inf_e e
  | (lhs `:= rhs)%stmt =>
      (inf_e lhs `:= inf_e rhs)%stmt
  | (If g Then tru Else fls)%stmt =>
      (If inf_e g Then inf_s tru Else inf_s fls)%stmt
  | (s1 `; s2)%stmt => (inf_s s1 `; inf_s s2)%stmt
  | Stmt.Block b =>
      Stmt.Block $ inf_s b
  | Stmt.ExternMethodCall extern_name method_name typ_args args =>
      let args' := inf_arrowE args in
      Stmt.ExternMethodCall extern_name method_name typ_args args'
  | Stmt.FunCall f typ_args args =>
      let args' := inf_arrowE args in
      Stmt.FunCall f typ_args args'
  | Stmt.ActCall a args =>
      let args' := map inf_arg args in
      Stmt.ActCall a args'
  | Stmt.Return e => Stmt.Return $ option_map inf_e e
  | Stmt.Apply ci ext_args args =>
      let args' := map inf_arg args in
      Stmt.Apply ci ext_args args
  end.

Definition inf_carg  (carg : Expr.constructor_arg) :=
  match carg with
  | Expr.CAName _ => carg
  | Expr.CAExpr e => Expr.CAExpr (inf_e e)
  end.

Definition inf_table  (tbl : Control.table) :=
  let tbl_keys := Control.table_key tbl in
  let tbl_acts := Control.table_actions tbl in
  let tbl_keys' := List.map (fun '(e,mk) => (inf_e e, mk)) tbl_keys in
  {| Control.table_key := tbl_keys'; Control.table_actions := tbl_acts |}.

Fixpoint inf_Cd  (d : Control.d) :=
  match d with
  | Control.Action a sig body =>
      Control.Action a sig $ inf_s body
  | Control.Table t tbl =>
      Control.Table t (inf_table tbl)
  | (d1 ;c; d2)%ctrl => (inf_Cd d1 ;c; inf_Cd d2)%ctrl
  end.

Fixpoint inf_transition  (transition : Parser.e) :=
  match transition with
  | Parser.Goto s =>
      Parser.Goto s
  | Parser.Select discriminee default cases =>
      let discriminee' := inf_e discriminee in
      let default' := inf_transition default in
      let cases' := Field.map inf_transition cases in
      Parser.Select discriminee' default' cases'
  end.

Definition inf_state  (st : Parser.state_block) :=
  let s := Parser.stmt st in
  let e := Parser.trans st in
  let s' := inf_s s in
  let e' := inf_transition e in
  {| Parser.stmt := s'; Parser.trans := e' |}.

Fixpoint inf_d  (d : TopDecl.d) : TopDecl.d :=
  match d with
    | TopDecl.Extern _ _ _ _ => d
  | TopDecl.Instantiate cname iname type_args cargs =>
      let cargs' := map inf_carg cargs in
      TopDecl.Instantiate cname iname type_args cargs'
  | TopDecl.Control cname cparams eparams params body apply_blk =>
      let body' := inf_Cd body in
      let apply_blk' := inf_s apply_blk in
      TopDecl.Control cname cparams eparams params body' apply_blk'
  | TopDecl.Parser pn cps eps ps strt sts =>
      let start' := inf_state strt in
      let states' := map inf_state sts in
      TopDecl.Parser pn cps eps ps start' states'
  | TopDecl.Funct f tparams params body =>
      let body' := inf_s body in
      TopDecl.Funct f tparams params body'
  | (d1 ;%; d2)%top => (inf_d d1 ;%; inf_d d2)%top
  end.
