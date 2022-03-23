From Poulet4 Require Import Utils.Envn
     P4cub.Syntax.AST P4cub.Syntax.CubNotations.
Import AllCubNotations String.

Fixpoint tshift_t (n : nat) (τ : Expr.t) : Expr.t :=
  match τ with
  | Expr.TBool
  | Expr.TBit _
  | Expr.TInt _
  | Expr.TError       => τ
  | Expr.TVar X       => n + X
  | Expr.TStruct ts b => Expr.TStruct (map (tshift_t n) ts) b
  end.

Definition find_default (σ : Env.t nat Expr.t) (X : nat) (default : Expr.t) :=
  match Env.find X σ with
  | Some t => t
  | None   => default
  end.

Fixpoint tsub_t (σ : Env.t nat Expr.t) (t : Expr.t) : Expr.t :=
  match t with
  | Expr.TBool
  | Expr.TBit _
  | Expr.TInt _
  | Expr.TError       => t    
  | Expr.TStruct ts b => Expr.TStruct (List.map (tsub_t σ) ts) b
  | Expr.TVar X => find_default σ X t
  end.
(**[]*)

Fixpoint tsub_e (σ : Env.t nat Expr.t) (e : Expr.e) : Expr.e :=
  match e with
  | Expr.Bool _
  | Expr.Bit _ _
  | Expr.Int _ _
  | Expr.Error _ => e
  | Expr.Var t x       => Expr.Var (tsub_t σ t) x
  | Expr.Slice e hi lo => Expr.Slice (tsub_e σ e) hi lo
  | Expr.Cast t e      => Expr.Cast (tsub_t σ t) (tsub_e σ e)
  | Expr.Uop rt op e => Expr.Uop (tsub_t σ rt) op (tsub_e σ e)
  | Expr.Bop rt op e1 e2 =>
      Expr.Bop (tsub_t σ rt) op (tsub_e σ e1) (tsub_e σ e2)
  | Expr.Struct es e =>
      Expr.Struct (map (tsub_e σ) es) (option_map (tsub_e σ) e)
  | Expr.Member rt mem arg =>
      Expr.Member (tsub_t σ rt) mem (tsub_e σ arg)
  end.
(**[]*)

Definition tsub_param (σ : Env.t nat Expr.t) (pa : paramarg Expr.t Expr.t) :=
  match pa with
  | PAIn t => PAIn (tsub_t σ t)
  | PAOut t => PAOut (tsub_t σ t)
  | PAInOut t => PAInOut (tsub_t σ t)
  | PADirLess t => PAInOut (tsub_t σ t)
  end.

Definition tsub_arg (σ : Env.t nat Expr.t) (pa : paramarg Expr.e Expr.e) :=
  match pa with
  | PAIn e => PAIn (tsub_e σ e)
  | PAOut e => PAOut (tsub_e σ e)
  | PAInOut e => PAInOut (tsub_e σ e)
  | PADirLess e => PAInOut (tsub_e σ e)
  end.

Definition tsub_arrowE
           (σ : Env.t nat Expr.t)
           '({| paramargs:=args; rtrns:=ret |} : Expr.arrowE) :=
  {| paramargs:=map (tsub_arg σ) args; rtrns:=option_map (tsub_e σ) ret |}.

Fixpoint tsub_s (σ : Env.t nat Expr.t) (s : Stmt.s) : Stmt.s :=
  match s with
  | Stmt.Skip
  | Stmt.Exit
  | Stmt.Invoke _ => s
  | Stmt.Var e =>
      Stmt.Var $ map_sum (tsub_t σ) (tsub_e σ) e
  | Stmt.Assign lhs rhs =>
      Stmt.Assign (tsub_e σ lhs) $ tsub_e σ rhs
  | Stmt.Conditional g tru fls =>
      Stmt.Conditional (tsub_e σ g) (tsub_s σ tru) $ tsub_s σ fls
  | Stmt.Seq s1 s2 =>
      Stmt.Seq (tsub_s σ s1) $ tsub_s σ s2
  | Stmt.Block b =>
      Stmt.Block $ tsub_s σ b
  | Stmt.ExternMethodCall extern_name method_name typ_args args =>
      Stmt.ExternMethodCall
        extern_name method_name
        (map (tsub_t σ) typ_args) $
        tsub_arrowE σ args
  | Stmt.FunCall f typ_args args =>
      Stmt.FunCall f (map (tsub_t σ) typ_args) $ tsub_arrowE σ args
  | Stmt.ActCall a args =>
      Stmt.ActCall a $ map (tsub_arg σ) args
  | Stmt.Return e =>
      Stmt.Return $ option_map (tsub_e σ) e 
  | Stmt.Apply ci ext_args args =>
      Stmt.Apply ci ext_args $ map (tsub_arg σ) args
  end.

Definition tsub_carg
           (σ : Env.t nat Expr.t) (carg : TopDecl.constructor_arg)
  : TopDecl.constructor_arg :=
  match carg with
  | TopDecl.CAName _ => carg
  | TopDecl.CAExpr e => tsub_e σ e
  end.

Fixpoint tsub_cparam
         (σ : Env.t nat Expr.t) (ctor_type : TopDecl.it) : TopDecl.it :=
  match ctor_type with
  | TopDecl.ControlInstType extern_params params =>
      TopDecl.ControlInstType
        extern_params (map (tsub_param σ) params)
  | TopDecl.ParserInstType extern_params params =>
      TopDecl.ParserInstType
        extern_params (map (tsub_param σ) params)
  | TopDecl.PackageInstType => TopDecl.PackageInstType
  | TopDecl.ExternInstType e => TopDecl.ExternInstType e
  | TopDecl.EType t => tsub_t σ t
  end.

Definition tsub_arrowT
           (σ : Env.t nat Expr.t)
           '({| paramargs:=params; rtrns:=ret |} : Expr.arrowT) : Expr.arrowT :=
  {| paramargs := map (tsub_param σ) params
  ; rtrns := option_map (tsub_t σ) ret |}.

Definition tshift_env (n : nat) : Env.t nat Expr.t -> Env.t nat Expr.t :=
  map (fun '(X,τ) => (n + X, tshift_t n τ)).

Definition tsub_method
           (σ : Env.t nat Expr.t)
           '((Δ,xs,arr) : nat * list string * Expr.arrowT) :=
  (Δ,xs,tsub_arrowT (tshift_env Δ σ) arr).


Definition tsub_table
           (σ : Env.t nat Expr.t) (tbl : Control.table) :=
  let tbl_keys := Control.table_key tbl in
  let tbl_acts := Control.table_actions tbl in
  let tbl_keys' := List.map (fun '(e,mk) => (tsub_e σ e, mk)) tbl_keys in
  {| Control.table_key := tbl_keys'; Control.table_actions := tbl_acts |}.

Fixpoint tsub_Cd (σ : Env.t nat Expr.t) (d : Control.d) :=
  match d with
  | Control.Action a sig body =>
      let sig' := map (tsub_param σ) sig in
      let body' := tsub_s σ body in
      Control.Action a sig' body'
  | Control.Table t tbl =>
      Control.Table t (tsub_table σ tbl)
  | (d1 ;c; d2)%ctrl =>
      (tsub_Cd σ d1 ;c; tsub_Cd σ d2)%ctrl
  end.

Fixpoint tsub_transition (σ : Env.t nat Expr.t) (transition : Parser.e) :=
  match transition with
  | Parser.Goto s =>
      Parser.Goto s
  | Parser.Select discriminee default cases =>
      let discriminee' := tsub_e σ discriminee in
      let default' := tsub_transition σ default in
      let cases' := Field.map (tsub_transition σ) cases in
      Parser.Select discriminee' default' cases'
  end.

Definition tsub_state (σ : Env.t nat Expr.t) (st : Parser.state_block) :=
  let s := Parser.stmt st in
  let e := Parser.trans st in
  let s' := tsub_s σ s in
  let e' := tsub_transition σ e in
  {| Parser.stmt := s'; Parser.trans := e' |}.

Fixpoint tsub_d (σ : Env.t nat Expr.t) (d : TopDecl.d) : TopDecl.d :=
  match d with
  | TopDecl.Instantiate cname iname type_args cargs =>
      (* TODO theres something broken here, need to get type params for cname *)
      let type_args' := map (tsub_t σ) type_args in
      let cargs' := map (tsub_carg σ) cargs in
      TopDecl.Instantiate cname iname type_args' cargs'
  | TopDecl.Extern ename tparams cparams methods =>
      let σ' := tshift_env tparams σ in
      let cparams' := map (tsub_cparam σ') cparams in
      let methods' := Field.map (tsub_method σ') methods in
      TopDecl.Extern ename tparams cparams' methods'
  | TopDecl.Control cname cparams eparams params body apply_blk =>
      let cparams' := map (tsub_cparam σ) cparams in
      let params' := map (tsub_param σ) params in
      let body' := tsub_Cd σ body in
      let apply_blk' := tsub_s σ apply_blk in
      TopDecl.Control cname cparams' eparams params' body' apply_blk'
  | TopDecl.Parser pn cps eps ps strt sts =>
      let cparams' := map (tsub_cparam σ) cps in
      let params' := map (tsub_param σ) ps in
      let start' := tsub_state σ strt in
      let states' := map (tsub_state σ) sts in
      TopDecl.Parser pn cparams' eps params' start' states'
  | TopDecl.Funct f tparams params body =>
      let σ' := tshift_env tparams σ in
      let cparams' := tsub_arrowT σ' params in
      let body' := tsub_s σ' body in
      TopDecl.Funct f tparams cparams' body'
  | (d1 ;%; d2)%top =>
      (tsub_d σ d1 ;%; tsub_d σ d2)%top
  end.
