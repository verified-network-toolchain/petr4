From Poulet4 Require Import
     Utils.Util.FunUtil
     P4cub.Syntax.AST P4cub.Syntax.CubNotations.
Import AllCubNotations String.

(** * Philip Wadler style de Bruijn substitution of type variables. *)

Fixpoint tshift_t (n : nat) (τ : Expr.t) : Expr.t :=
  match τ with
  | Expr.TBool
  | Expr.TBit _
  | Expr.TInt _
  | Expr.TError       => τ
  | Expr.TVar X       => n + X
  | Expr.TStruct ts b => Expr.TStruct (map (tshift_t n) ts) b
  end.

Definition exts (σ : nat -> Expr.t) (X : nat) : Expr.t :=
  match X with
  | O => O
  | S n => tshift_t 1 $ σ n
  end.

Fixpoint tsub_t (σ : nat -> Expr.t) (t : Expr.t) : Expr.t :=
  match t with
  | Expr.TBool
  | Expr.TBit _
  | Expr.TInt _
  | Expr.TError       => t    
  | Expr.TStruct ts b => Expr.TStruct (List.map (tsub_t σ) ts) b
  | Expr.TVar X       => σ X
  end.

Fixpoint tsub_e (σ : nat -> Expr.t) (e : Expr.e) : Expr.e :=
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

Definition tsub_param (σ : nat -> Expr.t) (pa : paramarg Expr.t Expr.t) :=
  match pa with
  | PAIn t => PAIn (tsub_t σ t)
  | PAOut t => PAOut (tsub_t σ t)
  | PAInOut t => PAInOut (tsub_t σ t)
  end.

Definition tsub_arg (σ : nat -> Expr.t) (pa : paramarg Expr.e Expr.e) :=
  match pa with
  | PAIn e => PAIn (tsub_e σ e)
  | PAOut e => PAOut (tsub_e σ e)
  | PAInOut e => PAInOut (tsub_e σ e)
  end.

Definition tsub_arrowE
           (σ : nat -> Expr.t)
           '({| paramargs:=args; rtrns:=ret |} : Expr.arrowE) :=
  {| paramargs:=map (tsub_arg σ) args; rtrns:=option_map (tsub_e σ) ret |}.

Definition tsub_s (σ : nat -> Expr.t) (s : Stmt.s) : Stmt.s :=
  match s with  
  | Stmt.Invoke _ => s
  | Stmt.Assign lhs rhs =>
      Stmt.Assign (tsub_e σ lhs) $ tsub_e σ rhs
  | Stmt.MethodCall extern_name method_name typ_args args =>
      Stmt.MethodCall
        extern_name method_name
        (map (tsub_t σ) typ_args) $
        tsub_arrowE σ args
  | Stmt.FunCall f typ_args args =>
      Stmt.FunCall f (map (tsub_t σ) typ_args) $ tsub_arrowE σ args
  | Stmt.ActCall a cargs dargs =>
      Stmt.ActCall a (map (tsub_e σ) cargs) $ map (tsub_arg σ) dargs
  | Stmt.Apply ci ext_args args =>
      Stmt.Apply ci ext_args $ map (tsub_arg σ) args
  end.

Fixpoint tsub_block (σ : nat -> Expr.t) (b : Stmt.block) : Stmt.block :=
  match b with
  | Stmt.Skip
  | Stmt.Exit => b
  | Stmt.Var e b => Stmt.Var (map_sum (tsub_t σ) (tsub_e σ) e) b
  | Stmt.Return e =>
      Stmt.Return $ option_map (tsub_e σ) e 
  | Stmt.Seq s1 s2 =>
      Stmt.Seq (tsub_s σ s1) $ tsub_block σ s2
  | Stmt.Conditional g tru fls b =>
      Stmt.Conditional
        (tsub_e σ g) (tsub_block σ tru)
        (tsub_block σ fls) $ tsub_block σ b
  | Stmt.Block b1 b2 =>
      Stmt.Block (tsub_block σ b1) $ tsub_block σ b2
  end.

Definition tsub_carg
           (σ : nat -> Expr.t) (carg : TopDecl.constructor_arg)
  : TopDecl.constructor_arg :=
  match carg with
  | TopDecl.CAName _ => carg
  | TopDecl.CAExpr e => tsub_e σ e
  end.

Definition tsub_cparam
         (σ : nat -> Expr.t) (ctor_type : TopDecl.it) : TopDecl.it :=
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
           (σ : nat -> Expr.t)
           '({| paramargs:=params; rtrns:=ret |} : Expr.arrowT) : Expr.arrowT :=
  {| paramargs := map (tsub_param σ) params
  ; rtrns := option_map (tsub_t σ) ret |}.

Definition tsub_method
           (σ : nat -> Expr.t)
           '((Δ,xs,arr) : nat * list string * Expr.arrowT) :=
  (Δ,xs,tsub_arrowT (exts `^ Δ σ) arr).

Definition tsub_Cd (σ : nat -> Expr.t) (d : Control.d) :=
  match d with
  | Control.Action a cps dps body =>
      Control.Action
        a (map (tsub_t σ) cps)
        (map (tsub_param σ) dps) $ tsub_block σ body
  | Control.Table t key acts =>
      Control.Table
        t (List.map (fun '(e,mk) => (tsub_e σ e, mk)) key) acts
  end.

Definition tsub_transition (σ : nat -> Expr.t) (transition : Parser.e) :=
  match transition with
  | Parser.Goto s =>
      Parser.Goto s
  | Parser.Select discriminee default cases =>
      Parser.Select (tsub_e σ discriminee) default cases
  end.

Definition tsub_state (σ : nat -> Expr.t) (st : Parser.state_block) :=
  let s := Parser.state_blk st in
  let e := Parser.state_trans st in
  let s' := tsub_block σ s in
  let e' := tsub_transition σ e in
  {| Parser.state_blk := s'; Parser.state_trans := e' |}.

Definition tsub_d (σ : nat -> Expr.t) (d : TopDecl.d) : TopDecl.d :=
  match d with
  | TopDecl.Instantiate cname type_args cargs =>
      (* TODO theres something broken here, need to get type params for cname *)
      let type_args' := map (tsub_t σ) type_args in
      let cargs' := map (tsub_carg σ) cargs in
      TopDecl.Instantiate cname type_args' cargs'
  | TopDecl.Extern ename tparams cparams methods =>
      let σ' := exts `^ tparams σ in
      let cparams' := map (tsub_cparam σ') cparams in
      let methods' := Field.map (tsub_method σ') methods in
      TopDecl.Extern ename tparams cparams' methods'
  | TopDecl.Control cname cparams eparams params body apply_blk =>
      let cparams' := map (tsub_cparam σ) cparams in
      let params' := map (tsub_param σ) params in
      let body' := map (tsub_Cd σ) body in
      let apply_blk' := tsub_block σ apply_blk in
      TopDecl.Control cname cparams' eparams params' body' apply_blk'
  | TopDecl.Parser pn cps eps ps strt sts =>
      let cparams' := map (tsub_cparam σ) cps in
      let params' := map (tsub_param σ) ps in
      let start' := tsub_state σ strt in
      let states' := map (tsub_state σ) sts in
      TopDecl.Parser pn cparams' eps params' start' states'
  | TopDecl.Funct f tparams params body =>
      let σ' := exts `^ tparams σ in
      let cparams' := tsub_arrowT σ' params in
      let body' := tsub_block σ' body in
      TopDecl.Funct f tparams cparams' body'
  end.

(** Generate a substitution from type arguments. *)
Fixpoint gen_tsub (τs : list Expr.t) (X : nat) : Expr.t :=
  match τs, X with
  | τ :: _, O => τ
  | _ :: τs, S n => gen_tsub τs n
  | [], O => O
  | [], S n => n
  end.
