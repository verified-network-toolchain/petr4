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
  | Expr.Struct es ob =>
      Expr.Struct (map (tsub_e σ) es) ob
  | Expr.Member rt mem arg =>
      Expr.Member (tsub_t σ rt) mem (tsub_e σ arg)
  end.

Definition tsub_param (σ : nat -> Expr.t) (pa : paramarg Expr.t Expr.t) :=
  match pa with
  | PAIn t => PAIn (tsub_t σ t)
  | PAOut t => PAOut (tsub_t σ t)
  | PAInOut t => PAInOut (tsub_t σ t)
  end.

Definition tsub_arg (σ : nat -> Expr.t)
  : paramarg Expr.e Expr.e -> paramarg Expr.e Expr.e :=
  paramarg_map_same $ tsub_e σ.

Definition tsub_transition (σ : nat -> Expr.t) (transition : Parser.e) :=
  match transition with
  | Parser.Goto s =>
      Parser.Goto s
  | Parser.Select discriminee default cases =>
      Parser.Select (tsub_e σ discriminee) default cases
  end.

Definition tsub_fun_kind (σ : nat -> Expr.t) (fk : Stmt.fun_kind) : Stmt.fun_kind :=
  match fk with
  | Stmt.Funct f τs oe
    => Stmt.Funct f (map (tsub_t σ) τs) $ option_map (tsub_e σ) oe
  | Stmt.Action a cargs
    => Stmt.Action a $ map (tsub_e σ) cargs
  | Stmt.Method e m τs oe
    => Stmt.Method e m (map (tsub_t σ) τs) $ option_map (tsub_e σ) oe
  end.

Fixpoint tsub_s (σ : nat -> Expr.t) (s : Stmt.s) : Stmt.s :=
  match s with
  | Stmt.Skip
  | Stmt.Exit
  | Stmt.Invoke _ => s
  | Stmt.Return e => Stmt.Return $ option_map (tsub_e σ) e
  | Stmt.Transition e => Stmt.Transition $ tsub_transition σ e
  | (lhs `:= rhs)%stmt
    => (tsub_e σ lhs `:= tsub_e σ rhs)%stmt
  | Stmt.Call fk args
    => Stmt.Call (tsub_fun_kind σ fk) $ map (tsub_arg σ) args
  | Stmt.Apply ci ext_args args =>
      Stmt.Apply ci ext_args $ map (tsub_arg σ) args
  | Stmt.Var e s
    => Stmt.Var
        (map_sum (tsub_t σ) (tsub_e σ) e)
        $ tsub_s σ s
  | (s₁ `; s₂)%stmt => (tsub_s σ s₁ `; tsub_s σ s₂)%stmt
  | (If g Then tru Else fls)%stmt
    => (If tsub_e σ g Then tsub_s σ tru Else tsub_s σ fls)%stmt
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
        (map (tsub_param σ) dps) $ tsub_s σ body
  | Control.Table t key acts =>
      Control.Table
        t (List.map (fun '(e,mk) => (tsub_e σ e, mk)) key) acts
  end.

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
      let apply_blk' := tsub_s σ apply_blk in
      TopDecl.Control cname cparams' eparams params' body' apply_blk'
  | TopDecl.Parser pn cps eps ps strt sts =>
      let cparams' := map (tsub_cparam σ) cps in
      let params' := map (tsub_param σ) ps in
      let start' := tsub_s σ strt in
      let states' := map (tsub_s σ) sts in
      TopDecl.Parser pn cparams' eps params' start' states'
  | TopDecl.Funct f tparams params body =>
      let σ' := exts `^ tparams σ in
      let cparams' := tsub_arrowT σ' params in
      let body' := tsub_s σ' body in
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
