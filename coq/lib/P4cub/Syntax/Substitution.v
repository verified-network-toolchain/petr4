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
  | Expr.TVarBit _
  | Expr.TError       => τ
  | Expr.TVar X       => n + X
  | Expr.TArray s t   => Expr.TArray s (tshift_t n t)
  | Expr.TStruct b ts => Expr.TStruct b (map (tshift_t n) ts)
  end.

Section Sub.
  Variable σ : nat -> Expr.t.

  Definition exts (X : nat) : Expr.t :=
    match X with
    | O => O
    | S n => tshift_t 1 $ σ n
    end.

  Fixpoint tsub_t (t : Expr.t) : Expr.t :=
    match t with
    | Expr.TBool
    | Expr.TBit _
    | Expr.TInt _
    | Expr.TVarBit _
    | Expr.TError       => t
    | Expr.TArray n t   => Expr.TArray n $ tsub_t t
    | Expr.TStruct b ts => Expr.TStruct b $ List.map tsub_t ts
    | Expr.TVar X       => σ X
    end.

  Definition tsub_lists (l : Expr.lists) : Expr.lists :=
    match l with
    | Expr.lists_struct   => Expr.lists_struct
    | Expr.lists_array  t => Expr.lists_array $ tsub_t t
    | Expr.lists_header b => Expr.lists_header b
    end.

  Fixpoint tsub_e (e : Expr.e) : Expr.e :=
    match e with
    | Expr.Bool _
    | Expr.Bit _ _
    | Expr.Int _ _
    | Expr.VarBit _ _ _
    | Expr.Error _ => e
    | Expr.Var t og x       => Expr.Var (tsub_t t) og x
    | Expr.Slice hi lo e => Expr.Slice hi lo $ tsub_e e
    | Expr.Cast t e      => Expr.Cast (tsub_t t) $ tsub_e e
    | Expr.Uop rt op e   => Expr.Uop (tsub_t rt) op $ tsub_e e
    | Expr.Bop rt op e1 e2 =>
        Expr.Bop (tsub_t rt) op (tsub_e e1) $ tsub_e e2
    | Expr.Index t e1 e2 => Expr.Index (tsub_t t) (tsub_e e1) $ tsub_e e2
    | Expr.Member rt mem arg =>
        Expr.Member (tsub_t rt) mem (tsub_e arg)
    | Expr.Lists l es => Expr.Lists (tsub_lists l) $ map tsub_e es
    end.
  
  Definition tsub_param
    : paramarg Expr.t Expr.t -> paramarg Expr.t Expr.t :=
    paramarg_map_same $ tsub_t.

  Definition tsub_arg
    : paramarg Expr.e Expr.e -> paramarg Expr.e Expr.e :=
    paramarg_map_same $ tsub_e.

  Definition tsub_transition (transition : Parser.pt) :=
    match transition with
    | Parser.Direct s => Parser.Direct s
    | Parser.Select discriminee default cases =>
        Parser.Select (tsub_e discriminee) default cases
    end.

  Definition tsub_fun_kind (fk : Stmt.fun_kind) : Stmt.fun_kind :=
    match fk with
    | Stmt.Funct f τs oe
      => Stmt.Funct f (map tsub_t τs) $ option_map tsub_e oe
    | Stmt.Action a cargs
      => Stmt.Action a $ map tsub_e cargs
    | Stmt.Method e m τs oe
      => Stmt.Method e m (map tsub_t τs) $ option_map tsub_e oe
    end.

  Fixpoint tsub_s (s : Stmt.s) : Stmt.s :=
    match s with
    | Stmt.Skip
    | Stmt.Exit => s
    | Stmt.Return e => Stmt.Return $ option_map tsub_e e
    | Stmt.Transition e => Stmt.Transition $ tsub_transition e
    | (lhs `:= rhs)%stmt
      => (tsub_e lhs `:= tsub_e rhs)%stmt
    | Stmt.Invoke e t
      => Stmt.Invoke (option_map tsub_e e) t
    | Stmt.Call fk args
      => Stmt.Call (tsub_fun_kind fk) $ map tsub_arg args
    | Stmt.Apply ci ext_args args =>
        Stmt.Apply ci ext_args $ map tsub_arg args
    | Stmt.Var x e s
      => Stmt.Var
          x (map_sum tsub_t tsub_e e)
          $ tsub_s s
    | (s₁ `; s₂)%stmt => (tsub_s s₁ `; tsub_s s₂)%stmt
    | (If g Then tru Else fls)%stmt
      => (If tsub_e g Then tsub_s tru Else tsub_s fls)%stmt
    end.
  
  Definition tsub_cparam
             (ctor_type : TopDecl.it) : TopDecl.it :=
    match ctor_type with
    | TopDecl.ControlInstType extern_params params =>
        TopDecl.ControlInstType
          extern_params (map_snd tsub_param params)
    | TopDecl.ParserInstType extern_params params =>
        TopDecl.ParserInstType
          extern_params (map_snd tsub_param params)
    | TopDecl.PackageInstType => TopDecl.PackageInstType
    | TopDecl.ExternInstType e => TopDecl.ExternInstType e
    end.

  Definition tsub_arrowT
             '({| paramargs:=params; rtrns:=ret |} : Expr.arrowT) : Expr.arrowT :=
    {| paramargs := map_snd tsub_param params
    ; rtrns := option_map tsub_t ret |}.
End Sub.

Definition tsub_method
           (σ : nat -> Expr.t)
           '((Δ,xs,arr) : nat * list string * Expr.arrowT) :=
  (Δ,xs,tsub_arrowT (exts `^ Δ σ) arr).

Definition tsub_Cd (σ : nat -> Expr.t) (d : Control.d) :=
  match d with
  | Control.Var og te =>
      Control.Var og $ map_sum (tsub_t σ) (tsub_e σ) te
  | Control.Action a cps dps body =>
      Control.Action
        a (map_snd (tsub_t σ) cps)
        (map_snd (tsub_param σ) dps) $ tsub_s σ body
  | Control.Table t key acts def =>
      Control.Table
        t (List.map (fun '(e,mk) => (tsub_e σ e, mk)) key)
        (List.map (fun '(a,args) => (a, map (tsub_arg σ) args)) acts)
        $ option_map (fun '(a,es) => (a, map (tsub_e σ) es)) def
  end.

Definition tsub_d (σ : nat -> Expr.t) (d : TopDecl.d) : TopDecl.d :=
  match d with
  | TopDecl.Instantiate cname iname type_args cargs expr_cargs =>
      (* TODO theres something broken here, need to get type params for cname *)
      let type_args' := map (tsub_t σ) type_args in
      let expr_cargs' := map (tsub_e σ) expr_cargs in
      TopDecl.Instantiate cname iname type_args' cargs expr_cargs'
  | TopDecl.Extern ename tparams cparams expr_cparams methods =>
      let σ' := exts `^ tparams σ in
      let cparams' :=
        List.map (FunUtil.map_snd $ tsub_cparam σ') cparams in
      let expr_cparams' :=
        map (tsub_t σ') expr_cparams in
      let methods' := Field.map (tsub_method σ') methods in
      TopDecl.Extern ename tparams cparams' expr_cparams' methods'
  | TopDecl.Control cname cparams expr_cparams eparams params body apply_blk =>
      let cparams' := map (FunUtil.map_snd $ tsub_cparam σ) cparams in
      let expr_cparams' :=
        map (tsub_t σ) expr_cparams in
      let params' := map_snd (tsub_param σ) params in
      let body' := map (tsub_Cd σ) body in
      let apply_blk' := tsub_s σ apply_blk in
      TopDecl.Control cname cparams' expr_cparams' eparams params' body' apply_blk'
  | TopDecl.Parser pn cps expr_cparams eps ps strt sts =>
      let cps' := map (FunUtil.map_snd $ tsub_cparam σ) cps in
      let expr_cparams' :=
        map (tsub_t σ) expr_cparams in
      let ps' := map_snd (tsub_param σ) ps in
      let start' := tsub_s σ strt in
      let states' := map (tsub_s σ) sts in
      TopDecl.Parser pn cps' expr_cparams' eps ps' start' states'
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
