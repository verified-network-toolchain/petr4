Require Import Poulet4.Utils.Envn Poulet4.P4cub.Syntax.AST.
(*Import String.*)

Definition find_default (σ : Env.t nat Expr.t) (X : nat) (default : Expr.t) :=
  match Env.find X σ with
  | Some t => t
  | None   => default
  end.

(*Definition remove_types (σ : Env.t nat Expr.t) (tparams : list nat) :=
  List.fold_right Env.remove σ tparams.*)

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
      let e' := map_sum (tsub_t σ) (tsub_e σ) e in
      Stmt.Var e'
  | Stmt.Assign lhs rhs =>
      let lhs' := tsub_e σ lhs in
      let rhs' := tsub_e σ rhs in
      Stmt.Assign lhs' rhs'
  | Stmt.Conditional g tru fls =>
      let g' := tsub_e σ g in
      let tru' := tsub_s σ tru in
      let fls' := tsub_s σ fls in
      Stmt.Conditional g' tru' fls'
  | Stmt.Seq s1 s2 =>
      let s1' := tsub_s σ s1 in
      let s2' := tsub_s σ s2 in
      Stmt.Seq s1' s2'
  | Stmt.Block b =>
      Stmt.Block (tsub_s σ b)
  | Stmt.ExternMethodCall extern_name method_name typ_args args =>
      (*TODO Is there something more complicated we need to do with typ_args? *)
      let typ_args' := List.map (tsub_t σ) typ_args in
      let args' := tsub_arrowE σ args in
      Stmt.ExternMethodCall extern_name method_name typ_args' args'
  | Stmt.FunCall f typ_args args =>
      (*TODO Is there something more complicated we need to do with typ_args? *)
      let typ_args' := List.map (tsub_t σ) typ_args in
      let args' := tsub_arrowE σ args in
      Stmt.FunCall f typ_args' args'
  | Stmt.ActCall a args =>
      let args' := map (tsub_arg σ) args in
      Stmt.ActCall a args'
  | Stmt.Return e =>
      let e' := option_map (tsub_e σ) e in
      Stmt.Return e' 
  | Stmt.Apply ci ext_args args =>
      let args' := map (tsub_arg σ) args in
      Stmt.Apply ci ext_args args
  end.

Definition tsub_carg (σ : Env.t nat Expr.t) (carg : Expr.constructor_arg) :=
  match carg with
  | Expr.CAName _ => carg
  | Expr.CAExpr e => Expr.CAExpr (tsub_e σ e)
  end.

Fixpoint tsub_cparam (σ : Env.t nat Expr.t) (ctor_type : Expr.ct) :=
  match ctor_type with
  | Expr.CTControl cparams extern_params params =>
      Expr.CTControl (map (tsub_cparam σ) cparams) extern_params
                     (map (tsub_param σ) params)
  | Expr.CTParser cparams extern_params params =>
      Expr.CTParser (map (tsub_cparam σ) cparams) extern_params
                    (map (tsub_param σ) params)
  | Expr.CTPackage cparams =>
      Expr.CTPackage (map (tsub_cparam σ) cparams)
  | Expr.CTExtern e => Expr.CTExtern e
  | Expr.CTType t =>
      let t' := tsub_t σ t in
      Expr.CTType t'
  end.

Definition tsub_arrowT (σ : Env.t nat Expr.t) (ar : Expr.arrowT) :=
  let params := paramargs ar in
  let ret := rtrns ar in
  let params' := map (tsub_param σ) params in
  let ret' := option_map (tsub_t σ) ret in
  {| paramargs := params'; rtrns := ret' |}.

(* TODO: rename types & extend type environments. *)

Definition tsub_method (σ : Env.t nat Expr.t) (method_types : (list nat * Expr.arrowT)) :=
  let '(type_params, arrow) := method_types in
  let σ' := remove_types σ type_params in
  (type_params, tsub_arrowT σ' arrow).

  (*Print Control.table.*)

  Definition tsub_table (σ : Env.t nat Expr.t) (tbl : Control.table) :=
    let tbl_keys := Control.table_key tbl in
    let tbl_acts := Control.table_actions tbl in
    let tbl_keys' := List.map (fun '(e,mk) => (tsub_e σ e, mk)) tbl_keys in
    {| Control.table_key := tbl_keys'; Control.table_actions := tbl_acts |}.

  Fixpoint tsub_Cd (σ : Env.t nat Expr.t) (d : Control.d) :=
    match d with
    | Control.CDAction a sig body i =>
      let sig' := map (tsub_param σ) sig in
      let body' := tsub_s σ body in
      Control.CDAction a sig' body' i
    | Control.CDTable t tbl i =>
      Control.CDTable t (tsub_table σ tbl) i
    | Control.CDSeq d1 d2 i =>
      Control.CDSeq (tsub_Cd σ d1) (tsub_Cd σ d2) i
    end.

  Fixpoint tsub_transition (σ : Env.t nat Expr.t) (transition : Parser.e) :=
    match transition with
    | Parser.PGoto s i =>
      Parser.PGoto s i
    | Parser.PSelect discriminee default cases i =>
      let discriminee' := tsub_e σ discriminee in
      let default' := tsub_transition σ default in
      let cases' := map (tsub_transition σ) cases in
      Parser.PSelect discriminee' default' cases' i
    end.

  Definition tsub_state (σ : Env.t nat Expr.t) (st : Parser.state_block) :=
    let s := Parser.stmt st in
    let e := Parser.trans st in
    let e' := tsub_transition σ e in
    {| Parser.stmt := s; Parser.trans := e' |}.

  Fixpoint tsub_d (σ : Env.t nat Expr.t) (d : TopDecl.d) : TopDecl.d :=
    match d with
    | TopDecl.Instantiate cname iname type_args cargs i =>
      (* TODO theres something broken here, need to get type params for cname *)
      let type_args' := List.map (tsub_t σ) type_args in
      let cargs' := map (tsub_carg σ) cargs in
      TopDecl.Instantiate cname iname type_args' cargs' i
    | TopDecl.Extern ename tparams cparams methods i =>
      let σ' := remove_types σ tparams in
      let cparams' := map (tsub_cparam σ') cparams in
      let methods' := map (tsub_method σ') methods in
      TopDecl.Extern ename tparams cparams' methods' i
    | TopDecl.Control cname cparams eparams params body apply_blk i =>
      let cparams' := map (tsub_cparam σ) cparams in
      let params' := map (tsub_param σ) params in
      let body' := tsub_Cd σ body in
      let apply_blk' := tsub_s σ apply_blk in
      TopDecl.Control cname cparams' eparams params' body' apply_blk' i
    | TopDecl.Parser pn cps eps ps strt sts i =>
      let cparams' := map (tsub_cparam σ) cps in
      let params' := map (tsub_param σ) ps in
      let start' := tsub_state σ strt in
      let states' := map (tsub_state σ) sts in
      TopDecl.Parser pn cparams' eps params' start' states' i
    | TopDecl.Function f tparams params body i =>
      let σ' := remove_types σ tparams in
      let cparams' := tsub_arrowT σ' params in
      let body' := tsub_s σ' body in
      TopDecl.Function f tparams cparams' body' i
    | TopDecl.Seq d1 d2 i =>
      TopDecl.Seq (tsub_d σ d1) (tsub_d σ d2) i
    end.

End TypeSubstitution.
