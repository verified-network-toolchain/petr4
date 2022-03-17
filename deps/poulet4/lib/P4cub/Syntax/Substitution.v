Require Import Poulet4.Utils.Envn Poulet4.P4cub.Syntax.AST.
Import String.

Section TypeSubstitution.

  Definition find_default (σ : Env.t nat Expr.t) (X : nat) (default : Expr.t) :=
    match Env.find X σ with
    | Some t => t
    | None   => default
    end.

  Definition remove_types (σ : Env.t nat Expr.t) (tparams : list nat) :=
    List.fold_right Env.remove σ tparams.

  Fixpoint tsub_t (σ : Env.t string Expr.t) (t : Expr.t) : Expr.t :=
    match t with
    | Expr.TBool
    | Expr.TBit _
    | Expr.TInt _
    | Expr.TError       => t    
    | Expr.TStruct ts b => Expr.TStruct (List.map (tsub_t σ) ts) b
    | Expr.TVar X => find_default σ X t
    end.
  (**[]*)

  Context {tags_t : Type}.

  Fixpoint tsub_e (σ : Env.t string Expr.t) (e : Expr.e tags_t) : Expr.e tags_t :=
    match e with
    | Expr.Bool _ _
    | Expr.Bit _ _ _
    | Expr.Int _ _ _
    | Expr.Error _ _ => e
    | Expr.Var t x i =>
      Expr.Var (tsub_t σ t) x i
    | Expr.Slice e hi lo i =>
      Expr.Slice (tsub_e σ e) hi lo i
    | Expr.Cast t e i =>
      Expr.Cast (tsub_t σ t) (tsub_e σ e) i
    | Expr.Uop rt op e i =>
      Expr.Uop (tsub_t σ rt) op (tsub_e σ e) i
    | Expr.Bop rt op e1 e2 i =>
      Expr.Bop (tsub_t σ rt) op (tsub_e σ e1) (tsub_e σ e2) i
    | Expr.Tuple es i =>
      Expr.Tuple (List.map (tsub_e σ) es) i
    | Expr.Struct es i =>
      Expr.Struct (F.map (tsub_e σ) es) i
    | Expr.Header es e i =>
      Expr.Header (F.map (tsub_e σ) es) (tsub_e σ e) i
    | Expr.ExprMember rt mem arg i =>
      Expr.ExprMember (tsub_t σ rt) mem (tsub_e σ arg) i
    | Expr.HeaderStack fs hs ni i =>
      Expr.HeaderStack (F.map (tsub_t σ) fs) (List.map (tsub_e σ) hs) ni i
    | Expr.HeaderStackAccess result_hdr_type stk index i =>
      Expr.HeaderStackAccess (F.map (tsub_t σ) result_hdr_type) (tsub_e σ stk) index i
    end.
  (**[]*)


 Definition tsub_param (σ : Env.t string Expr.t) (pa : paramarg Expr.t Expr.t) :=
    match pa with
    | PAIn t => PAIn (tsub_t σ t)
    | PAOut t => PAOut (tsub_t σ t)
    | PAInOut t => PAInOut (tsub_t σ t)
    | PADirLess t => PAInOut (tsub_t σ t)
    end.

 Definition tsub_arg (σ : Env.t string Expr.t) (pa : paramarg (Expr.e tags_t) (Expr.e tags_t)) :=
    match pa with
    | PAIn e => PAIn (tsub_e σ e)
    | PAOut e => PAOut (tsub_e σ e)
    | PAInOut e => PAInOut (tsub_e σ e)
    | PADirLess e => PAInOut (tsub_e σ e)
    end.

  Definition tsub_retE (σ : Env.t string Expr.t) (ret : option (Expr.e tags_t)) :=
    let* e := ret in
    Some (tsub_e σ e).

  (*Print arrow.*)

  Definition tsub_arrowE (σ : Env.t string Expr.t) (ar : Expr.arrowE tags_t) :=
    let args := paramargs ar in
    let ret := rtrns ar in
    let args' := F.map (tsub_arg σ) args in
    let ret' := tsub_retE σ ret in
    {| paramargs := args'; rtrns := ret' |}.

  Fixpoint tsub_s (σ : Env.t string Expr.t) (s : Stmt.s tags_t) : Stmt.s tags_t :=
    match s with
    | Stmt.Skip _ => s
    | Stmt.Vardecl x e i =>
      let e' := map_sum (tsub_t σ) (tsub_e σ) e in
      Stmt.Vardecl x e' i
    | Stmt.Assign lhs rhs i =>
      let lhs' := tsub_e σ lhs in
      let rhs' := tsub_e σ rhs in
      Stmt.Assign lhs' rhs' i
    | Stmt.Conditional g tru fls i =>
      let g' := tsub_e σ g in
      let tru' := tsub_s σ tru in
      let fls' := tsub_s σ fls in
      Stmt.Conditional g' tru' fls' i
    | Stmt.Seq s1 s2 i =>
      let s1' := tsub_s σ s1 in
      let s2' := tsub_s σ s2 in
      Stmt.Seq s1' s2' i
    | Stmt.Block b =>
      Stmt.Block (tsub_s σ b)
    | Stmt.ExternMethodCall extern_name method_name typ_args args i =>
      (*TODO Is there something more complicated we need to do with typ_args? *)
      let typ_args' := List.map (tsub_t σ) typ_args in
      let args' := tsub_arrowE σ args in
      Stmt.ExternMethodCall extern_name method_name typ_args' args' i
    | Stmt.FunCall f typ_args args i =>
      (*TODO Is there something more complicated we need to do with typ_args? *)
      let typ_args' := List.map (tsub_t σ) typ_args in
      let args' := tsub_arrowE σ args in
      Stmt.FunCall f typ_args' args' i
    | Stmt.ActCall a args i =>
      let args' := F.map (tsub_arg σ) args in
      Stmt.ActCall a args' i
    | Stmt.Return e i =>
      let e' := tsub_retE σ e in
      Stmt.Return e' i
    | Stmt.Exit _ => s
    | Stmt.Invoke _ _ => s
    | Stmt.Apply ci ext_args args i =>
      let args' := F.map (tsub_arg σ) args in
      Stmt.Apply ci ext_args args i
    (* | Stmt.PApply _ pi ext_args args i => *)
    (*   let args' := F.map (tsub_arg σ) args in *)
    (*   Stmt.PApply _ pi ext_args args' i *)
    | Stmt.HeaderStackOp _ _ _ _ => s
    | Stmt.SetValidity _ _ _ => s
    end.

  Definition tsub_carg (σ : Env.t string Expr.t) (carg : Expr.constructor_arg tags_t) :=
    match carg with
    | Expr.CAName _ => carg
    | Expr.CAExpr e => Expr.CAExpr (tsub_e σ e)
    end.

  Definition tsub_retT (σ : Env.t string Expr.t) (ret : option Expr.t) :=
    let* t := ret in
    Some (tsub_t σ t).


  Fixpoint tsub_cparam (σ : Env.t string Expr.t) (ctor_type : Expr.ct) :=
    match ctor_type with
    | Expr.CTControl cparams extern_params params =>
      Expr.CTControl (F.map (tsub_cparam σ) cparams) extern_params
                  (F.map (tsub_param σ) params)
    | Expr.CTParser cparams extern_params params =>
      Expr.CTParser (F.map (tsub_cparam σ) cparams) extern_params
                 (F.map (tsub_param σ) params)
    | Expr.CTPackage cparams =>
      Expr.CTPackage (F.map (tsub_cparam σ) cparams)
    | Expr.CTExtern e => Expr.CTExtern e
    | Expr.CTType t =>
      let t' := tsub_t σ t in
      Expr.CTType t'
    end.

  Definition tsub_arrowT (σ : Env.t string Expr.t) (ar : Expr.arrowT) :=
    let params := paramargs ar in
    let ret := rtrns ar in
    let params' := F.map (tsub_param σ) params in
    let ret' := tsub_retT σ ret in
    {| paramargs := params'; rtrns := ret' |}.

  Definition tsub_method (σ : Env.t string Expr.t) (method_types : (list string * Expr.arrowT)) :=
    let '(type_params, arrow) := method_types in
    let σ' := remove_types σ type_params in
    (type_params, tsub_arrowT σ' arrow).

  (*Print Control.table.*)

  Definition tsub_table (σ : Env.t string Expr.t) (tbl : Control.table tags_t) :=
    let tbl_keys := Control.table_key tbl in
    let tbl_acts := Control.table_actions tbl in
    let tbl_keys' := List.map (fun '(e,mk) => (tsub_e σ e, mk)) tbl_keys in
    {| Control.table_key := tbl_keys'; Control.table_actions := tbl_acts |}.

  Fixpoint tsub_Cd (σ : Env.t string Expr.t) (d : Control.d tags_t) :=
    match d with
    | Control.CDAction a sig body i =>
      let sig' := F.map (tsub_param σ) sig in
      let body' := tsub_s σ body in
      Control.CDAction a sig' body' i
    | Control.CDTable t tbl i =>
      Control.CDTable t (tsub_table σ tbl) i
    | Control.CDSeq d1 d2 i =>
      Control.CDSeq (tsub_Cd σ d1) (tsub_Cd σ d2) i
    end.

  Fixpoint tsub_transition (σ : Env.t string Expr.t) (transition : Parser.e tags_t) :=
    match transition with
    | Parser.PGoto s i =>
      Parser.PGoto s i
    | Parser.PSelect discriminee default cases i =>
      let discriminee' := tsub_e σ discriminee in
      let default' := tsub_transition σ default in
      let cases' := F.map (tsub_transition σ) cases in
      Parser.PSelect discriminee' default' cases' i
    end.

  Definition tsub_state (σ : Env.t string Expr.t) (st : Parser.state_block tags_t) :=
    let s := Parser.stmt st in
    let e := Parser.trans st in
    let e' := tsub_transition σ e in
    {| Parser.stmt := s; Parser.trans := e' |}.

  Fixpoint tsub_d (σ : Env.t string Expr.t) (d : TopDecl.d tags_t) : TopDecl.d tags_t :=
    match d with
    | TopDecl.Instantiate cname iname type_args cargs i =>
      (* TODO theres something broken here, need to get type params for cname *)
      let type_args' := List.map (tsub_t σ) type_args in
      let cargs' := F.map (tsub_carg σ) cargs in
      TopDecl.Instantiate cname iname type_args' cargs' i
    | TopDecl.Extern ename tparams cparams methods i =>
      let σ' := remove_types σ tparams in
      let cparams' := F.map (tsub_cparam σ') cparams in
      let methods' := F.map (tsub_method σ') methods in
      TopDecl.Extern ename tparams cparams' methods' i
    | TopDecl.Control cname cparams eparams params body apply_blk i =>
      let cparams' := F.map (tsub_cparam σ) cparams in
      let params' := F.map (tsub_param σ) params in
      let body' := tsub_Cd σ body in
      let apply_blk' := tsub_s σ apply_blk in
      TopDecl.Control cname cparams' eparams params' body' apply_blk' i
    | TopDecl.Parser pn cps eps ps strt sts i =>
      let cparams' := F.map (tsub_cparam σ) cps in
      let params' := F.map (tsub_param σ) ps in
      let start' := tsub_state σ strt in
      let states' := F.map (tsub_state σ) sts in
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
