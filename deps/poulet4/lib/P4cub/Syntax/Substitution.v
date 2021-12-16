Require Import Poulet4.Utils.Util.Envn Poulet4.P4cub.Syntax.AST.
Import String.

(* Module P := P4cub. *)
Module E := Expr.
Module TD := TopDecl.
Module ST := Stmt.

Section TypeSubstitution.

  Definition find_default (σ : Env.t string E.t) (X : string) (default : E.t) :=
    match Env.find X σ with
    | Some t => t
    | None   => default
    end.

  Definition remove_types (σ : Env.t string E.t) (tparams : list string) :=
    List.fold_right Env.remove σ tparams.

  Fixpoint tsub_t (σ : Env.t string E.t) (t : E.t) : E.t :=
    match t with
    | E.TBool
    | E.TBit _
    | E.TInt _
    | E.TError
    | E.TMatchKind     => t
    | E.TTuple ts      => E.TTuple $ List.map (tsub_t σ) ts
    | E.TStruct ts => E.TStruct $ F.map (tsub_t σ) ts
    | E.THeader ts    => E.THeader $ F.map (tsub_t σ) ts
    | E.THeaderStack ts n   => E.THeaderStack (F.map (tsub_t σ) ts) n
    | E.TVar X => find_default σ X t
    end.
  (**[]*)

  Context {tags_t : Type}.

  Fixpoint tsub_e (σ : Env.t string E.t) (e : E.e tags_t) : E.e tags_t :=
    match e with
    | E.EBool _ _
    | E.EBit _ _ _
    | E.EInt _ _ _
    | E.EError _ _
    | E.EMatchKind _ _ => e
    | E.EVar t x i =>
      E.EVar (tsub_t σ t) x i
    | E.ESlice e hi lo i =>
      Expr.ESlice (tsub_e σ e) hi lo i
    | E.ECast t e i =>
      Expr.ECast (tsub_t σ t) (tsub_e σ e) i
    | E.EUop rt op e i =>
      Expr.EUop (tsub_t σ rt) op (tsub_e σ e) i
    | E.EBop rt op e1 e2 i =>
      Expr.EBop (tsub_t σ rt) op (tsub_e σ e1) (tsub_e σ e2) i
    | E.ETuple es i =>
      E.ETuple (List.map (tsub_e σ) es) i
    | E.EStruct es i =>
      E.EStruct (F.map (tsub_e σ) es) i
    | E.EHeader es e i =>
      Expr.EHeader (F.map (tsub_e σ) es) (tsub_e σ e) i
    | E.EExprMember rt mem arg i =>
      E.EExprMember (tsub_t σ rt) mem (tsub_e σ arg) i
    | E.EHeaderStack fs hs ni i =>
      E.EHeaderStack (F.map (tsub_t σ) fs) (List.map (tsub_e σ) hs) ni i
    | E.EHeaderStackAccess result_hdr_type stk index i =>
      E.EHeaderStackAccess (F.map (tsub_t σ) result_hdr_type) (tsub_e σ stk) index i
    end.
  (**[]*)


 Definition tsub_param (σ : Env.t string E.t) (pa : paramarg E.t E.t) :=
    match pa with
    | PAIn t => PAIn (tsub_t σ t)
    | PAOut t => PAOut (tsub_t σ t)
    | PAInOut t => PAInOut (tsub_t σ t)
    | PADirLess t => PAInOut (tsub_t σ t)
    end.

 Definition tsub_arg (σ : Env.t string E.t) (pa : paramarg (E.e tags_t) (E.e tags_t)) :=
    match pa with
    | PAIn e => PAIn (tsub_e σ e)
    | PAOut e => PAOut (tsub_e σ e)
    | PAInOut e => PAInOut (tsub_e σ e)
    | PADirLess e => PAInOut (tsub_e σ e)
    end.

  Definition tsub_retE (σ : Env.t string E.t) (ret : option (E.e tags_t)) :=
    let* e := ret in
    Some (tsub_e σ e).

  (*Print arrow.*)

  Definition tsub_arrowE (σ : Env.t string E.t) (ar : E.arrowE tags_t) :=
    let args := paramargs ar in
    let ret := rtrns ar in
    let args' := F.map (tsub_arg σ) args in
    let ret' := tsub_retE σ ret in
    {| paramargs := args'; rtrns := ret' |}.

  Fixpoint tsub_s (σ : Env.t string E.t) (s : ST.s tags_t) : ST.s tags_t :=
    match s with
    | ST.SSkip _ => s
    | ST.SVardecl x e i =>
      let e' := map_sum (tsub_t σ) (tsub_e σ) e in
      ST.SVardecl x e' i
    | ST.SAssign lhs rhs i =>
      let lhs' := tsub_e σ lhs in
      let rhs' := tsub_e σ rhs in
      ST.SAssign lhs' rhs' i
    | ST.SConditional g tru fls i =>
      let g' := tsub_e σ g in
      let tru' := tsub_s σ tru in
      let fls' := tsub_s σ fls in
      ST.SConditional g' tru' fls' i
    | ST.SSeq s1 s2 i =>
      let s1' := tsub_s σ s1 in
      let s2' := tsub_s σ s2 in
      ST.SSeq s1' s2' i
    | ST.SBlock b =>
      ST.SBlock (tsub_s σ b)
    | ST.SExternMethodCall extern_name method_name typ_args args i =>
      (*TODO Is there something more complicated we need to do with typ_args? *)
      let typ_args' := List.map (tsub_t σ) typ_args in
      let args' := tsub_arrowE σ args in
      ST.SExternMethodCall extern_name method_name typ_args' args' i
    | ST.SFunCall f typ_args args i =>
      (*TODO Is there something more complicated we need to do with typ_args? *)
      let typ_args' := List.map (tsub_t σ) typ_args in
      let args' := tsub_arrowE σ args in
      ST.SFunCall f typ_args' args' i
    | ST.SActCall a args i =>
      let args' := F.map (tsub_arg σ) args in
      ST.SActCall a args' i
    | ST.SReturn e i =>
      let e' := tsub_retE σ e in
      ST.SReturn e' i
    | ST.SExit _ => s
    | ST.SInvoke _ _ => s
    | ST.SApply ci ext_args args i =>
      let args' := F.map (tsub_arg σ) args in
      ST.SApply ci ext_args args i
    (* | ST.PApply _ pi ext_args args i => *)
    (*   let args' := F.map (tsub_arg σ) args in *)
    (*   ST.PApply _ pi ext_args args' i *)
    | ST.SHeaderStackOp _ _ _ _ => s
    | ST.SSetValidity _ _ _ => s
    end.


  Definition tsub_carg (σ : Env.t string E.t) (carg : E.constructor_arg tags_t) :=
    match carg with
    | E.CAName _ => carg
    | E.CAExpr e => E.CAExpr (tsub_e σ e)
    end.

  Definition tsub_retT (σ : Env.t string E.t) (ret : option E.t) :=
    let* t := ret in
    Some (tsub_t σ t).


  Fixpoint tsub_cparam (σ : Env.t string E.t) (ctor_type : E.ct) :=
    match ctor_type with
    | E.CTControl cparams extern_params params =>
      E.CTControl (F.map (tsub_cparam σ) cparams) extern_params
                  (F.map (tsub_param σ) params)
    | E.CTParser cparams extern_params params =>
      E.CTParser (F.map (tsub_cparam σ) cparams) extern_params
                 (F.map (tsub_param σ) params)
    | E.CTPackage cparams =>
      E.CTPackage (F.map (tsub_cparam σ) cparams)
    | E.CTExtern e => E.CTExtern e
    | E.CTType t =>
      let t' := tsub_t σ t in
      E.CTType t'
    end.

  Definition tsub_arrowT (σ : Env.t string E.t) (ar : E.arrowT) :=
    let params := paramargs ar in
    let ret := rtrns ar in
    let params' := F.map (tsub_param σ) params in
    let ret' := tsub_retT σ ret in
    {| paramargs := params'; rtrns := ret' |}.

  Definition tsub_method (σ : Env.t string E.t) (method_types : (list string * E.arrowT)) :=
    let '(type_params, arrow) := method_types in
    let σ' := remove_types σ type_params in
    (type_params, tsub_arrowT σ' arrow).

  (*Print Control.table.*)

  Definition tsub_table (σ : Env.t string E.t) (tbl : Control.table tags_t) :=
    let tbl_keys := Control.table_key tbl in
    let tbl_acts := Control.table_actions tbl in
    let tbl_keys' := List.map (fun '(e,mk) => (tsub_e σ e, mk)) tbl_keys in
    {| Control.table_key := tbl_keys'; Control.table_actions := tbl_acts |}.

  Fixpoint tsub_Cd (σ : Env.t string E.t) (d : Control.d tags_t) :=
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

  Fixpoint tsub_transition (σ : Env.t string E.t) (transition : Parser.e tags_t) :=
    match transition with
    | Parser.PGoto s i =>
      Parser.PGoto s i
    | Parser.PSelect discriminee default cases i =>
      let discriminee' := tsub_e σ discriminee in
      let default' := tsub_transition σ default in
      let cases' := F.map (tsub_transition σ) cases in
      Parser.PSelect discriminee' default' cases' i
    end.

  Definition tsub_state (σ : Env.t string E.t) (st : Parser.state_block tags_t) :=
    let s := Parser.stmt st in
    let e := Parser.trans st in
    let e' := tsub_transition σ e in
    {| Parser.stmt := s; Parser.trans := e' |}.

  Fixpoint tsub_d (σ : Env.t string E.t) (d : TD.d tags_t) : TD.d tags_t :=
    match d with
    | TD.TPInstantiate cname iname type_args cargs i =>
      (* TODO theres something broken here, need to get type params for cname *)
      let type_args' := List.map (tsub_t σ) type_args in
      let cargs' := F.map (tsub_carg σ) cargs in
      TD.TPInstantiate cname iname type_args' cargs' i
    | TD.TPExtern ename tparams cparams methods i =>
      let σ' := remove_types σ tparams in
      let cparams' := F.map (tsub_cparam σ') cparams in
      let methods' := F.map (tsub_method σ') methods in
      TD.TPExtern ename tparams cparams' methods' i
    | TD.TPControl cname cparams eparams params body apply_blk i =>
      let cparams' := F.map (tsub_cparam σ) cparams in
      let params' := F.map (tsub_param σ) params in
      let body' := tsub_Cd σ body in
      let apply_blk' := tsub_s σ apply_blk in
      TD.TPControl cname cparams' eparams params' body' apply_blk' i
    | TD.TPParser pn cps eps ps strt sts i =>
      let cparams' := F.map (tsub_cparam σ) cps in
      let params' := F.map (tsub_param σ) ps in
      let start' := tsub_state σ strt in
      let states' := F.map (tsub_state σ) sts in
      TD.TPParser pn cparams' eps params' start' states' i
    | TD.TPFunction f tparams params body i =>
      let σ' := remove_types σ tparams in
      let cparams' := tsub_arrowT σ' params in
      let body' := tsub_s σ' body in
      TD.TPFunction f tparams cparams' body' i
    (*| TD.TPPackage p tparams cparams i =>
      let σ' := remove_types σ tparams in
      let cparams' := F.map (tsub_cparam σ') cparams in
      TD.TPPackage p tparams cparams' i*)
    | TD.TPSeq d1 d2 i =>
      TD.TPSeq (tsub_d σ d1) (tsub_d σ d2) i
    end.

End TypeSubstitution.
