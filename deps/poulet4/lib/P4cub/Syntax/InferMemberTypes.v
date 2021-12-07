Require Import Poulet4.P4cub.Envn Poulet4.P4cub.Syntax.AST.
Import String.

(* Module P := P4cub. *)
Module E := Expr.
Module TD := TopDecl.
Module ST := Stmt.

Section Inference.

  Definition infer_or_nop (fs : F.fs string E.t) (mem : string) (t : E.t) :=
    match F.find_value (String.eqb mem) fs with
    | None => t
    | Some t => t
    end.

  Context {tags_t : Type}.

  Fixpoint inf_e  (e : E.e tags_t) : E.e tags_t :=
    match e with
    | E.EBool _ _
    | E.EBit _ _ _
    | E.EInt _ _ _
    | E.EError _ _
    | E.EMatchKind _ _
    | E.EVar _ _ _ =>
      e
    | E.ESlice e hi lo i =>
      Expr.ESlice (inf_e e) hi lo i
    | E.ECast t e i =>
      Expr.ECast t (inf_e e) i
    | E.EUop rt op e i =>
      Expr.EUop rt op (inf_e e) i
    | E.EBop rt op e1 e2 i =>
      Expr.EBop rt op (inf_e e1) (inf_e e2) i
    | E.ETuple es i =>
      E.ETuple (List.map (inf_e) es) i
    | E.EStruct es i =>
      E.EStruct (F.map (inf_e) es) i
    | E.EHeader es e i =>
      Expr.EHeader (F.map (inf_e) es) (inf_e e) i
    | E.EExprMember argtype mem arg i =>
      match argtype with
      | E.TStruct fs =>
        let t := infer_or_nop fs mem argtype in
        E.EExprMember t mem (inf_e arg) i
      | E.THeader fs =>
        let t := infer_or_nop fs mem argtype in
        E.EExprMember t mem (inf_e arg) i
      | t =>
        E.EExprMember t mem (inf_e arg) i
      end
    | E.EHeaderStack fs hs ni i =>
      E.EHeaderStack fs (List.map inf_e hs) ni i
    | E.EHeaderStackAccess result_hdr_type stk index i =>
      E.EHeaderStackAccess result_hdr_type (inf_e stk) index i
    end.
  (**[]*)


 Definition inf_param (pa : paramarg E.t E.t) := pa.


 Definition inf_arg (pa : paramarg (E.e tags_t) (E.e tags_t)) :=
    match pa with
    | PAIn e => PAIn (inf_e e)
    | PAOut e => PAOut (inf_e e)
    | PAInOut e => PAInOut (inf_e e)
    | PADirLess e => PAInOut (inf_e e)
    end.

  Definition inf_retE  (ret : option (E.e tags_t)) :=
    let* e := ret in
    Some (inf_e e).

  Definition inf_arrowE  (ar : E.arrowE tags_t) :=
    let args := paramargs ar in
    let ret := rtrns ar in
    let args' := F.map inf_arg args in
    let ret' := inf_retE ret in
    {| paramargs := args'; rtrns := ret' |}.

  Fixpoint inf_s  (s : ST.s tags_t) : ST.s tags_t :=
    match s with
    | ST.SSkip _ => s
    | ST.SVardecl x e i =>
      let e' := map_sum id inf_e e in
      ST.SVardecl x e' i
    | ST.SAssign lhs rhs i =>
      let lhs' := inf_e lhs in
      let rhs' := inf_e rhs in
      ST.SAssign lhs' rhs' i
    | ST.SConditional g tru fls i =>
      let g' := inf_e g in
      let tru' := inf_s tru in
      let fls' := inf_s fls in
      ST.SConditional g' tru' fls' i
    | ST.SSeq s1 s2 i =>
      let s1' := inf_s s1 in
      let s2' := inf_s s2 in
      ST.SSeq s1' s2' i
    | ST.SBlock b =>
      ST.SBlock (inf_s b)
    | ST.SExternMethodCall extern_name method_name typ_args args i =>
      let args' := inf_arrowE args in
      ST.SExternMethodCall extern_name method_name typ_args args' i
    | ST.SFunCall f typ_args args i =>
      let args' := inf_arrowE args in
      ST.SFunCall f typ_args args' i
    | ST.SActCall a args i =>
      let args' := F.map inf_arg args in
      ST.SActCall a args' i
    | ST.SReturn e i =>
      let e' := inf_retE e in
      ST.SReturn e' i
    | ST.SExit _ => s
    | ST.SInvoke _ _ => s
    | ST.SApply ci ext_args args i =>
      let args' := F.map inf_arg args in
      ST.SApply ci ext_args args i
    (* | ST.PApply _ pi ext_args args i => *)
    (*   let args' := F.map (inf_arg σ) args in *)
    (*   ST.PApply _ pi ext_args args' i *)
    | ST.SHeaderStackOp _ _ _ _ => s
    | ST.SSetValidity _ _ _ => s
    end.


  Definition inf_carg  (carg : E.constructor_arg tags_t) :=
    match carg with
    | E.CAName _ => carg
    | E.CAExpr e => E.CAExpr (inf_e e)
    end.

  Definition inf_retT  (ret : option E.t) := ret.

  Fixpoint inf_cparam  (ctor_type : E.ct) :=
    match ctor_type with
    | E.CTControl cparams extern_params params =>
      E.CTControl (F.map inf_cparam cparams) extern_params
                  (F.map inf_param params)
    | E.CTParser cparams extern_params params =>
      E.CTParser (F.map inf_cparam cparams) extern_params
                 (F.map inf_param params)
    | E.CTPackage cparams =>
      E.CTPackage (F.map inf_cparam cparams)
    | E.CTExtern _
    | E.CTType _ => ctor_type
    end.

  Definition inf_arrowT  (ar : E.arrowT) :=
    let params := paramargs ar in
    let ret := rtrns ar in
    let params' := F.map inf_param params in
    let ret' := inf_retT ret in
    {| paramargs := params'; rtrns := ret' |}.

  Definition inf_method  (method_types : (list string * E.arrowT)) :=
    let '(type_params, arrow) := method_types in
    (type_params, inf_arrowT arrow).

  Definition inf_table  (tbl : Control.table tags_t) :=
    let tbl_keys := Control.table_key tbl in
    let tbl_acts := Control.table_actions tbl in
    let tbl_keys' := List.map (fun '(e,mk) => (inf_e e, mk)) tbl_keys in
    {| Control.table_key := tbl_keys'; Control.table_actions := tbl_acts |}.

  Fixpoint inf_Cd  (d : Control.d tags_t) :=
    match d with
    | Control.CDAction a sig body i =>
      let sig' := F.map inf_param sig in
      let body' := inf_s body in
      Control.CDAction a sig' body' i
    | Control.CDTable t tbl i =>
      Control.CDTable t (inf_table tbl) i
    | Control.CDSeq d1 d2 i =>
      Control.CDSeq (inf_Cd d1) (inf_Cd d2) i
    end.

  Fixpoint inf_transition  (transition : Parser.e tags_t) :=
    match transition with
    | Parser.PGoto s i =>
      Parser.PGoto s i
    | Parser.PSelect discriminee default cases i =>
      let discriminee' := inf_e discriminee in
      let default' := inf_transition default in
      let cases' := F.map inf_transition cases in
      Parser.PSelect discriminee' default' cases' i
    end.

  Definition inf_state  (st : Parser.state_block tags_t) :=
    let s := Parser.stmt st in
    let e := Parser.trans st in
    let e' := inf_transition e in
    {| Parser.stmt := s; Parser.trans := e' |}.

  Fixpoint inf_d  (d : TD.d tags_t) : TD.d tags_t :=
    match d with
    | TD.TPInstantiate cname iname type_args cargs i =>
      let cargs' := F.map inf_carg cargs in
      TD.TPInstantiate cname iname type_args cargs' i
    | TD.TPExtern ename tparams cparams methods i =>
      let cparams' := F.map inf_cparam cparams in
      let methods' := F.map inf_method methods in
      TD.TPExtern ename tparams cparams' methods' i
    | TD.TPControl cname cparams eparams params body apply_blk i =>
      let cparams' := F.map inf_cparam cparams in
      let params' := F.map inf_param params in
      let body' := inf_Cd body in
      let apply_blk' := inf_s apply_blk in
      TD.TPControl cname cparams' eparams params' body' apply_blk' i
    | TD.TPParser pn cps eps ps strt sts i =>
      let cparams' := F.map inf_cparam cps in
      let params' := F.map inf_param ps in
      let start' := inf_state strt in
      let states' := F.map inf_state sts in
      TD.TPParser pn cparams' eps params' start' states' i
    | TD.TPFunction f tparams params body i =>
      let cparams' := inf_arrowT params in
      let body' := inf_s body in
      TD.TPFunction f tparams cparams' body' i
    (*| TD.TPPackage p tparams cparams i =>
      let cparams' := F.map inf_cparam cparams in
      TD.TPPackage p tparams cparams' i*)
    | TD.TPSeq d1 d2 i =>
      TD.TPSeq (inf_d d1) (inf_d d2) i
    end.

End Inference.
