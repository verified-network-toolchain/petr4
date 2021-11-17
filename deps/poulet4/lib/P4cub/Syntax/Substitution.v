Require Import Poulet4.P4cub.Envn Poulet4.P4cub.Syntax.AST.

Module P := P4cub.
Module E := P.Expr.
Module F := P.F.
Module TD := P.TopDecl.
Module ST := P.Stmt.

Import Env.EnvNotations P.P4cubNotations.

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
    | {{ Bool }}
    | {{ bit<_> }}
    | {{ int<_> }}
    | {{ error }}
    (*| {{ Str }}
    | {{ enum _ { _ } }}*)
    | {{ matchkind }}     => t
    | {{ tuple ts }}      => E.TTuple $ List.map (tsub_t σ) ts
    | {{ struct { ts } }} => E.TStruct $ F.map (tsub_t σ) ts
    | {{ hdr { ts } }}    => E.THeader $ F.map (tsub_t σ) ts
    | {{ stack ts[n] }}   => E.THeaderStack (F.map (tsub_t σ) ts) n
    | E.TVar X => find_default σ X t
    end.
  (**[]*)

  Context {tags_t : Type}.
  
  Fixpoint tsub_e (σ : Env.t string E.t) (e : E.e tags_t) : E.e tags_t :=
    match e with
    | <{ BOOL _ @ _ }>
    | <{ _ W _ @ _ }>
    | <{ _ S _ @ _ }>
    | <{ Error _ @ _ }>
    (*| <{ Stri _ @ _ }>
    | <{ Enum _ dot _ @ _ }>*)
    | <{ Matchkind _ @ _ }> => e
    | <{ Var x : t @ i }> =>
      let t' := tsub_t σ t in
      <{ Var x : t' @ i }>
    | <{ Slice e:t [hi:lo] @ i }> => E.ESlice (tsub_e σ e) (tsub_t σ t) hi lo i
    | <{ Cast e:t @ i }> => E.ECast (tsub_t σ t) (tsub_e σ e) i
    | <{ UOP op e:t @ i }> => E.EUop op (tsub_t σ t) (tsub_e σ e) i
    | <{ BOP e1:t1 op e2:t2 @ i }>
      => E.EBop op (tsub_t σ t1) (tsub_t σ t2) (tsub_e σ e1) (tsub_e σ e2) i
    | <{ tup es @ i }> => E.ETuple (List.map (tsub_e σ) es) i
    | <{ struct { es } @ i }>
      => E.EStruct (F.map (fun '(t,e) => (tsub_t σ t, tsub_e σ e)) es) i
    | <{ hdr { es } valid:=e @ i }>
      => E.EHeader
          (F.map (fun '(t,e) => (tsub_t σ t, tsub_e σ e)) es)
          (tsub_e σ e) i
    | <{ Mem e:t dot x @ i }>
      => E.EExprMember x (tsub_t σ t) (tsub_e σ e) i
    | <{ Stack hs:ts[n] nextIndex:=ni @ i }>
      => E.EHeaderStack (F.map (tsub_t σ) ts) (List.map (tsub_e σ) hs) n ni i
    | <{ Access e[n] @ i }> => E.EHeaderStackAccess (tsub_e σ e) n i
    end.
  (**[]*)


  Fixpoint tsub_param (σ : Env.t string E.t) (pa : P.paramarg E.t E.t) :=
    match pa with
    | P.PAIn t => P.PAIn (tsub_t σ t)
    | P.PAOut t => P.PAOut (tsub_t σ t)
    | P.PAInOut t => P.PAInOut (tsub_t σ t)
    | P.PADirLess t => P.PAInOut (tsub_t σ t)
    end.

  Fixpoint tsub_arg (σ : Env.t string E.t) (pa : P.paramarg (E.t * E.e tags_t) (E.t * E.e tags_t)) :=
    match pa with
    | P.PAIn (t,e) => P.PAIn (tsub_t σ t, tsub_e σ e)
    | P.PAOut (t,e) => P.PAOut (tsub_t σ t, tsub_e σ e)
    | P.PAInOut (t,e) => P.PAInOut (tsub_t σ t, tsub_e σ e)
    | P.PADirLess (t,e) => P.PAInOut (tsub_t σ t, tsub_e σ e)
    end.

  Definition tsub_retE (σ : Env.t string E.t) (ret : option (E.t * E.e tags_t)) :=
    let* '(t,e) := ret in
    Some (tsub_t σ t, tsub_e σ e).

  Fixpoint tsub_arrowE (σ : Env.t string E.t) (ar : TD.E.arrowE tags_t) :=
    let '(P.Arrow args ret) := ar in
    let args' := F.map (tsub_arg σ) args in
    let ret' := tsub_retE σ ret in
    P.Arrow args' ret'.

  Print ST.PApply.

  Fixpoint tsub_s (σ : Env.t string E.t) (s : ST.s tags_t) : ST.s tags_t :=
    match s with
    | ST.SSkip _ => s
    | ST.SVardecl t x i =>
      let t' := tsub_t σ t in
      ST.SVardecl t' x i
    | ST.SAssign typ lhs rhs i =>
      let typ' := tsub_t σ typ in
      let lhs' := tsub_e σ lhs in
      let rhs' := tsub_e σ rhs in
      ST.SAssign typ' lhs' rhs' i
    | ST.SConditional gt g tru fls i =>
      let gt' := tsub_t σ gt in
      let g' := tsub_e σ g in
      let tru' := tsub_s σ tru in
      let fls' := tsub_s σ fls in
      ST.SConditional gt' g' tru' fls' i
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
    | ST.SReturnVoid _ => s
    | ST.SReturnFruit t e i =>
      let t' := tsub_t σ t in
      let e' := tsub_e σ e in
      ST.SReturnFruit t' e' i
    | ST.SExit _ => s
    | ST.SInvoke _ _ => s
    | ST.SApply ci ext_args args i =>
      let args' := F.map (tsub_arg σ) args in
      ST.SApply ci ext_args args i
    | ST.PApply _ pi ext_args args i =>
      let args' := F.map (tsub_arg σ) args in
      ST.PApply _ pi ext_args args' i
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
    | {{{VType t}}} =>
      (* FIXME i dont know why this works and E.CTType t doesnt... *)
      let t := tsub_t σ t in
      {{{VType t}}}
    end.

  Fixpoint tsub_arrowT (σ : Env.t string E.t) (ar : TD.E.arrowT) :=
    let '(P.Arrow params ret) := ar in
    let params' := F.map (tsub_param σ) params in
    let ret' := tsub_retT σ ret in
    P.Arrow params' ret'.

  Fixpoint tsub_method (σ : Env.t string E.t) (method_types : (list string * TD.E.arrowT)) :=
    let '(type_params, arrow) := method_types in
    let σ' := remove_types σ type_params in
    (type_params, tsub_arrowT σ' arrow).

  Definition tsub_table (σ : Env.t string E.t) (tbl : TD.C.table tags_t) :=
    match tbl with
    | TD.C.Table keys acts =>
      let keys' := List.map (fun '(t,e,mk) => (tsub_t σ t, tsub_e σ e, mk)) keys in
      TD.C.Table keys' acts
    end.

  Fixpoint tsub_Cd (σ : Env.t string E.t) (d : TD.C.d tags_t) :=
    match d with
    | TD.C.CDAction a sig body i =>
      let sig' := F.map (tsub_param σ) sig in
      let body' := tsub_s σ body in
      TD.C.CDAction a sig' body' i
    | TD.C.CDTable t tbl i =>
      TD.C.CDTable t (tsub_table σ tbl) i
    | TD.C.CDSeq d1 d2 i =>
      TD.C.CDSeq (tsub_Cd σ d1) (tsub_Cd σ d2) i
    end.

  Print TD.P.state_block.


  Print TD.P.e.

  Fixpoint tsub_transition (σ : Env.t string E.t) (transition : TD.P.e tags_t) :=
    match transition with
    | TD.P.PGoto s i =>
      TD.P.PGoto s i
    | TD.P.PSelect discriminee default cases i =>
      let discriminee' := tsub_e σ discriminee in
      let default' := tsub_transition σ default in
      let cases' := F.map (tsub_transition σ) cases in
      TD.P.PSelect discriminee' default' cases' i
    end.

  Fixpoint tsub_state (σ : Env.t string E.t) (st : TD.P.state_block tags_t) :=
    match st with
    | TD.P.State s e =>
      let e' := tsub_transition σ e in
      TD.P.State s e'
    end.

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
      let body' := tsub_s σ body in
      TD.TPFunction f tparams cparams' body' i
    | TD.TPPackage p tparams cparams i =>
      let σ' := remove_types σ tparams in
      let cparams' := F.map (tsub_cparam σ') cparams in
      TD.TPPackage p tparams cparams' i
    | TD.TPSeq d1 d2 i =>
      TD.TPSeq (tsub_d σ d1) (tsub_d σ d2) i
    end.

  Import String.
  Open Scope string_scope.

  Variable d : tags_t.

  Compute tsub_s [("standard_metadata_t", E.TStruct [])]
          (ST.SFunCall "mark_to_drop" []
                       (P.Arrow
                         [("standard_metadata",
                           P.PAInOut
                            (E.TVar "standard_metadata_t",
                             E.EVar
                              (E.TVar
                                "standard_metadata_t")
                              "standard_metadata" d))]
                         None) d).

End TypeSubstitution.
