Require Export Poulet4.Syntax.
Require Import Poulet4.SimplExpr.
Require Export
        Poulet4.P4cub.Syntax.Syntax
        Poulet4.P4cub.Util.Result
        Poulet4.P4cub.BigStep.InstUtil.
Import AST Result P4cub Envn.
Import ResultNotations.

Require Import String.
Open Scope string_scope.


Module ST := Stmt.
Module E := Expr.

Module NameGen.
  Definition t := list (string * nat).
  Fixpoint rep s n :=
    match n with
    | O => ""
    | S n' => s ++ rep s n'
    end.

  Fixpoint fresh (g : t) (x : string) : (t * string) :=
    match g with
    | [] => ([(x, 1)], x)
    | (y,n)::g' =>
      if String.eqb y x
      then
        ((y,n+1)::g', x ++ rep "$" n)
      else
        let (g'', x') := fresh g' x in
        ((y,n)::g'', x')
    end.

End NameGen.


Section ToP4cub.
  Variable tags_t : Type.

  Import Typed.
  Import P4Int.

  Definition pos : (nat -> positive) := BinPos.Pos.of_nat.
  Definition posN (n : N) : positive := pos (BinNat.N.to_nat n).

  Record DeclCtx :=
    { controls :  list (TopDecl.d tags_t);
      parsers : list (TopDecl.d tags_t);
      tables : @tenv tags_t;
      actions : @aenv tags_t;
      functions : list (TopDecl.d tags_t);
      packages : list (TopDecl.d tags_t);
      externs : list (TopDecl.d tags_t);
    }.

  Definition empty_declaration_context :=
    {| controls := [];
       parsers := [];
       tables := Env.empty string (CD.table tags_t);
       actions := Env.empty string adecl;
       functions := [];
       packages := [];
       externs := []
    |}.


  Definition add_control (decl : DeclCtx) (c : TopDecl.d tags_t) :=
    {| controls := c::decl.(controls);
       parsers := decl.(parsers);
       tables := decl.(tables);
       actions := decl.(actions);
       functions := decl.(functions);
       packages := decl.(packages);
       externs := decl.(externs);
    |}.

  Definition add_parser (decl : DeclCtx) (p : TopDecl.d tags_t) :=
    {| controls := decl.(controls);
       parsers := p::decl.(parsers);
       tables := decl.(tables);
       actions := decl.(actions);
       functions := decl.(functions);
       packages := decl.(packages);
       externs := decl.(externs);
    |}.

  Definition add_package (decl : DeclCtx) (p : TopDecl.d tags_t) :=
    {| controls := decl.(controls);
       parsers := decl.(parsers);
       tables := decl.(tables);
       actions := decl.(actions);
       functions := decl.(functions);
       packages := p::decl.(packages);
       externs := decl.(externs);
    |}.

  Definition add_extern (decl : DeclCtx) (e : TopDecl.d tags_t) :=
    {| controls := decl.(controls);
       parsers := decl.(parsers);
       tables := decl.(tables);
       actions := decl.(actions);
       functions := decl.(functions);
       packages := decl.(packages);
       externs := e::decl.(externs);
    |}.

  Print List.fold_right.

  Definition to_decl (tags : tags_t) (decls : DeclCtx) : TopDecl.d tags_t :=
    (** FIXME ACTIONS & TABLES??? *)
    let decls := List.concat [decls.(controls); decls.(parsers); decls.(functions); decls.(packages); decls.(externs)] in
    List.fold_right (fun d1 d2 => TopDecl.TPSeq d1 d2 tags)
                    (TopDecl.TPFunction "$DUMMY" (Arrow [] None) (ST.SSkip tags) tags)
                    decls.

  Definition extend (hi_prio lo_prio: DeclCtx) : DeclCtx :=
    let combine f := List.app (f hi_prio) (f lo_prio) in
    {| controls := combine controls;
       parsers := combine parsers;
       tables := List.app hi_prio.(tables) lo_prio.(tables);
       actions := List.app hi_prio.(actions) lo_prio.(actions);
       functions := combine functions;
       packages := combine packages;
       externs := combine externs;
    |}.

  Print adecl.

  Definition to_action_ctrl_decl tags '(act_name, adecl) : TopDecl.C.d tags_t :=
    let '(ADecl cl fs aa eis params body) := adecl in
    (** FIXME ADD PARAMETERS *)
    TopDecl.C.CDAction act_name [] body tags.

  Definition to_table_ctrl_decl tags '(tbl_name, tdecl) : TopDecl.C.d tags_t :=
    TopDecl.C.CDTable tbl_name tdecl tags.

  Definition to_ctrl_decl tags (c: DeclCtx) : TopDecl.C.d tags_t :=
    let actions := List.map (to_action_ctrl_decl tags) c.(actions) in
    let tables := List.map (to_table_ctrl_decl tags) c.(tables) in
    List.fold_right (fun d1 d2 => TopDecl.C.CDSeq d1 d2 tags)
                    (TopDecl.C.CDAction "$DUMMY_ACTION" [] (ST.SSkip tags) (tags))
                    (List.app actions tables).

  Definition find {A : Type} (f : A -> bool) : list A -> option A :=
    List.fold_right (fun x found => match found with | None => if f x then Some x else None | Some _ => found end) None.

  Definition decl_has_name (name : string) (d : TopDecl.d tags_t) :=
    let matches := String.eqb name in
    match d with
    | TopDecl.TPInstantiate _ instance_name _ _ => matches instance_name
    | TopDecl.TPExtern extern_name _ _ _ => matches extern_name
    | TopDecl.TPControl control_name _ _ _ _ _ _ => matches control_name
    | TopDecl.TPParser parser_name _ _ _ _ _ _ => matches parser_name
    | TopDecl.TPFunction function_name _ _ _ => matches function_name
    | TopDecl.TPPackage package_name _ _ => matches package_name
    | TopDecl.TPSeq _ _ _ =>
      (* Should Not Occur *)
      false
    end.

  Definition lookup_instantiatable (ctx : DeclCtx) (name : string) :=
    find (decl_has_name name) (ctx.(controls) ++ ctx.(parsers) ++ ctx.(packages) ++ ctx.(externs)).

  Definition translate_op_uni (op : OpUni) : E.uop :=
    match op with
    | Not => E.Not
    | BitNot => E.BitNot
    | UMinus => E.UMinus
    end.

  Definition translate_op_bin (op : OpBin) : result E.bop :=
    match op with
    | Plus => ok E.Plus
    | PlusSat => ok E.PlusSat
    | Minus => ok E.Minus
    | MinusSat => ok E.MinusSat
    | Mul => ok E.Times
    | Div => error "division not supported"
    | Mod => error "mod not supported"
    | Shl => ok E.Shl
    | Shr => ok E.Shr
    | Le => ok E.Le
    | Ge => ok E.Ge
    | Lt => ok E.Lt
    | Gt => ok E.Gt
    | Eq => ok E.Eq
    | NotEq => ok E.NotEq
    | BitAnd => ok E.BitAnd
    | BitXor => ok E.BitXor
    | BitOr => ok E.BitOr
    | PlusPlus => ok E.PlusPlus
    | And => ok E.And
    | Or => ok E.Or
    end.

  (* TODO move to Result.v *)
  Definition cons_res {A : Type} (hd_res : result A) (rlist : result (list A)) : result (list A) :=
    let* l := rlist in
    let** hd := hd_res in
    hd :: l.


  Print Typed.name.
  Program Fixpoint translate_exp_type (i : tags_t) (typ : @P4Type tags_t) {struct typ} : result E.t :=
    let translate_fields :=
        fold_right (fun '(name,typ) res_rst =>
                      let* cub_typ := translate_exp_type i typ in
                      let** rst := res_rst in
                      (P4String.str name, cub_typ) :: rst ) (ok [])
    in
    match typ with
    | TypBool => ok E.TBool
    | TypString =>
      (* TODO Strings should only occur as arguments to externs.  We should add these to P4cub *)
      ok E.TString
    | TypInteger =>
      (* TODO This should be added to P4cub, but can only be a value; enforced by the type system *)
      error "[FIXME] P4cub doesnt support Integers"
    | TypInt w => ok (E.TInt (pos w))
    | TypBit w => ok (E.TBit (pos w))
    | TypVarBit w =>
      error "[FIXME] Compile to fixed-width"
    | TypArray typ size =>
      match typ with
      | TypHeader fields =>
        let** cub_fields := translate_fields fields in
        E.THeaderStack cub_fields (pos size)
      | _ => error "Typeerror:: Arrays must contain Headers"
      end
    | TypTuple types =>
      (* TODO ensure are cast-able *)
      let** cub_types := fold_right (cons_res ∘ (translate_exp_type i)) (ok []) types in
      E.TTuple cub_types
    | TypList types =>
      let** cub_types := fold_right (cons_res ∘ (translate_exp_type i)) (ok []) types in
      E.TTuple cub_types
    | TypRecord fields =>
      let** cub_fields := translate_fields fields in
      E.TStruct cub_fields
    | TypSet elt_type =>
      (* Shows up in typechecking a select *)
      error "A set is not an expression type"
    | TypError => ok E.TError
    | TypMatchKind => ok E.TMatchKind
    | TypVoid => error "[FIXME] void is not the type of any expression literal"
    | TypHeader fields =>
      let** fields' := translate_fields fields in
      E.THeader fields'
    | TypHeaderUnion _ =>
      error "[FIXME] Header Unions need to be compiled away or added to p4cub"
    | TypStruct fields =>
      let** fields' := translate_fields fields in
      E.TStruct fields'
    | TypEnum name typ members =>
      (* TODO We're throwing away the type here. Should we be? *)
      let cub_name := P4String.str name in
      (* For some reason Coq needs this to ebe explicitly applied in order to guess the tags argument *)
      let cub_members := List.map (fun s => P4String.str s) members in
      ok (E.TEnum cub_name cub_members)
    | TypTypeName name =>
      match name with
      | BareName nm =>
        ok (E.TVar (P4String.str nm))
      | QualifiedName _ _ =>
        error "Unsure how to handle qualified names"
      end
    | TypNewType name typ =>
      let** typ' := translate_exp_type i typ in
      typ'
    | TypControl c =>
      error "A control is not an expression type"
    | TypParser c =>
      error "A Parser is not an expression type"
    | TypExtern name =>
      error "An extern is not an expression type"
    | TypFunction fn =>
      error "A function is not an expression"
    | TypAction _ _ =>
      error "An action is not an expression"
    | TypTable _ =>
      error "A table is not an expression"
    | TypPackage _ _ _ =>
      error "A package is not an expression"
    | TypSpecializedType base args =>
      error "Specialized types are not expression types"
    | TypConstructor _ _ _ _ =>
      error "A type constructor is not an expression"
    end.

  Definition realize_array_index (e : @Expression tags_t) : result Z :=
    match e with
    | MkExpression _ (ExpInt z) _ _  =>
      (*TODO Do we have to do some normalizaztion here?*)
      ok (z.(value))
    | _ =>
      error "Array Indices must be literals"
    end.

  Section HoistEffects.

    Definition get_type_of_expr (e : Expression) : @P4Type tags_t :=
      let '(MkExpression _ _ typ _) := e in
      typ.


    Fixpoint voidify_fun_stmt  (ret : P4String.t tags_t) (s : Statement) : Statement :=
      let '(MkStatement tags stmt typ) := s in
      let stmt' := voidify_fun_stmt_pre ret tags stmt typ in
      MkStatement tags stmt' typ

    with voidify_fun_stmt_pre (ret : P4String.t tags_t) (tags : tags_t) (stmt : StatementPreT) (typ : StmType) : StatementPreT :=
      match stmt with
      | StatMethodCall _ _ _ => stmt
      | StatAssignment _ _ => stmt
      | StatDirectApplication _ _ => stmt
      | StatConditional cond tru fls_opt =>
        let tru' := voidify_fun_stmt ret tru in
        let fls' := let* fls := fls_opt in Some (voidify_fun_stmt ret fls) in
        StatConditional cond tru fls'
      | StatBlock block =>
        StatBlock (voidify_fun_block ret block)
      | StatExit => stmt
      | StatEmpty => stmt
      | StatReturn opt_e =>
        match opt_e with
        | None => StatReturn None
        | Some e =>
          let typ := get_type_of_expr e in
          let ret_exp := MkExpression tags (ExpName (BareName ret) NoLocator) typ InOut in
          let assn := MkStatement tags (StatAssignment ret_exp e) StmUnit in
          let ret_void := MkStatement tags (StatReturn None) StmUnit in
          let blck := BlockCons assn (BlockCons ret_void (BlockEmpty tags)) in
          StatBlock blck
        end
      | StatSwitch expr cases =>
        let case' := List.map (fun c =>
                                 match c with
                                 | StatSwCaseAction tags label code =>
                                   let code' := voidify_fun_block ret code in
                                   StatSwCaseAction tags label code'
                                 | StatSwCaseFallThrough _ _  =>
                                   c
                                 end) cases in
        StatSwitch expr cases
      | StatConstant _ _ _ _ => stmt
      | StatVariable _ _ _ _ => stmt
      | StatInstantiation _ _ _ _ => stmt
      end

    with voidify_fun_block (ret : P4String.t tags_t) (b : Block) :=
      match b with
      | BlockEmpty t => BlockEmpty t
      | BlockCons stmt rst =>
        let s := voidify_fun_stmt ret stmt in
        let b := voidify_fun_block ret rst in
        BlockCons s b
      end.


    Definition compute_return_var (name : P4String.t tags_t) :=
      {| P4String.tags := name.(P4String.tags);
         P4String.str  := name.(P4String.str) ++ "_ret$" |}.

    Definition compute_void_name (name : P4String.t tags_t) :=
      {| P4String.tags := name.(P4String.tags);
         P4String.str := name.(P4String.str) ++ "_void$"|}.

    Definition voidify_fun_decl (tags : tags_t) (ret: @P4Type tags_t) (name : P4String.t tags_t) (body : @Block tags_t) : result (tags_t * P4String.t tags_t * @Block tags_t) :=
      match ret with
      | TypVoid => error "TypeError:: void functions are invalid as expressions"
      | _ =>
        let return_var := compute_return_var name in
        let name' := compute_void_name name in
        let body' : Block := voidify_fun_block return_var body in
        ok (tags, name', body')
      end.

    Definition voidify_fun_call_exp (func_e : @Expression tags_t)  (typ_args : list (@P4Type tags_t)) (args : list (option (@Expression tags_t)))  : result (@Statement tags_t * @Expression tags_t) :=
      let '(MkExpression tags func typ dir) := func_e in
      match func with
      | ExpExpressionMember expr name =>
        let name':= compute_void_name name in
        let return_var := compute_return_var name in
        let pre_exp := ExpExpressionMember expr name' in
        let exp : Expression := MkExpression tags pre_exp typ dir in
        let pre_stmt := StatMethodCall exp typ_args args in
        let stmt := MkStatement tags pre_stmt StmUnit in
        let replacement := MkExpression tags (ExpName (BareName return_var) NoLocator) typ dir in
        ok (stmt, replacement)

      | ExpName name loc =>
        match name with
        | BareName n =>
          let name' := compute_void_name n in
          let return_var := compute_return_var n in
          let exp := (MkExpression tags (ExpName (BareName name') loc) typ dir) in
          let stmt : Statement := MkStatement tags (StatMethodCall exp typ_args args) StmUnit in
          let replacement : Expression := MkExpression tags (ExpName (BareName return_var) loc) typ dir in
          ok (stmt, replacement)
        | _ =>
          error "Qualified Names deprecated"
        end
      | _ => error "Typerror :: unrecognized function application"
      end.

    Fixpoint extract_funs_from_exp (e : Expression) : result (list Statement * Expression) :=
      let '(MkExpression tags expr typ dir) := e in
      let** (hoist, e) := extract_funs_from_exp_pre_t expr in
      (hoist, MkExpression tags e typ dir)
    with extract_funs_from_exp_pre_t (e : ExpressionPreT) : result (list Statement * ExpressionPreT) :=
      match e with
      | ExpBool _ => ok ([], e)
      | ExpInt _ => ok ([], e)
      | ExpString _ => ok ([], e)
      | ExpName _ _ => ok ([], e)
      | ExpArrayAccess array index =>
        let* (array_hoist, array') := extract_funs_from_exp array in
        let** (index_hoist, index') := extract_funs_from_exp index in
        (List.app array_hoist index_hoist, ExpArrayAccess array index)
      | ExpBitStringAccess bits lo hi =>
        let** (bits_hoist, bits') := extract_funs_from_exp bits in
        (bits_hoist, ExpBitStringAccess bits' lo hi)
      | ExpList values =>
        let** (hoist, values') := fold_right (fun v acc =>
                                                let* (v_hs, v') := extract_funs_from_exp v in
                                                let** (hs, vs) := acc in
                                                (List.app v_hs hs, v'::vs)) (ok ([],[])) values in
        (hoist, ExpList values')
      | ExpRecord entries =>
        let** (hoist, entries) := fold_right (fun kv acc =>
                                                let '(MkKeyValue tags key value) := kv in
                                                let* (h, value') := extract_funs_from_exp value in
                                                let** (hs, vs) := acc in
                                                (List.app h hs, (MkKeyValue tags key value')::vs)
                                             ) (ok ([],[])) entries in
        (hoist, ExpRecord entries)
      | ExpUnaryOp op arg =>
        let** (hoist, arg') := extract_funs_from_exp arg in
        (hoist, ExpUnaryOp op arg')
      | ExpBinaryOp op (lhs,rhs) =>
        let* (hoist_left, lhs') := extract_funs_from_exp lhs in
        let** (hoist_right, rhs') := extract_funs_from_exp rhs in
        (List.app hoist_left hoist_right, ExpBinaryOp op (lhs', rhs'))
      | ExpCast typ e =>
        let** (hoist, e') := extract_funs_from_exp e in
        (hoist, ExpCast typ e')
      | ExpTypeMember _ _ => ok ([], e)
      | ExpErrorMember _ => ok ([], e)
      | ExpExpressionMember expr name =>
        let** (hoist, expr') := extract_funs_from_exp expr in
        (hoist, ExpExpressionMember expr' name)
      | ExpTernary cond tru fls =>
        let*  (hoist_cond, cond') := extract_funs_from_exp cond in
        let*  (hoist_tru, tru') := extract_funs_from_exp tru in
        let** (hoist_fls, fls') := extract_funs_from_exp fls in
        (List.app (List.app hoist_cond hoist_tru) hoist_fls,
         ExpTernary cond' tru' fls')
      | ExpFunctionCall func type_args args =>
        let* (hoist_args, args') := fold_right (fun a_opt acc =>
                                                  let* (hs, args) := acc in
                                                  match a_opt with
                                                  | None =>
                                                    ok (hs, None :: args)
                                                  | Some arg =>
                                                    let** (h, arg') := extract_funs_from_exp arg in
                                                    (List.app h hs, (Some arg') :: args)
                                                  end)
                                               (ok ([],[]))
                                               args
        in
        let** (hoist_f, func') := voidify_fun_call_exp func type_args args' in
        (hoist_f :: hoist_args, ExpFunctionCall func' type_args args')

      | ExpNamelessInstantiation typ args =>
        let* (hoist_args, args') := fold_right (fun arg acc =>
                                                  let* (h, arg') := extract_funs_from_exp arg in
                                                  let** (hs, args) := acc in
                                                  (List.app h hs, arg' :: args))
                                               (ok ([],[]))
                                               args in
        let** (hoist_ni, ni_var) := error "[FIXME] hoist Nameless Instantiation" in
        (List.app hoist_args hoist_ni, ni_var)
      | ExpDontCare => ok([], e)
      | ExpMask e m =>
        let*  (hoist_e, e') := extract_funs_from_exp e in
        let** (hoist_m, m') := extract_funs_from_exp m in
        (List.app hoist_e hoist_m, ExpMask e' m')

      | ExpRange lo hi =>
        let*  (hoist_lo, lo') := extract_funs_from_exp lo in
        let** (hoist_hi, hi') := extract_funs_from_exp hi in
        (List.app hoist_lo hoist_hi, ExpRange lo' hi')
      end.

    Function hoist_functions (statement : @Statement tags_t) : result (@Statement tags_t) := error "Implement.".

  End HoistEffects.

  Section ElimDA.

    Fixpoint get_string_from_type (t : P4Type) : result (P4String.t tags_t) :=
      match t with
      | TypTypeName (BareName str) => ok str
      | TypSpecializedType t [] => get_string_from_type t
      | TypControl c => error "[FIXME] get name from control type"
      | TypParser c => error "[FIXME] get name from parser type"
      | _ => error "Don't know how to get constructor from arbitrary type"
      end.

    Definition inst_name_from_type (g : NameGen.t) (t : P4Type) : result (NameGen.t * P4String.t tags_t) :=
      let** type_name := get_string_from_type t in
      let (g, name) := NameGen.fresh g (P4String.str type_name) in
      let p4str_name := {| P4String.tags := P4String.tags type_name;
                           P4String.str := name
                        |} in
      (g, p4str_name).


    (** Eliminate direct application statements by minpting a new name and then applying that named thing *)
    Fixpoint elim_da_statement (namegen : NameGen.t) (s : Statement) :=
      let '(MkStatement tags stmt typ) := s in
      let** (g, stmt') := elim_da_pre_statement namegen tags stmt typ in
      (g, MkStatement tags stmt typ)
    with elim_da_pre_statement (namegen : NameGen.t) (tags : tags_t) (stmt : StatementPreT) (type : StmType) : result (NameGen.t * StatementPreT) :=
      match stmt with
      | StatDirectApplication typ args =>
        let** (namegen', inst_name) := inst_name_from_type namegen typ in
        let inst := StatInstantiation typ args inst_name None in
        let inst_stmt := MkStatement tags inst type in
        let inst_pre := ExpName (BareName inst_name) NoLocator in
        let inst_exp := MkExpression tags inst_pre typ InOut in
        let apply_name := {|P4String.tags := tags; P4String.str := "apply" |} in
        let inst_apply := ExpExpressionMember inst_exp apply_name in
        let inst_apply_exp := MkExpression tags inst_apply typ InOut in
        let aply := StatMethodCall inst_apply_exp [] [] in
        let aply_stmt := MkStatement tags aply type in
        let blck := BlockCons inst_stmt (BlockCons aply_stmt (BlockEmpty tags)) in
        (namegen', StatBlock blck)
      | StatConditional cond tru fls_opt =>
        let* (g', tru') := elim_da_statement namegen tru in
        match fls_opt with
        | None => ok (g', StatConditional cond tru' None)
        | Some fls =>
          let** (g'', fls') := elim_da_statement namegen fls in
          (g'', StatConditional cond tru' (Some fls'))
        end
      | StatBlock blck =>
        let** (g', blck') := elim_da_block namegen blck in
        (g', StatBlock blck')
      | _ => ok (namegen, stmt)
      end
    with elim_da_block (g : NameGen.t) (block : @Block tags_t) :=
      match block with
      | BlockEmpty _ => ok (g, block)
      | BlockCons st rst =>
        let* (g', st') := elim_da_statement g st in
        let** (g'', rst') := elim_da_block g' rst in
        (g'', BlockCons st' rst')
      end.

  End ElimDA.


  Fixpoint translate_expression_pre_t (i : tags_t) (typ : P4Type) (e_pre : @ExpressionPreT tags_t) : result (E.e tags_t) :=
    match e_pre with
    | ExpBool b =>
      ok (E.EBool b i)
    | ExpInt z =>
      match z.(width_signed) with
      | Some (w, b) =>
        if b then
          ok (E.EInt (pos w) z.(value) z.(tags))
        else
          ok (E.EBit (pos w) z.(value) z.(tags))
      | None => error "[FIXME] integer didnt have a width."
      end
    | ExpString s =>
      ok (E.EString (P4String.str s) i)
    | ExpName name loc =>
      match name with
      | BareName str =>
        let** cub_type := translate_exp_type i typ in
        E.EVar cub_type (P4String.str str) i
      | QualifiedName namespaces name =>
        error "Qualified names should be eliminated"
      end
    | ExpArrayAccess array index =>
      let* (_,stck) := translate_expression array in
      let** index := realize_array_index index in
      E.EHeaderStackAccess stck index i
    | ExpBitStringAccess bits lo hi =>
      let** (typ,e) := translate_expression bits in
      E.ESlice e typ (posN hi) (posN lo) i
    | ExpList values =>
      let f := fun v res_rst =>
                 let* (_,cub_v) := translate_expression v in
                 let** rst := res_rst in
                 cub_v :: rst in
      let** cub_values := fold_right f (ok []) values in
      E.ETuple cub_values i
    | ExpRecord entries =>
      let f := fun kv res_rst =>
                 let '(MkKeyValue i nm expr) := kv in
                 let* type_expr := translate_expression expr in
                 let** rst := res_rst in
                 (P4String.str nm, type_expr) :: rst in
      let** cub_entries := fold_right f (ok []) entries  in
      E.EStruct cub_entries i
    | ExpUnaryOp op arg =>
      let eop := translate_op_uni op in
      let** (type, earg) := translate_expression arg in
      E.EUop eop type earg i
    | ExpBinaryOp op (e1,e2) =>
      let* (t1,e1') := translate_expression e1 in
      let* (t2,e2') := translate_expression e2 in
      let** eop := translate_op_bin op in
      E.EBop eop t1 t2 e1' e2' i
    | ExpCast typ expr =>
      let* (_,expr') := translate_expression expr in
      let** typ' := translate_exp_type i typ in
      E.ECast typ' expr' i
    | ExpTypeMember typ name =>
      error "[FIXME] type members unimplemented"
    | ExpErrorMember str =>
      ok (E.EError (Some (P4String.str str)) i)
    | ExpExpressionMember expr name =>
      let** (cub_typ,cub_expr) := translate_expression expr in
      E.EExprMember (P4String.str name) cub_typ cub_expr i
    | ExpTernary cond tru fls =>
      error "Ternary expressions should have been hoisted by a previous pass"
    | ExpFunctionCall func type_args args =>
      error "Function Calls should have been hoisted by a previous pass"
    | ExpNamelessInstantiation typ args =>
      error "Nameless Intantiations should have been hoisted by a previous pass"
    | ExpDontCare =>
      error "[FIXME] These are actually patterns (unimplemented)"
    | ExpMask expr mask =>
      error "[FIXME] actually patterns (unimplemented)"
    | ExpRange lo hi =>
      error "[FIXME] actually patterns (unimplemented)"
    end
  with translate_expression (e : @Expression tags_t) : result (E.t * E.e tags_t) :=
    match e with
    | MkExpression tags expr typ dir =>
      let* cub_type := translate_exp_type tags typ in
      let** cub_expr := translate_expression_pre_t tags typ expr in
      (cub_type, cub_expr)
    end.

  Definition get_name (e : Expression) : result (P4String.t tags_t) :=
    let '(MkExpression _ pre_e _ _ ) := e in
    match pre_e with
    | ExpName (BareName n ) _ => ok n
    | ExpName _ _ => error "Qualified Names are Deprecated"
    | _ => error "Tried to get the name of an expression that wasn't an ExpName"
    end.

  Definition optionlist_to_list {A : Type} : list (option A) -> list A :=
    fold_right (fun x_opt acc => match x_opt with
                                 | None => acc
                                 | Some x => x::acc
                                 end) [].

  Definition translate_return_type (tags : tags_t) (ret : @P4Type tags_t) :=
    match ret with
    | TypVoid => ok None
    | _ =>
      let** x := translate_exp_type tags ret in
      Some x
    end.

  Definition apply_arg_to_param (x : string * paramarg E.t E.t * (E.t * E.e tags_t)) (acc : result (F.fs string (paramarg (E.t * E.e tags_t) (E.t * E.e tags_t)))) : result (F.fs string (paramarg (E.t * E.e tags_t) (E.t * E.e tags_t))) :=
    let '(name, typ, (_, exp)) := x in
    let** fs := acc in
    match typ with
    | PAIn t => (name, PAIn (t, exp)) :: fs
    | PAOut t => (name, PAOut (t, exp)) :: fs
    | PAInOut t => (name, PAInOut (t,exp)) :: fs
    end.


  Definition apply_args_to_params (params : F.fs string (paramarg E.t E.t)) (args : list (E.t * E.e tags_t)) : result (F.fs string (paramarg (E.t * E.e tags_t) (E.t * E.e tags_t))) :=
    let* params_args := zip params args in
    fold_right apply_arg_to_param (ok []) params_args.

  Definition translate_expression_member_call
             (args : list (option (@Expression tags_t)))
             (tags : tags_t)
             (ctx : DeclCtx)
             (callee : Expression)
             (f : P4String.t tags_t) : result (ST.s tags_t) :=
    let f_str := P4String.str f in
    let* callee_name := get_name callee in
    let typ := get_type_of_expr callee in
    if f_str =? "apply"
    then
      match typ with
      | TypControl (MkControlType type_params parameters) =>
        error "[FIXME] translate control apply calls"
      | TypTable _ =>
        ok (ST.SInvoke (P4String.str callee_name) tags)
      | TypParser _ =>
        error "[FIXME] translate parser apply calls"
      | _ =>
        error "Error got a type that cannot be applied."
      end
    else
      match typ with
      | TypExtern e =>
        let* args := error "[FIXME] add action args" in
        ok (ST.SExternMethodCall (P4String.str callee_name) f_str args tags)
      | TypAction data_params control_params =>
        let* act_args := error "[FIXME] add action args" in
        ok (ST.SActCall (P4String.str callee_name) act_args tags)
      | TypTypeName (BareName extern_obj) =>
        let extern_str := (P4String.str extern_obj : string) in
        let extern_decl :=  find (decl_has_name extern_str) ctx.(externs) in
        match extern_decl with
        | None => error (String.append "ERROR expected an extern, but got " extern_str)
        | Some (TopDecl.TPExtern extn_name cparams methods i) =>
          let called_method := find (fun '(nm, _) => String.eqb nm f_str) methods in
          match called_method with
          | None =>
          error (append "Couldn't find " (append (append extern_str ".") f_str))
          | Some (_, Arrow params _) =>
            let* cub_args := rred (List.map translate_expression (optionlist_to_list args)) in
            let* paramargs := apply_args_to_params params cub_args in
            (* TODO Currently assuming method calls return None*)
            let typ : E.arrowE tags_t := Arrow paramargs None in
            ok (ST.SExternMethodCall (P4String.str extern_obj) f_str typ tags)
          end
        | Some _ =>
          error "Invariant Violated. Declaration Context Extern list contained something other than an extern."
        end
      | _ =>
        error (String.append "ERROR: :: Cannot translate non-externs member functions that aren't `apply`s: " f_str)
      end.

  Fixpoint translate_statement_switch_case (ssw : @StatementSwitchCase tags_t) : result (ST.s tags_t) :=
    match ssw with
    | StatSwCaseAction tags label code =>
      error "[FIXME] switch case action unimplemented"
    | StatSwCaseFallThrough tags label =>
      error "[FIXME] switch case fall through unimplemented"
    end
  with translate_statement_pre_t (ctx : DeclCtx) (i : tags_t) (pre_s : @StatementPreT tags_t) : result (ST.s tags_t) :=
    match pre_s with
    | StatMethodCall func type_args args =>
      let '(MkExpression tags func_pre typ dir) := func in
      match func_pre with
      | ExpExpressionMember callee f =>
        translate_expression_member_call args tags ctx callee f
      | ExpName (BareName n) loc =>
        match typ with
        | TypFunction (MkFunctionType type_params parameters kind ret) =>
          let** args := error "[FIXME] compute function args for function call" in
          ST.SFunCall (P4String.str n) args tags
        | _ => error "A name, applied like a method call, must be a function or extern type; I got something else"
        end
      | _ => error "ERROR :: Cannot handle this kind of expression"
      end
    | StatAssignment lhs rhs =>
      let* (cub_ltyp, cub_lhs) := translate_expression lhs in
      let** (_, cub_rhs) := translate_expression rhs in
      ST.SAssign cub_ltyp cub_lhs cub_rhs i
    | StatDirectApplication typ args =>
      error "[FIXME] (StatDirectApplication) Need to translate into instantiation and then application"
    | StatConditional cond tru fls_opt =>
      let* (cub_type, cub_cond) := translate_expression cond in
      let* cub_tru := translate_statement ctx tru in
      let** cub_fls := match fls_opt with
                       | None => ok (ST.SSkip i)
                       | Some fls => translate_statement ctx fls
                       end in
      ST.SConditional cub_type cub_cond cub_tru cub_fls i
    | StatBlock block =>
      let** sblck := translate_block ctx i block in
      ST.SBlock sblck
    | StatExit =>
      ok (ST.SExit i)
    | StatEmpty =>
      ok (ST.SSkip i)
    | StatReturn expr_opt =>
      match expr_opt with
      | Some e =>
        let** (cub_typ, cub_expr) := translate_expression e in
        ST.SReturnFruit cub_typ cub_expr i
      | None =>
        ok (ST.SReturnVoid i)
      end
    | StatSwitch expr cases =>
      error "[FIXME] switch statement not implemented"
    | StatConstant typ name value loc =>
      error "Should not occur"
    | StatVariable typ name init loc =>
      error "Should not occur"
    | StatInstantiation typ args name init =>
      error "Should not occur"
    end
  with translate_statement (ctx : DeclCtx) (s : @Statement tags_t) : result (ST.s tags_t) :=
    match s with
    | MkStatement tags stmt typ =>
      translate_statement_pre_t ctx tags stmt
    end
  with translate_block (ctx : DeclCtx) (i : tags_t) (b : @Block tags_t) : result (ST.s tags_t) :=
    match b with
    | BlockEmpty tags =>
      ok (ST.SSkip i)
    | BlockCons statement rest =>
      let* s1 := translate_statement ctx statement in
      let** s2 := translate_block ctx i rest in
      ST.SSeq s1 s2 i
    end.

  Definition translate_state_name (state_name : P4String.t tags_t) :=
    match P4String.str state_name with
    | "accept" => Parser.STAccept
    | "reject" => Parser.STReject
    | "start" => Parser.STStart
    | st => Parser.STName st
    end.

  Print P4Int.

  Fixpoint translate_expression_to_pattern (e : @Expression tags_t) : result (Parser.pat) :=
    let '(MkExpression tags pre_expr typ dir) := e in
    translate_pre_expr tags pre_expr typ dir
  with translate_pre_expr tags pre_expr typ dir : result (Parser.pat) :=
    match pre_expr with
    | ExpDontCare => ok Parser.PATWild
    | ExpRange lo hi =>
      let* lopat := translate_expression_to_pattern lo in
      let** hipat := translate_expression_to_pattern hi in
      Parser.PATRange lopat hipat
    | ExpMask expr mask =>
      let* expr_pat := translate_expression_to_pattern expr in
      let** mask_pat := translate_expression_to_pattern mask in
      Parser.PATMask expr_pat mask_pat
    | ExpInt z =>
      match z.(width_signed) with
      | Some (w, signed) =>
        if signed
        then ok (Parser.PATInt (pos w) z.(value))
        else ok (Parser.PATBit (pos w) z.(value))
      | None => error "Masked ints must have a known width"
      end
    | ExpCast (TypSet (TypBit w)) (MkExpression _ (ExpInt z) _ _) =>
      match z.(width_signed) with
      | Some (_, signed) =>
        if signed
        then ok (Parser.PATInt (pos w) z.(value))
        else ok (Parser.PATBit (pos w) z.(value))
      | _ => error "Masked ints must have a known width"
      end
    | _ => error "unknown set variant"
    end.

  Definition translate_match (m : Match) : result (Parser.pat) :=
    let '(MkMatch tags pre_match typ) := m in
    match pre_match with
    | MatchDontCare => ok Parser.PATWild
    | MatchExpression e => translate_expression_to_pattern e
    end.

  Definition translate_matches (ms : list Match) : result (list Parser.pat) :=
    rred (List.map translate_match ms).

  Definition total_wildcard (patterns : list Parser.pat) : bool :=
    fold_right (fun p acc => match p with
                             | Parser.PATWild => acc
                             | _ => false
                             end)
               true patterns.

  Definition translate_parser_case (pcase : @ParserCase tags_t) : result (either (Parser.e tags_t) (Parser.pat * Parser.e tags_t)) :=
    let '(MkParserCase tags matches next) := pcase in
    let transition := Parser.PGoto (translate_state_name next) tags in
    let** patterns := translate_matches matches in
    if total_wildcard patterns
    then Left transition
    else Right (Parser.PATTuple patterns, transition).

  Definition translate_parser_case_loop pcase acc :=
    let* (def_opt, cases) := acc in
    let** cub_case := translate_parser_case pcase in
    match cub_case with
    | Left x => (Some x, cases)
    | Right y => (def_opt, y::cases)
    end.

  (* TODO ASSUME default is the last element of case list *)
  Definition translate_cases (cases : list (@ParserCase tags_t)) : result (Parser.e tags_t * F.fs Parser.pat (Parser.e tags_t)) :=
    let* (def_opt, cases) := List.fold_right translate_parser_case_loop (ok (None, [])) cases in
    let*~ def := def_opt else "ERROR, could not retrieve default from parser case list" in
    ok (def, cases).

  Fixpoint translate_transition (transition : ParserTransition) : result (Parser.e tags_t) :=
    match transition with
    | ParserDirect tags next =>
      let next_state := translate_state_name next in
      ok (Parser.PGoto next_state tags)
    | ParserSelect tags exprs cases =>
      let* type_expr_list := rred (List.map translate_expression exprs) in
      let expr_list := List.map snd type_expr_list in
      let** (default, cub_cases) := translate_cases cases in
      Parser.PSelect (E.ETuple expr_list tags) default cub_cases tags
    end.

  Definition translate_statements (ctx : DeclCtx) (tags : tags_t) (statements : list Statement) : result (ST.s tags_t) :=
    fold_right (fun s res_acc => let* cub_s := translate_statement ctx s in
                                 let** acc := res_acc in
                                 ST.SSeq cub_s acc tags)
               (ok (ST.SSkip tags))
               statements.

  Fixpoint translate_parser_state (ctx : DeclCtx) (pstate : ParserState) : result (string * Parser.state_block tags_t) :=
    let '(MkParserState tags name statements transition) := pstate in
    let* ss := translate_statements ctx tags statements in
    let** trans := translate_transition transition in
    (P4String.str name, Parser.State ss trans).

  Definition translate_parser_states_inner (ctx : DeclCtx) (p : ParserState) (res_acc : result ((option (Parser.state_block tags_t)) * F.fs string (Parser.state_block tags_t))) :=
    let* (nm, state) := translate_parser_state ctx p in
    let** (start_opt, states) := res_acc in
    if String.eqb nm "start"
    then (Some state, (nm, state)::states)
    else (start_opt, (nm, state)::states).

  Fixpoint translate_parser_states (ctx : DeclCtx) (pstates : list ParserState) : result (option (Parser.state_block tags_t) * F.fs string (Parser.state_block tags_t)) :=
    fold_right (translate_parser_states_inner ctx) (ok (None, [])) pstates.

  Print E.constructor_arg.
  Print E.constructor_args.

  Print P4Type.

  Definition lookup_params_by_ctor_name (name : string) (ctx : DeclCtx) : result (E.constructor_params) :=
    let lookup := find (decl_has_name name) in
    match lookup ctx.(controls) with
    | Some (TopDecl.TPPackage _ cparams _) =>
      ok cparams
    | Some (TopDecl.TPControl name cparams _ _ _ _ _) =>
      error (String.append (String.append "[FIXME] instantiated a control" name) ", not sure what actions to use.")
    | Some _ =>
      error "[FIXME] instantiating controls/Parsers etc is hard"
    | None =>
      error (String.append "[FIXME] instantated a table, function, or action named: " name)
    end.

  Definition translate_instantiation_args (ps : E.constructor_params) (es : list (E.e tags_t)) : result (E.constructor_args tags_t) :=
    let* param_args := zip ps es in
    (* FIXME Something is wrong here. We should be disambiguating here between CAExpr and CAName *)
    List.fold_right (fun '((str, typ), e) (acc_r : result (E.constructor_args tags_t)) =>
                       let* acc := acc_r in
                       match typ, e with
                       | E.CTType _, _ =>
                         ok ((str, E.CAExpr e)::acc)
                       | _, E.EVar _ nm _ =>
                         ok ((str, E.CAName nm)::acc)
                       | _, _ => error "Couldn't translate instaniation properly"
                       end) (ok []) param_args.

  Definition constructor_paramargs (ctor_name: string) (args : list Expression) (ctx : DeclCtx) :=
    let* params := lookup_params_by_ctor_name ctor_name ctx in
    let* cub_typed_args := rred (List.map translate_expression args) in
    let cub_args := List.map snd cub_typed_args in
    translate_instantiation_args params cub_args.

  Definition translate_constructor_param (tags : tags_t) (param : @P4Parameter tags_t) : result (either (string * string) (string * E.ct)) :=
    let '(MkParameter opt dir typ default_arg_id var) := param in
    let v_str := P4String.str var in
    match typ with
    | TypExtern typname =>
      (* Translate to CTExtern or to extern list? *)
      ok(Left (v_str, P4String.str typname))
    | TypControl _ =>
      error "[FIXME] translate control as constructor param"
    | TypParser _ =>
      error "[FIXME] translate parser as constructor param"
    | TypPackage _ _ _  =>
      error "[FIXME] translate package as constructor param"
    | _ =>
      let** cub_type := translate_exp_type tags typ in
      Right (v_str, E.CTType cub_type)
    end.

  Definition partition_constructor_params (tags : tags_t) (params : list (@P4Parameter tags_t)) :=
    fold_right (fun p acc =>
                  let* (extn, ctrlr) := acc in
                  let** param := translate_constructor_param tags p in
                  match param with
                  | Left e => (e :: extn, ctrlr)
                  | Right c => (extn, c::ctrlr)
                  end
               ) (ok ([],[])) params.

  Print E.params.
  Print direction.

  Definition parameter_to_paramarg (tags : tags_t) (parameter : @P4Parameter tags_t) : result (string * paramarg E.t E.t) :=
    let '(MkParameter b dir typ default_arg_id var) := parameter in
    let v_str := P4String.str var in
    let* t := translate_exp_type tags typ in
    let** parg := match dir with
                  | In => ok (PAIn t)
                  | Out => ok (PAOut t)
                  | InOut => ok (PAInOut t)
                  | Directionless =>
                    (* [FIXME] DIRECTIONLESS CANNOT BE WRITTEN, SO CASTING TO IN FOR THE MOMENT*)
                    ok (PAIn t)
                  end
    in
    (v_str, parg).

  Definition parameters_to_params (tags : tags_t) (parameters : list (@P4Parameter tags_t)) : result E.params :=
    rred (List.map (parameter_to_paramarg tags) parameters).

  Print MethodPrototype.

  Print E.arrowT.
  Print arrow.
  Print E.params.
  Definition translate_method (ext_name : P4String.t tags_t) (m : MethodPrototype) : result (string * E.arrowT) :=
    match m with
    | ProtoMethod tags ret name type_args parameters =>
      let* cub_ret := translate_return_type tags ret in
      let* params := parameters_to_params tags parameters in
      let arrowtype := Arrow params cub_ret in
      ok (P4String.str name, arrowtype)
    | ProtoConstructor tags type_args parameters  =>
      let* params := parameters_to_params tags parameters in
      let arrowtype := Arrow params (Some (E.TVar (P4String.str ext_name))) in
      ok (P4String.str ext_name, arrowtype)
    | ProtoAbstractMethod _ _ _ _ _ =>
      error "[FIXME] Dont know how to translate abstract methods"
    end.

  Definition translate_methods (ext_name : P4String.t tags_t) (ms : list MethodPrototype) : result (F.fs string E.arrowT) :=
    rred (List.map (translate_method ext_name) ms).

  Program Fixpoint translate_decl (ctx : DeclCtx)  (d : @Declaration tags_t) {struct d}: result (DeclCtx) :=
    match d with
    | DeclConstant tags typ name value =>
      error "[FIXME] Constant declarations unimplemented"
    | DeclInstantiation tags typ args name init =>
      (* TODO HIGH PRIORITY *)
      let cub_name := P4String.str name in
      let* ctor_p4string := get_string_from_type typ in
      let ctor_name := P4String.str ctor_p4string in
      let* cub_paramargs := constructor_paramargs ctor_name args ctx in
      let d := TopDecl.TPInstantiate ctor_name cub_name cub_paramargs tags in
      match typ with
      | TypPackage _ _ _ => ok (add_package ctx d)
      | _ =>  error "unimplemented declaration type"
      end
    | DeclParser tags name [] params constructor_params [] states =>
        let cub_name := P4String.str name in
        let* (cub_eparams,cub_cparams) := partition_constructor_params tags constructor_params in
        let* cub_params := parameters_to_params tags params in
        let* (start_opt, cub_states) := translate_parser_states ctx states in
        let*~ cub_start := start_opt else "could not find a starting state for the parser" in
        let d := TopDecl.TPParser cub_name cub_cparams cub_eparams cub_params cub_start cub_states tags in
        ok (add_parser ctx d)
    | DeclParser _ _ _ _ _ _ _ => error "got type params or local declarations. these should be gone"
    | DeclControl tags name type_params params constructor_params locals apply_blk =>
      let cub_name := P4String.str name in
      let* (cub_eparams, cub_cparams) := partition_constructor_params tags constructor_params in
      let* cub_params := parameters_to_params tags params in
      let* local_ctx :=
         let loop := fun acc decl => let* ctx := acc in
                                     translate_decl ctx decl in
         fold_left loop locals (ok (empty_declaration_context))
      in
      let cub_body := to_ctrl_decl tags local_ctx in
      let* cub_block := translate_block local_ctx tags apply_blk in
      let d := TopDecl.TPControl cub_name cub_cparams cub_eparams cub_params cub_body cub_block tags in
      ok (add_control ctx d)
    | DeclFunction tags ret name type_params params body =>
      (* let cub_name := P4String.str name in *)
      (* let* cub_signature := error "[FIXME] Translate function signature" in *)
      (* let* cub_body := error "[FIXME] Translate function bodies" in *)
    (* error "[FIXME] implement function declarations" *)
      ok ctx
    | DeclExternFunction tags ret name type_params params =>
    (* error "[FIXME] Extern function declarations unimplemented" *)
      ok ctx
    | DeclVariable tags typ name init =>
    (* error "[FIXME] Variable Declarations unimplemented" *)
      ok ctx
    | DeclValueSet tags typ size name =>
    (* error "[FIXME] Value Set declarations unimplemented" *)
      ok ctx
    | DeclAction tags name data_params ctrl_params body =>
      (* TODO High prio *)
    (* error "[FIXME] Action Declarations unimplemented" *)
      ok ctx
    | DeclTable tags name key actions entires default_action size custom_properties =>
      (* TODO High prio *)
    (* error "[FIXME] Table Declarations unimplemented" *)
      ok ctx
    | DeclHeader tags name fields =>
    (* error "[FIXME] Header Declarations unimplemented" *)
      ok ctx
    | DeclHeaderUnion tags name fields =>
    (* error "[FIXME] Header Union Declarations unimplemented" *)
      ok ctx
    | DeclStruct tags name fields =>
    (* error "[FIXME] Struct Declarations unimplemented" *)
      ok ctx
    | DeclError tags members =>
      (* error "[FIXME] Error Declarations unimplemented" *)
      ok ctx
    | DeclMatchKind tags members =>
    (* error "[FIXME] Match Kind declarations unimplemented" *)
      ok ctx
    | DeclEnum tags name members =>
    (* error "[FIXME] Enum Declarations unimplemented" *)
      ok ctx
    | DeclSerializableEnum tags typ name members =>
    (* error "[FIXME] Serializable Enum declarations unimplemented" *)
      ok ctx
    | DeclExternObject tags name type_params methods =>
      (* error "[FIXME] Extern Object declarations unimplemented" *)
      let str_name := P4String.str name in
      let* cub_methods := translate_methods name methods in
      let d := TopDecl.TPExtern str_name [] cub_methods tags in
      ok (add_extern ctx d)
    | DeclTypeDef tags name typ_or_decl =>
    (* error "[FIXME] Type Definitions unimplemented" *)
      ok ctx
    | DeclNewType tags name typ_or_decl =>
    (* error "[FIXME] Newtypes unimplemented" *)
      ok ctx
    | DeclControlType tags name type_params params =>
    (* error "[FIXME] ControlType declarations unimplemented" *)
      ok ctx
    | DeclParserType tags name type_params params =>
    (* error "[FIXME] ParserType declarations unimplemented" *)
      ok ctx
    | DeclPackageType tags name type_params params =>
      (* TODO HIGH PRIO *)
      (* error "[FIXME] PackageType declaration unimplemented" *)
      ok ctx
  end.

  (* This is redunant with the locals resolution in the previous code, but I
   * can't get it to compile using mutual fixpoints *)
  Definition translate_decls (decls : list (@Declaration tags_t)) : result DeclCtx :=
    let loop := fun acc decl => let* ctx := acc in
                                translate_decl ctx decl in
    fold_left loop decls (ok (empty_declaration_context)).

  Definition seq_opt (i : tags_t) (d : TopDecl.d tags_t) (r : option (TopDecl.d tags_t)) : option (TopDecl.d tags_t) :=
    match r with
    | None => Some d
    | Some rst => Some (TopDecl.TPSeq d rst i)
    end.

  Definition translate_program (tags : tags_t) (p : program) : result (DeclCtx) :=
    let '(Program decls) := SimplExpr.transform_prog tags p in
    translate_decls decls.

End ToP4cub.


Require Import Poulet4.P4defs.
Require Import Poulet4.SimpleNat.

Print Info.

Compute (translate_program Info NoInfo (SimpleNat.prog)).
