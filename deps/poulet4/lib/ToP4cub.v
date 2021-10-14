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

Require Import Poulet4.HoistNameless.
Import HoistNameless.

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
      tables : list (TopDecl.C.d tags_t);
      actions : list (TopDecl.C.d tags_t);
      functions : list (TopDecl.d tags_t);
      packages : list (TopDecl.d tags_t);
      externs : list (TopDecl.d tags_t);
    }.

  Definition empty_declaration_context :=
    {| controls := [];
       parsers := [];
       tables := [];
       actions := [];
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

  Definition add_table (decl : DeclCtx) (t : TopDecl.C.d tags_t) :=
    {| controls := decl.(controls);
       parsers := decl.(parsers);
       tables := t::decl.(tables);
       actions := decl.(actions);
       functions := decl.(functions);
       packages := decl.(packages);
       externs := decl.(externs);
    |}.

  Definition add_action (decl : DeclCtx) (a : TopDecl.C.d tags_t) :=
    {| controls := decl.(controls);
       parsers := decl.(parsers);
       tables := decl.(tables);
       actions := a::decl.(actions);
       functions := decl.(functions);
       packages := decl.(packages);
       externs := decl.(externs);
    |}.
  
  Definition to_decl (tags : tags_t) (decls : DeclCtx) : TopDecl.d tags_t :=
    let decls := List.concat [decls.(controls); decls.(parsers); decls.(functions); decls.(packages); decls.(externs)] in
    List.fold_right (fun d1 d2 => TopDecl.TPSeq d1 d2 tags)
                    (TopDecl.TPFunction "$DUMMY" [] (Arrow [] None) (ST.SSkip tags) tags)
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


  Definition to_ctrl_decl tags (c: DeclCtx) : TopDecl.C.d tags_t :=
    List.fold_right (fun d1 d2 => TopDecl.C.CDSeq d1 d2 tags)
                    (TopDecl.C.CDAction "$DUMMY_ACTION" [] (ST.SSkip tags) (tags))
                    (List.app c.(actions) c.(tables)).

  Definition find {A : Type} (f : A -> bool) : list A -> option A :=
    List.fold_right (fun x found => match found with | None => if f x then Some x else None | Some _ => found end) None.

  Definition decl_has_name (name : string) (d : TopDecl.d tags_t) :=
    let matches := String.eqb name in
    match d with
    | TopDecl.TPInstantiate _ instance_name _ _ _ => matches instance_name
    | TopDecl.TPExtern extern_name _ _ _ _ => matches extern_name
    | TopDecl.TPControl control_name _ _ _ _ _ _ => matches control_name
    | TopDecl.TPParser parser_name _ _ _ _ _ _ => matches parser_name
    | TopDecl.TPFunction function_name _ _ _ _ => matches function_name
    | TopDecl.TPPackage package_name _ _ _ => matches package_name
    | TopDecl.TPSeq _ _ _ =>
      (* Should Not Occur *)
      false
    end.

  Definition is_member (name : string) (l : list (TopDecl.d tags_t)) : bool :=
    match find (decl_has_name name) l with
    | None => false
    | Some _ => true
    end.

  Definition get_augment_from_name (ctx : DeclCtx) (name : string) :=
    let name_is := is_member name in
    if name_is ctx.(controls) then
      ok (add_control ctx)
    else if name_is ctx.(parsers) then
           ok(add_parser ctx)
         else if name_is ctx.(packages) then
                ok (add_package ctx)
              else if name_is ctx.(externs) then
                     ok (add_extern ctx)
                   else
                     error ("couldn't identify augment for" ++ name).


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
    let+ hd := hd_res in
    hd :: l.

  Definition width_of_enum (members : list (P4String.t tags_t)) :=
    let num_members := List.length members in
    PeanoNat.Nat.max 1 (PeanoNat.Nat.log2_up num_members).

  Definition cub_type_of_enum (members : list (P4String.t tags_t)) :=
    E.TBit (pos (width_of_enum members)).

  Program Fixpoint translate_exp_type (i : tags_t) (typ : @P4Type tags_t) {struct typ} : result E.t :=
    let translate_fields :=
        fold_right (fun '(name,typ) res_rst =>
                      let* cub_typ := translate_exp_type i typ in
                      let+ rst := res_rst in
                      (P4String.str name, cub_typ) :: rst ) (ok [])
    in
    match typ with
    | TypBool => ok E.TBool
    | TypString =>
      (* TODO Strings should only occur as arguments to externs.  We should add these to P4cub *)
      error "String is not a valid p4cub type"
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
        let+ cub_fields := translate_fields fields in
        E.THeaderStack cub_fields (pos size)
      | _ => error "Typeerror:: Arrays must contain Headers"
      end
    | TypTuple types =>
      (* TODO ensure are cast-able *)
      let+ cub_types := fold_right (cons_res ∘ (translate_exp_type i)) (ok []) types in
      E.TTuple cub_types
    | TypList types =>
      let+ cub_types := fold_right (cons_res ∘ (translate_exp_type i)) (ok []) types in
      E.TTuple cub_types
    | TypRecord fields =>
      let+ cub_fields := translate_fields fields in
      E.TStruct cub_fields
    | TypSet elt_type =>
      (* Shows up in typechecking a select *)
      error "A set is not an expression type"
    | TypError => ok E.TError
    | TypMatchKind => ok E.TMatchKind
    | TypVoid => error "[FIXME] void is not the type of any expression literal"
    | TypHeader fields =>
      let+ fields' := translate_fields fields in
      E.THeader fields'
    | TypHeaderUnion _ =>
      error "[FIXME] Header Unions need to be compiled away or added to p4cub"
    | TypStruct fields =>
      let+ fields' := translate_fields fields in
      E.TStruct fields'
    | TypEnum name typ members =>
      ok (cub_type_of_enum members)
    | TypTypeName name =>
      match name with
      | BareName nm =>
        ok (E.TVar (P4String.str nm))
      | QualifiedName _ _ =>
        error "Unsure how to handle qualified names"
      end
    | TypNewType name typ =>
      let+ typ' := translate_exp_type i typ in
      typ'
    | TypControl c =>
      (* FIXME Solve control type issue*)
      ok (E.TVar "$CONTROL_DUMMY")
    | TypParser c =>
      (* FIXME solve control type issue*)
      ok (E.TVar "$PARSER_DUMMY")
    | TypExtern name =>
      (* error "An extern is not an expression type" *)
      ok (E.TVar ("$EXTERN_DUMMY_"++ (P4String.str name)))
    | TypFunction fn =>
      error "A function is not an expression"
    | TypAction _ _ =>
      error "An action is not an expression"
    | TypTable _ =>
      error "A table is not an expression"
    | TypPackage _ _ _ =>
      error "A package is not an expression"
    | TypSpecializedType base args =>
      (* FIXME handle specialized types in a monomorphising pass *)
      translate_exp_type i base
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

  Definition get_type_of_expr (e : Expression) : @P4Type tags_t :=
    let '(MkExpression _ _ typ _) := e in
    typ.
  Fixpoint get_string_from_type (t : P4Type) : result (P4String.t tags_t) :=
    match t with
    | TypTypeName (BareName str) => ok str
    | TypSpecializedType t [] => get_string_from_type t
    | TypControl c => error "[FIXME] get name from control type"
    | TypParser c => error "[FIXME] get name from parser type"
    | _ => error "Don't know how to get constructor from arbitrary type"
    end.

  Definition inst_name_from_type (g : NameGen.t) (t : P4Type) : result (NameGen.t * P4String.t tags_t) :=
    let+ type_name := get_string_from_type t in
    let (g, name) := NameGen.fresh g (P4String.str type_name) in
    let p4str_name := {| P4String.tags := P4String.tags type_name;
                         P4String.str := name
                      |} in
    (g, p4str_name).


  Fixpoint get_enum_id_aux (idx : nat) (member_list : list (P4String.t tags_t)) (member : P4String.t tags_t) : result nat :=
    match member_list with
    | [] => error  ("Could not find member" ++ P4String.str member ++ "in member list")
    | m::ms =>
      if P4String.str member =? P4String.str m
      then ok idx
      else get_enum_id_aux (idx + 1) ms member
    end.

  Definition get_enum_id := get_enum_id_aux 0.

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
      error "[FIXME] strings need to be compiled away"
    | ExpName name loc =>
      match name with
      | BareName str =>
        let+ cub_type := translate_exp_type i typ in
        E.EVar cub_type (P4String.str str) i
      | QualifiedName namespaces name =>
        error "Qualified names should be eliminated"
      end
    | ExpArrayAccess array index =>
      let* stck := translate_expression array in
      let+ index := realize_array_index index in
      E.EHeaderStackAccess stck index i
    | ExpBitStringAccess bits lo hi =>
      let* typ := translate_exp_type i (get_type_of_expr bits) in
      let+ e := translate_expression bits in
      E.ESlice e typ (posN hi) (posN lo) i
    | ExpList values =>
      let f := fun v res_rst =>
                 let* cub_v := translate_expression v in
                 let+ rst := res_rst in
                 cub_v :: rst in
      let+ cub_values := fold_right f (ok []) values in
      E.ETuple cub_values i
    | ExpRecord entries =>
      let f := fun kv res_rst =>
                 let '(MkKeyValue i nm expr) := kv in
                 let* type := translate_exp_type i (get_type_of_expr expr) in
                 let* expr := translate_expression expr in
                 let+ rst := res_rst in
                 (P4String.str nm, (type,expr)) :: rst in
      let+ cub_entries := fold_right f (ok []) entries  in
      E.EStruct cub_entries i
    | ExpUnaryOp op arg =>
      let eop := translate_op_uni op in
      let* typ := translate_exp_type i (get_type_of_expr arg) in
      let+ earg := translate_expression arg in
      E.EUop eop typ earg i
    | ExpBinaryOp op (e1,e2) =>
      let* t1 := translate_exp_type i (get_type_of_expr e1) in
      let* t2 := translate_exp_type i (get_type_of_expr e2) in
      let* e1' := translate_expression e1 in
      let* e2' := translate_expression e2 in
      let+ eop := translate_op_bin op in
      E.EBop eop t1 t2 e1' e2' i
    | ExpCast typ expr =>
      let* expr' := translate_expression expr in
      let+ typ' := translate_exp_type i typ in
      E.ECast typ' expr' i
    | ExpTypeMember _ name =>
      match typ with
      | TypEnum _ _ members =>
        let w := width_of_enum members in
        let+ n := get_enum_id members name in
        E.EBit (pos w) (BinIntDef.Z.of_nat n) i
      | _ =>
        error "Type Error. Type Member had non-enum type"
      end

    | ExpErrorMember str =>
      ok (E.EError (Some (P4String.str str)) i)
    | ExpExpressionMember expr name =>
      let* cub_type := translate_exp_type i (get_type_of_expr expr) in
      let+ cub_expr := translate_expression expr in
      E.EExprMember (P4String.str name) cub_type cub_expr i
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
  with translate_expression (e : @Expression tags_t) : result (E.e tags_t) :=
    match e with
    | MkExpression tags expr typ dir =>
      translate_expression_pre_t tags typ expr
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
      let+ x := translate_exp_type tags ret in
      Some x
    end.

  Definition apply_arg_to_param (x : string * paramarg E.t E.t * (E.t * E.e tags_t)) (acc : result (F.fs string (paramarg (E.t * E.e tags_t) (E.t * E.e tags_t)))) : result (F.fs string (paramarg (E.t * E.e tags_t) (E.t * E.e tags_t))) :=
    let '(name, typ, (_, exp)) := x in
    let+ fs := acc in
    match typ with
    | PAIn t => (name, PAIn (t, exp)) :: fs
    | PAOut t => (name, PAOut (t, exp)) :: fs
    | PAInOut t => (name, PAInOut (t,exp)) :: fs
    | PADirLess t => (name, PADirLess (t,exp))::fs
    end.


  Definition apply_args_to_params (params : F.fs string (paramarg E.t E.t)) (args : list (E.t * E.e tags_t)) : result (F.fs string (paramarg (E.t * E.e tags_t) (E.t * E.e tags_t))) :=
    let* params_args := zip params args in
    fold_right apply_arg_to_param (ok []) params_args.

  Definition parameter_to_paramarg (tags : tags_t) (parameter : @P4Parameter tags_t) : result (string * paramarg E.t E.t) :=
    let '(MkParameter b dir typ default_arg_id var) := parameter in
    let v_str := P4String.str var in
    let* t := translate_exp_type tags typ in
    let+ parg := match dir with
                  | In => ok (PAIn t)
                  | Out => ok (PAOut t)
                  | InOut => ok (PAInOut t)
                  | Directionless => ok (PADirLess t)
                  end
    in
    (v_str, parg).

  Definition parameters_to_params (tags : tags_t) (parameters : list (@P4Parameter tags_t)) : result E.params :=
    rred (List.map (parameter_to_paramarg tags) parameters).


  Definition translate_expression_and_type tags e :=
    let* cub_t := translate_exp_type tags (get_type_of_expr e) in
    let+ cub_e := translate_expression e in
    (cub_t, cub_e).

  Definition translate_expression_member_call
             (args : list (option (@Expression tags_t)))
             (tags : tags_t)
             (ctx : DeclCtx)
             (callee : Expression)
             (ret_var : option string)
             (f : P4String.t tags_t) : result (ST.s tags_t) :=
    let f_str := P4String.str f in
    let typ := get_type_of_expr callee in
    if f_str =? "apply" then
      match typ with
      | TypControl (MkControlType type_params parameters) =>
        error "[FIXME] translate control apply calls"
      | TypTable _ =>
        let* callee_name := get_name callee in
        ok (ST.SInvoke (P4String.str callee_name) tags)
      | TypParser _ =>
        error "[FIXME] translate parser apply calls"
      | _ =>
        error "Error got a type that cannot be applied."
      end
    else if f_str =? "setInvalid" then
      let+ hdr := translate_expression callee in
      ST.SSetValidity hdr ST.Invalid tags
    else if f_str =? "setValid" then
      let+ hdr := translate_expression callee in
      ST.SSetValidity hdr ST.Valid tags
    else if f_str =? "isValid" then
      let* hdr := translate_expression callee in
      match ret_var with
      | None => error "IsValid has no return value"
      | Some rv =>
        ok (ST.SAssign E.TBool
                       (E.EVar E.TBool rv tags)
                       (E.EUop E.IsValid E.TBool hdr tags)
                       tags)
      end
    else
      match typ with
      | TypTypeName (BareName extern_obj) =>
        let extern_str := (P4String.str extern_obj : string) in
        let extern_decl :=  find (decl_has_name extern_str) ctx.(externs) in
        match extern_decl with
        | None => error (String.append "ERROR expected an extern, but got " extern_str)
        | Some (TopDecl.TPExtern extn_name tparams cparams methods i) =>
          let called_method := find (fun '(nm, _) => String.eqb nm f_str) methods in
          match called_method with
          | None =>
            error (append "Couldn't find " (append (append extern_str ".") f_str))
          | Some (_, (targs, Arrow params _)) =>
            let arg_list := optionlist_to_list args in
            let* cub_args := rred (List.map (translate_expression_and_type tags) arg_list) in
            let+ paramargs := apply_args_to_params params cub_args in
            (* TODO Currently assuming method calls return None*)
            let typ : E.arrowE tags_t := Arrow paramargs None in
            ST.SExternMethodCall (P4String.str extern_obj) f_str [] typ tags

          end
        | Some _ =>
          error "Invariant Violated. Declaration Context Extern list contained something other than an extern."
        end
      | _ =>
        error (String.append "ERROR: :: Cannot translate non-externs member functions that aren't `apply`s: " f_str)
      end.

  Definition function_call_init (ctx : DeclCtx) (e : Expression) (ret_var : string) : option (result (ST.s tags_t)) :=
    let '(MkExpression tags expr typ dir) := e in
    match expr with
    | ExpFunctionCall func type_args args =>
      let '(MkExpression tags func_pre typ dir) := func in
      match func_pre with
      | ExpExpressionMember callee f =>
        Some (translate_expression_member_call args tags ctx callee (Some ret_var) f)
      | ExpName (BareName n) loc =>
        match typ with
        | TypFunction (MkFunctionType type_params parameters kind ret) =>
          Some (let* cub_args := rred (List.map (translate_expression_and_type tags) (optionlist_to_list args)) in
                let* params := parameters_to_params tags parameters in
                let* paramargs := apply_args_to_params params cub_args in
                let+ ret_typ := translate_return_type tags ret in
                let cub_ret := option_map (fun t => (t, E.EVar t ret_var tags)) ret_typ in
                ST.SFunCall (P4String.str n) [] (Arrow paramargs cub_ret) tags)
        | _ => Some (error "A name, applied like a method call, must be a function or extern type; I got something else")
        end
      | _ => Some (error "ERROR :: Cannot handle this kind of expression")
      end
    | _ =>
      None
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
        translate_expression_member_call args tags ctx callee None f
      | ExpName (BareName n) loc =>
        match typ with
        | TypFunction (MkFunctionType type_params parameters kind ret) =>
          let* cub_args := rred (List.map (translate_expression_and_type i) (optionlist_to_list args)) in
          let* params := parameters_to_params tags parameters in
          let* paramargs := apply_args_to_params params cub_args in
          let+ ret_typ := translate_return_type tags ret in
          let cub_ret := option_map (fun t => (t, E.EVar t ("$RETVAR_" ++ (P4String.str n)) tags)) ret_typ in
          ST.SFunCall (P4String.str n) [] (Arrow paramargs cub_ret) tags
        | _ => error "A name, applied like a method call, must be a function or extern type; I got something else"
        end
      | _ => error "ERROR :: Cannot handle this kind of expression"
      end
    | StatAssignment lhs rhs =>
      let* (cub_ltyp, cub_lhs) := translate_expression_and_type i lhs in
      let+ cub_rhs := translate_expression rhs in
      ST.SAssign cub_ltyp cub_lhs cub_rhs i
    | StatDirectApplication typ args =>
      error "[FIXME] (StatDirectApplication) Need to translate into instantiation and then application"
    | StatConditional cond tru fls_opt =>
      let* (cub_type, cub_cond) := translate_expression_and_type i cond in
      let* cub_tru := translate_statement ctx tru in
      let+ cub_fls := match fls_opt with
                       | None => ok (ST.SSkip i)
                       | Some fls => translate_statement ctx fls
                       end in
      ST.SConditional cub_type cub_cond cub_tru cub_fls i
    | StatBlock block =>
      let+ sblck := translate_block ctx i block in
      ST.SBlock sblck
    | StatExit =>
      ok (ST.SExit i)
    | StatEmpty =>
      ok (ST.SSkip i)
    | StatReturn expr_opt =>
      match expr_opt with
      | Some e =>
        let+ (cub_typ, cub_expr) := translate_expression_and_type i e in
        ST.SReturnFruit cub_typ cub_expr i
      | None =>
        ok (ST.SReturnVoid i)
      end
    | StatSwitch expr cases =>
      error "[FIXME] switch statement not implemented"
    | StatConstant typ name value loc =>
      error "Constant Statement should not occur"
    | StatVariable typ name init loc =>
      let* t := translate_exp_type i typ in
      let vname := P4String.str name in
      let decl := ST.SVardecl t vname i in
      match init with
      | None =>
        ok decl
      | Some e =>
        match function_call_init ctx e vname with
        | None =>  (** check whether e is a function call *)
          let+ cub_e := translate_expression e in
          let var := E.EVar t vname i in
          let assign := ST.SAssign t var cub_e i in
          ST.SSeq decl assign i
        | Some s =>
          let+ s := s in
          ST.SSeq decl s i
        end
      end
    | StatInstantiation typ args name init =>
      error "Instantiation statement should not occur"
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
      let+ s2 := translate_block ctx i rest in
      ST.SSeq s1 s2 i
    end.

  Definition translate_state_name (state_name : P4String.t tags_t) :=
    match P4String.str state_name with
    | "accept" => Parser.STAccept
    | "reject" => Parser.STReject
    | "start" => Parser.STStart
    | st => Parser.STName st
    end.

  Fixpoint translate_expression_to_pattern (e : @Expression tags_t) : result (Parser.pat) :=
    let '(MkExpression tags pre_expr typ dir) := e in
    translate_pre_expr tags pre_expr typ dir
  with translate_pre_expr tags pre_expr typ dir : result (Parser.pat) :=
    match pre_expr with
    | ExpDontCare => ok Parser.PATWild
    | ExpRange lo hi =>
      let* lopat := translate_expression_to_pattern lo in
      let+ hipat := translate_expression_to_pattern hi in
      Parser.PATRange lopat hipat
    | ExpMask expr mask =>
      let* expr_pat := translate_expression_to_pattern expr in
      let+ mask_pat := translate_expression_to_pattern mask in
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
    let+ patterns := translate_matches matches in
    if total_wildcard patterns
    then Left transition
    else Right (Parser.PATTuple patterns, transition).

  Definition translate_parser_case_loop pcase acc :=
    let* (def_opt, cases) := acc in
    let+ cub_case := translate_parser_case pcase in
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
      let* type_expr_list := rred (List.map (translate_expression_and_type tags) exprs) in
      let expr_list := List.map snd type_expr_list in
      let+ (default, cub_cases) := translate_cases cases in
      Parser.PSelect (E.ETuple expr_list tags) default cub_cases tags
    end.

  Definition translate_statements (ctx : DeclCtx) (tags : tags_t) (statements : list Statement) : result (ST.s tags_t) :=
    fold_right (fun s res_acc => let* cub_s := translate_statement ctx s in
                                 let+ acc := res_acc in
                                 ST.SSeq cub_s acc tags)
               (ok (ST.SSkip tags))
               statements.

  Fixpoint translate_parser_state (ctx : DeclCtx) (pstate : ParserState) : result (string * Parser.state_block tags_t) :=
    let '(MkParserState tags name statements transition) := pstate in
    let* ss := translate_statements ctx tags statements in
    let+ trans := translate_transition transition in
    (P4String.str name, Parser.State ss trans).

  Definition translate_parser_states_inner (ctx : DeclCtx) (p : ParserState) (res_acc : result ((option (Parser.state_block tags_t)) * F.fs string (Parser.state_block tags_t))) :=
    let* (nm, state) := translate_parser_state ctx p in
    let+ (start_opt, states) := res_acc in
    if String.eqb nm "start"
    then (Some state, (nm, state)::states)
    else (start_opt, (nm, state)::states).

  Fixpoint translate_parser_states (ctx : DeclCtx) (pstates : list ParserState) : result (option (Parser.state_block tags_t) * F.fs string (Parser.state_block tags_t)) :=
    fold_right (translate_parser_states_inner ctx) (ok (None, [])) pstates.

  Print TopDecl.d.

  Definition lookup_params_by_ctor_name (name : string) (ctx : DeclCtx) : result (E.constructor_params) :=
    match lookup_instantiatable ctx name with
    | Some (TopDecl.TPPackage _ _ cparams _) =>
      ok cparams
    | Some (TopDecl.TPParser _ cparams _ _ _ _ _)  =>
      ok cparams
    | Some (TopDecl.TPControl _ cparams _ _ _ _ _) =>
      ok cparams
    | Some (TopDecl.TPExtern _ _ cparams _ _) =>
      ok cparams
    | Some (_) =>
      error ("Dont kow how to get constructors for " ++ name)
    | None =>
      error (String.append "Error, couldn't find: " name)
    end.

  Definition translate_constructor_arg_expression (arg : @Expression tags_t) : result (E.e tags_t) :=
    match translate_expression arg with
    | Ok _ e =>
      (* try to reuse translation*)
      ok e
    | Error _ msg =>
      (* if the naive translation fails, try something better  *)
      let '(MkExpression tags expr typ dir) := arg in
      match expr with
      | _ =>
        error ("naive expression translation for constructor arguments failed with message: " ++ msg)
      end
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
                       | _, _ => error "DONT KNOW HOW TO translate instaniations"
                       end) (ok []) param_args.

  Definition constructor_paramargs (ctor_name: string) (args : list Expression) (ctx : DeclCtx) :=
    let* params := lookup_params_by_ctor_name ctor_name ctx in
    let* cub_args := rred (List.map translate_constructor_arg_expression args) in
    translate_instantiation_args params cub_args.

  Print P4Type.


  Definition translate_constructor_parameter (tags : tags_t) (parameter : @P4Parameter tags_t) : result (string * E.ct) :=
    let '(MkParameter opt dir typ default_arg_id var) := parameter in
    let v_str := P4String.str var in
    match typ with
    | TypExtern typname =>
      ok(v_str, E.CTExtern (P4String.str typname))
    | TypControl _ =>
      error "[FIXME] translate control as constructor param"
    | TypParser _ =>
      error "[FIXME] translate parser as constructor param"
    | TypPackage _ _ _  =>
      error "[FIXME] translate package as constructor param"
    | TypSpecializedType (TypTypeName (BareName name)) _   =>
      ok (v_str, E.CTType (E.TVar (P4String.str name)))
    | _ =>
      error "[FIXME] dont kjnow how to translate type to constructor type"
    end.

  Definition translate_constructor_parameters (tags : tags_t) :=
    fold_right (fun p acc =>
                  let* params := acc in
                  let+ param := translate_constructor_parameter tags p in
                  param :: params
               ) (ok []).

  (* TODO write in terms of translate_constructor_parameter *)
  Definition translate_constructor_parameter_either (tags : tags_t) (parameter : @P4Parameter tags_t) : result (either (string * string) (string * E.ct)) :=
    let '(MkParameter opt dir typ default_arg_id var) := parameter in
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
      error "[FIXME] dont kjnow how to translate type to constructor type"
      (* let+ cub_type := translate_exp_type tags typ in *)
      (* Right (v_str, E.CTType cub_type) *)
    end.

  Definition partition_constructor_params (tags : tags_t) (params : list (@P4Parameter tags_t)) :=
    fold_right (fun p acc =>
                  let* (extn, ctrlr) := acc in
                  let+ param := translate_constructor_parameter_either tags p in
                  match param with
                  | Left e => (e :: extn, ctrlr)
                  | Right c => (extn, c::ctrlr)
                  end
               ) (ok ([],[])) params.

  Definition translate_method (ext_name : P4String.t tags_t) (m : MethodPrototype) : result (string * (list string * E.arrowT)) :=
    match m with
    | ProtoMethod tags ret name type_args parameters =>
      let* cub_ret := translate_return_type tags ret in
      let* params := parameters_to_params tags parameters in
      let arrowtype := Arrow params cub_ret in
      ok (P4String.str name, ([], arrowtype))
    | ProtoConstructor tags type_args parameters  =>
      let* params := parameters_to_params tags parameters in
      let arrowtype := Arrow params (Some (E.TVar (P4String.str ext_name))) in
      ok (P4String.str ext_name, ([], arrowtype))
    | ProtoAbstractMethod _ _ _ _ _ =>
      error "[FIXME] Dont know how to translate abstract methods"
    end.

  Definition translate_methods (ext_name : P4String.t tags_t) (ms : list MethodPrototype) : result (F.fs string (list string * E.arrowT)) :=
    rred (List.map (translate_method ext_name) ms).

  Definition translate_action_params tags data_params ctrl_params :=
    let* cub_data_params := parameters_to_params tags data_params in
    let+ cub_ctrl_params := parameters_to_params tags ctrl_params in
    (* TODO ensure ctrl params are directionless? *)
    List.app cub_data_params cub_ctrl_params.

  Print TableKey.

  Definition translate_matchkind (matchkind : P4String.t tags_t) : result E.matchkind :=
    let mk_str := P4String.str matchkind in
    match mk_str with
    | "lpm" => ok E.MKLpm
    | "ternary" => ok E.MKTernary
    | "exact" => ok E.MKExact
    | _ => error ("Matchkind not supported by P4cub: " ++ mk_str)
    end.

  Definition translate_key (key : TableKey) : result (E.t * E.e tags_t * E.matchkind) :=
    let '(MkTableKey tags key_exp matchkind) := key in
    let* (t, e) := translate_expression_and_type tags key_exp in
    let+ mk := translate_matchkind matchkind in
    (t, e, mk).

  Definition translate_keys_loop (key : TableKey) (acc : result (list (E.t * E.e tags_t * E.matchkind))) : result (list (E.t * E.e tags_t * E.matchkind)) :=
    let* cub_key := translate_key key in
    let+ cub_keys := acc in
    cub_key :: cub_keys.

  Definition translate_keys (keys : list TableKey) : result (list (E.t * E.e tags_t * E.matchkind)) :=
    List.fold_right translate_keys_loop (ok []) keys.

  Definition translate_action (action : TableActionRef) : result string :=
    let '(MkTableActionRef tags pre_action typ) := action in
    let '(MkTablePreActionRef name args) := pre_action in
    match name with
    | BareName act_name => ok (@P4String.str tags_t act_name)
    | QualifiedName _ _ =>
      error "don't know how to deal with quantified names"
    end.

  Definition translate_actions_loop (action : TableActionRef) (acc : result (list string)) : result (list string) :=
    let* cub_act := translate_action action in
    let+ cub_acts := acc in
    cub_act :: cub_acts.

  Definition translate_actions (actions : list TableActionRef) : result (list string) :=
    List.fold_right translate_actions_loop (ok []) actions.

  Fixpoint translate_decl (ctx : DeclCtx)  (d : @Declaration tags_t) {struct d}: result (DeclCtx) :=
    match d with
    | DeclConstant tags typ name value =>
      error "[FIXME] Constant declarations unimplemented"
    | DeclInstantiation tags typ args name init =>
      (* TODO HIGH PRIORITY *)
      let cub_name := P4String.str name in
      let* ctor_p4string := get_string_from_type typ in
      let ctor_name := P4String.str ctor_p4string in
      let* cub_paramargs := constructor_paramargs ctor_name args ctx in
      let d := TopDecl.TPInstantiate ctor_name cub_name [] cub_paramargs tags in
      let+ add_to_context := get_augment_from_name ctx ctor_name in
      add_to_context d
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
      let+ cub_block := translate_block (extend local_ctx ctx) tags apply_blk in
      let d := TopDecl.TPControl cub_name cub_cparams cub_eparams cub_params cub_body cub_block tags in
      add_control ctx d
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
      let cub_name := P4String.str name in
      let* cub_signature := translate_action_params tags data_params ctrl_params in
      let+ cub_body := translate_block ctx tags body in
      let a := TopDecl.C.CDAction cub_name cub_signature cub_body tags in
      add_action ctx a
    | DeclTable tags name keys actions entries default_action size custom_properties =>
      (* TODO High prio *)
      let name := P4String.str name in
      let* cub_keys := translate_keys keys in
      let+ cub_actions := translate_actions actions in
      let table := TopDecl.C.Table cub_keys cub_actions in
      let t := TopDecl.C.CDTable name table tags in
      add_action ctx t
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
      let+ cub_methods := translate_methods name methods in
      let d := TopDecl.TPExtern str_name [] [] cub_methods tags in
      add_extern ctx d
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
    | DeclPackageType tags name type_params parameters =>
      let cub_name := P4String.str name in
      let cub_type_params := List.map (@P4String.str tags_t) type_params in
      let+ cub_params := translate_constructor_parameters tags parameters in
      let p := TopDecl.TPPackage cub_name cub_type_params cub_params tags in
      add_package ctx p
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

  Definition preprocess (tags : tags_t)  :=
    (hoist_nameless_instantiations tags_t)
      ∘ (SimplExpr.transform_prog tags).

  Definition translate_program (tags : tags_t) (p : program) : result (DeclCtx) :=
    let* '(Program decls) := preprocess tags p in
    translate_decls decls.

End ToP4cub.


Require Import Poulet4.P4defs.
Require Import Poulet4.SimpleNat.

Import SimpleNat.

Definition test := Program
                     [decl'1
                      ; packet_in
                      ; packet_out
                      ; verify'check'toSignal
                      ; NoAction
                      ; decl'2
                      ; decl'3
                      ; standard_metadata_t
                      ; CounterType
                      ; MeterType
                      ; counter
                      ; direct_counter
                      ; meter
                      ; direct_meter
                      ; register
                      ; action_profile
                      ; random'result'lo'hi
                      ; digest'receiver'data
                      ; HashAlgorithm
                      ; mark_to_drop
                      ; mark_to_drop'standard_metadata
                      ; hash'result'algo'base'data'max
                      ; action_selector
                      ; CloneType
                      ; Checksum16
                      ; verify_checksum'condition'data'checksum'algo
                      ; update_checksum'condition'data'checksum'algo
                      ; verify_checksum_with_payload'condition'data'checksum'algo
                      ; update_checksum_with_payload'condition'data'checksum'algo
                      ; resubmit'data
                      ; recirculate'data
                      ; clone'type'session
                      ; clone3'type'session'data
                      ; truncate'length
                      ; assert'check
                      ; assume'check
                      ; log_msg'msg
                      ; log_msg'msg'data
                      ; Parser
                      ; VerifyChecksum
                      ; Ingress
                      ; Egress
                      ; ComputeChecksum
                      ; Deparser
                      ; V1Switch
                      ; intrinsic_metadata_t
                      ; meta_t
                      ; cpu_header_t
                      ; ethernet_t
                      ; ipv4_t
                      ; tcp_t
                      ; metadata
                      ; headers
                      ; ParserImpl
                      ; egress
                      ; ingress
                      ; DeparserImpl
                      ; verifyChecksum
                      ; computeChecksum
                      ; main
                     ].

Compute (translate_program Info NoInfo test).

Compute (preprocess Info NoInfo test).

Compute (translate_program Info NoInfo (SimpleNat.prog)).
