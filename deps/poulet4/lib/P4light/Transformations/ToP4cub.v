Set Warnings "-custom-entry-overridden".
Require Export Poulet4.P4light.Syntax.Syntax.
Require Import Poulet4.P4light.Transformations.SimplExpr.
Require Import Poulet4.Utils.Util.ListUtil.
Require Export
        Poulet4.P4cub.Syntax.Syntax
        Poulet4.P4cub.Syntax.Substitution
        Poulet4.P4cub.Syntax.InferMemberTypes
        Poulet4.Utils.Util.Result
        Poulet4.P4cub.BigStep.InstUtil.
Import AST Result Envn.
Import ResultNotations.

Require Import String.
Open Scope string_scope.

Require Import Poulet4.P4light.Transformations.HoistNameless.
Import HoistNameless.

Module ST := Stmt.
Module E := Expr.
Module Sub := Syntax.Substitution.

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
      tables : list (Control.d tags_t);
      actions : list (Control.d tags_t);
      functions : list (TopDecl.d tags_t);
      package_types : F.fs string (list string * list (string * E.ct) * tags_t);
      packages : list (TopDecl.d tags_t);
      externs : list (TopDecl.d tags_t);
      types : list (string * E.t);
    }.

  Definition empty_declaration_context :=
    {| controls := [];
       parsers := [];
       tables := [];
       actions := [];
       functions := [];
       package_types := [];
       packages := [];
       externs := [];
       types := []
    |}.


  Definition add_control (decl : DeclCtx) (c : TopDecl.d tags_t) :=
    {| controls := c::decl.(controls);
       parsers := decl.(parsers);
       tables := decl.(tables);
       actions := decl.(actions);
       functions := decl.(functions);
       package_types := decl.(package_types);
       packages := decl.(packages);
       externs := decl.(externs);
       types := decl.(types)
    |}.

  Definition add_parser (decl : DeclCtx) (p : TopDecl.d tags_t) :=
    {| controls := decl.(controls);
       parsers := p::decl.(parsers);
       tables := decl.(tables);
       actions := decl.(actions);
       functions := decl.(functions);
       package_types := decl.(package_types);
       packages := decl.(packages);
       externs := decl.(externs);
       types := decl.(types)
    |}.

  Definition add_package (decl : DeclCtx) (p : TopDecl.d tags_t) :=
    {| controls := decl.(controls);
       parsers := decl.(parsers);
       tables := decl.(tables);
       actions := decl.(actions);
       functions := decl.(functions);
       package_types := decl.(package_types);
       packages := p::decl.(packages);
       externs := decl.(externs);
       types := decl.(types);
    |}.

  Definition add_package_type (decl : DeclCtx) pt :=
    {| controls := decl.(controls);
       parsers := decl.(parsers);
       tables := decl.(tables);
       actions := decl.(actions);
       functions := decl.(functions);
       package_types := pt::decl.(package_types);
       packages := decl.(packages);
       externs := decl.(externs);
       types := decl.(types);
    |}.

  Definition add_extern (decl : DeclCtx) (e : TopDecl.d tags_t) :=
    {| controls := decl.(controls);
       parsers := decl.(parsers);
       tables := decl.(tables);
       actions := decl.(actions);
       functions := decl.(functions);
       package_types := decl.(package_types);
       packages := decl.(packages);
       externs := e::decl.(externs);
       types := decl.(types);
    |}.

  Definition add_table (decl : DeclCtx) (t : Control.d tags_t) :=
    {| controls := decl.(controls);
       parsers := decl.(parsers);
       tables := t::decl.(tables);
       actions := decl.(actions);
       functions := decl.(functions);
       packages := decl.(packages);
       package_types := decl.(package_types);
       externs := decl.(externs);
       types := decl.(types);
    |}.

  Definition add_action (decl : DeclCtx) (a : Control.d tags_t) :=
    {| controls := decl.(controls);
       parsers := decl.(parsers);
       tables := decl.(tables);
       actions := a::decl.(actions);
       functions := decl.(functions);
       package_types := decl.(package_types);
       packages := decl.(packages);
       externs := decl.(externs);
       types := decl.(types);
    |}.

  Definition add_type (decl : DeclCtx) (typvar : string) (typ : E.t) :=
    {| controls := decl.(controls);
       parsers := decl.(parsers);
       tables := decl.(tables);
       actions := decl.(actions);
       functions := decl.(functions);
       package_types := decl.(package_types);
       packages := decl.(packages);
       externs := decl.(externs);
       types := (typvar, typ) :: decl.(types);
    |}.

  Fixpoint tsub_ts (σ : Env.t string E.t) (ts : F.fs string E.t) :=
    let tsub_t := Sub.tsub_t in
    match ts with
    | [] => []
    | (x,t)::ts' =>
      match Env.find x σ with
      | None => (x, tsub_t σ t) :: tsub_ts σ ts'
      | Some _ =>
        let σ' := Env.remove x σ in
        let t' := tsub_t σ' t in
        let σ'' := Env.bind x t' σ' in
        (x, t') :: tsub_ts σ'' ts'
      end
    end.

  Definition subst_type (decl : DeclCtx) (typvar : string) (type : E.t) : DeclCtx :=
    let σ := [(typvar, type)] in
    let tsub_ds := List.map (Sub.tsub_d σ) in
    let tsub_Cds := List.map (Sub.tsub_Cd σ) in
    let tsub_pts := F.map (fun '(cub_type_params, cub_params, tags) =>
                                let σ' := Sub.remove_types σ cub_type_params in
                                let cub_params' := F.map (Sub.tsub_cparam σ') cub_params in
                                (cub_type_params, cub_params', tags)
                             ) in
    {| controls := tsub_ds decl.(controls);
       parsers := tsub_ds decl.(parsers);
       tables := tsub_Cds decl.(tables);
       actions := tsub_Cds decl.(actions);
       functions := tsub_ds decl.(functions);
       package_types := tsub_pts decl.(package_types);
       packages := tsub_ds decl.(packages);
       externs := tsub_ds decl.(externs);
       types := (typvar, type) :: tsub_ts σ decl.(types);
    |}.

  Definition to_decl (tags : tags_t) (decls : DeclCtx) : TopDecl.d tags_t :=
    let decls := List.concat [decls.(controls); decls.(parsers); decls.(functions); decls.(packages); decls.(externs)] in
    let dummy_type := {| paramargs := []; rtrns := None |} in
    let dummy_function := TopDecl.TPFunction "$DUMMY" [] dummy_type (ST.SSkip tags) tags in
    List.fold_right (fun d1 d2 => TopDecl.TPSeq d1 d2 tags)
                    dummy_function
                    decls.

  Fixpoint of_cdecl (decls : DeclCtx) (d : Control.d tags_t) :=
    match d with
    | Control.CDAction _ _ _ _ =>
      add_action decls d
    | Control.CDTable _ _ _ =>
      add_table decls d
    | Control.CDSeq d1 d2 i =>
      let decls1 := of_cdecl decls d1 in
      of_cdecl decls1 d2
    end.

  Definition extend (hi_prio lo_prio: DeclCtx) : DeclCtx :=
    let combine {A : Type} (f : DeclCtx -> list A) := List.app (f hi_prio) (f lo_prio) in
    {| controls := combine controls;
       parsers := combine parsers;
       tables := combine tables;
       actions := combine actions;
       functions := combine functions;
       package_types := combine package_types;
       packages := combine packages;
       externs := combine externs;
       types := List.app hi_prio.(types) lo_prio.(types);
    |}.

  Definition to_ctrl_decl tags (c: DeclCtx) : Control.d tags_t :=
    List.fold_right (fun d1 d2 => Control.CDSeq d1 d2 tags)
                    (Control.CDAction "$DUMMY_ACTION" [] (ST.SSkip tags) (tags))
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
    (*| TopDecl.TPPackage package_name _ _ _ => matches package_name*)
    | TopDecl.TPSeq _ _ _ =>
      (* Should Not Occur *)
      false
    end.

  Definition cdecl_has_name (name : string) (d : Control.d tags_t) :=
    let matches := String.eqb name in
    match d with
    | Control.CDAction action_name _ _ _ => matches action_name
    | Control.CDTable table_name _ _ => matches table_name
    | Control.CDSeq _ _ _ =>
      (* Should Not Occur *)
      false
    end.

  Definition is_member (name : string) (l : list (TopDecl.d tags_t)) : bool :=
    match find (decl_has_name name) l with
    | None => false
    | Some _ => true
    end.


  Definition get_augment_from_name (ctx : DeclCtx) (name : string) :=
    let name_is_in := is_member name in
    let pt_name_is_in := List.find ((String.eqb name) ∘ fst) in
    if name_is_in ctx.(controls) then
      ok (add_control ctx)
    else if name_is_in ctx.(parsers) then
           ok(add_parser ctx)
         else if pt_name_is_in ctx.(package_types) then
                ok (add_package ctx)
              else if name_is_in ctx.(externs) then
                     ok (add_extern ctx)
                   else
                     error ("couldn't identify augment for" ++ name).

  Definition lookup_instantiatable (ctx : DeclCtx) (name : string) :=
    find (decl_has_name name) (ctx.(controls) ++ ctx.(parsers) ++ ctx.(packages) ++ ctx.(externs)).

  Definition find_control (ctx : DeclCtx) (name : string) :=
    find (decl_has_name name) (ctx.(controls)).

  Definition find_parser (ctx : DeclCtx) (name : string) :=
    find (decl_has_name name) (ctx.(parsers)).

  Definition find_table (ctx : DeclCtx) (name : string) :=
    find (cdecl_has_name name) (ctx.(tables)).

  Definition find_action (ctx : DeclCtx) (name : string) :=
    find (cdecl_has_name name) (ctx.(actions)).

  Definition find_function (ctx : DeclCtx) (name : string) :=
    find (decl_has_name name) (ctx.(functions)).

  Definition find_package (ctx : DeclCtx) (name : string) :=
    find (decl_has_name name) (ctx.(packages)).

  Definition find_extern (ctx : DeclCtx) (name : string) :=
    find (decl_has_name name) (ctx.(externs)).

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
    E.TBit (Npos (pos (width_of_enum members))).


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
      ok E.TBool
    | TypInteger =>
      (* TODO This should be added to P4cub, but can only be a value; enforced by the type system *)
      error "[FIXME] P4cub doesnt support Integers"
    | TypInt w => ok (E.TInt (posN w))
    | TypBit w => ok (E.TBit w)
    | TypVarBit w =>
      error "[FIXME] Compile to fixed-width"
    | TypArray typ size =>
      match typ with
      | TypHeader fields =>
        let+ cub_fields := translate_fields fields in
        E.THeaderStack cub_fields (posN size)
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
    | TypTypeName name => ok (E.TVar (P4String.str name))
    | TypNewType name typ =>
      let+ typ' := translate_exp_type i typ in
      typ'
    | TypControl c =>
      (* FIXME Solve control type issue*)
      ok (E.TVar "$DUMMY")
    | TypParser c =>
      (* FIXME solve control type issue*)
      ok (E.TVar "$DUMMY")
    | TypExtern name =>
      (* error "An extern is not an expression type" *)
      ok (E.TVar ("$DUMMY"++ (P4String.str name)))
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
    | TypBool => error "cannot get  from boolean"
    | TypString => error "cannot get type name from string"
    | TypInteger => error "cannot get type name from Integer"
    | TypInt _ => error "cannot get type name from int "
    | TypBit _ => error "cannot get type name from bit"
    | TypVarBit _ => error "cannot get type name from varbit"
    | TypArray _ _ => error "cannot get type name from array"
    | TypTuple _ => error "cannot get type name from tuple"
    | TypList _ => error "cannot get type name from list"
    | TypRecord _ => error "cannot get type name from list"
    | TypSet _ => error "cannot get type name from set"
    | TypError => error "cannot get type name from error"
    | TypMatchKind => error "cannot get type name from matchkind"
    | TypVoid => error "cannot get type name from void"
    | TypHeader _ => error "cannot get type name from Header"
    | TypHeaderUnion _ => error "cannot get type name from Header Union"
    | TypStruct _ => error "cannot get type name from struct"
    | TypEnum _ _ _ => error "cannot get type name from enum"
    | TypTypeName str => ok str
    | TypNewType str _ => ok str
    | TypControl c => error "[FIXME] get name from control type"
    | TypParser c => error "[FIXME] get name from parser type"
    | TypExtern str => ok str
    | TypFunction _ => error "cannot get name from function type"
    | TypAction _ _ => error "cannot get name from action type"
    | TypTable s => ok s
    | TypPackage _ _ _ => error "cannot get name from package type"
    | TypSpecializedType t _ => get_string_from_type t
    | TypConstructor _ _ _ _ => error "cannot get name from typconstructor"
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
          ok (E.EInt (posN w) z.(value) z.(tags))
        else
          ok (E.EBit w z.(value) z.(tags))
      | None => error "[FIXME] integer didnt have a width."
      end
    | ExpString _ =>
      (* [FIXME] strings need to be compiled away *)
      ok (E.EBool false i)
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
      let* type := translate_exp_type i (get_type_of_expr array) in
      match type with
      | E.THeaderStack fs _ =>
        let+ index := realize_array_index index in
        E.EHeaderStackAccess fs stck index i
      | _ =>
        error "translateed type of array access is not a headerstack type"
      end
    | ExpBitStringAccess bits lo hi =>
      let* typ := translate_exp_type i (get_type_of_expr bits) in
      let+ e := translate_expression bits in
      E.ESlice e (posN hi) (posN lo) i
    | ExpList values =>
      let f := fun v res_rst =>
                 let* cub_v := translate_expression v in
                 let+ rst := res_rst in
                 cub_v :: rst in
      let+ cub_values := fold_right f (ok []) values in
      E.ETuple cub_values i
    | ExpRecord entries =>
      let f := fun kv res_rst =>
                 let '(nm,expr) := kv in
                 let* type := translate_exp_type i (get_type_of_expr expr) in
                 let* expr := translate_expression expr in
                 let+ rst := res_rst in
                 (P4String.str nm, expr) :: rst in
      let+ cub_entries := fold_right f (ok []) entries  in
      E.EStruct cub_entries i
    | ExpUnaryOp op arg =>
      let eop := translate_op_uni op in
      let* typ := translate_exp_type i (get_type_of_expr arg) in
      let+ earg := translate_expression arg in
      E.EUop typ eop earg i
    | ExpBinaryOp op (e1,e2) =>
      let* typ' := translate_exp_type i typ in
      let* e1' := translate_expression e1 in
      let* e2' := translate_expression e2 in
      let+ eop := translate_op_bin op in
      E.EBop typ' eop e1' e2' i
    | ExpCast typ expr =>
      let* expr' := translate_expression expr in
      let+ typ' := translate_exp_type i typ in
      E.ECast typ' expr' i
    | ExpTypeMember _ name =>
      match typ with
      | TypEnum _ _ members =>
        let w := width_of_enum members in
        let+ n := get_enum_id members name in
        E.EBit (Npos (pos w)) (BinIntDef.Z.of_nat n) i
      | _ =>
        error "Type Error. Type Member had non-enum type"
      end

    | ExpErrorMember str =>
      ok (E.EError (Some (P4String.str str)) i)
    | ExpExpressionMember expr name =>
      let* cub_type := translate_exp_type i (get_type_of_expr expr) in
      let+ cub_expr := translate_expression expr in
      E.EExprMember cub_type (P4String.str name) cub_expr i
    | ExpTernary cond tru fls =>
      error "Ternary expressions should have been hoisted by a previous pass"
    | ExpFunctionCall func type_args args =>
      error "Function Calls should have been hoisted by a previous pass"
    | ExpNamelessInstantiation typ args =>
      error "Nameless Intantiations should have been hoisted by a previous pass"
    | ExpDontCare =>
      error "[FIXME] These are actually patterns (unimplemented)"
    (* | ExpMask expr mask => *)
    (*   error "[FIXME] actually patterns (unimplemented)" *)
    (* | ExpRange lo hi => *)
    (*   error "[FIXME] actually patterns (unimplemented)" *)
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

  Definition apply_arg_to_param (x : string * paramarg E.t E.t * E.e tags_t) (acc : result (F.fs string (paramarg (E.e tags_t) (E.e tags_t)))) : result (F.fs string (paramarg (E.e tags_t) (E.e tags_t))) :=
    let '(name, typ, exp) := x in
    let+ fs := acc in
    match typ with
    | PAIn t => (name, PAIn (exp)) :: fs
    | PAOut t => (name, PAOut (exp)) :: fs
    | PAInOut t => (name, PAInOut (exp)) :: fs
    | PADirLess t => (name, PADirLess (exp))::fs
    end.


  Definition apply_args_to_params (params : F.fs string (paramarg E.t E.t)) (args : list (E.e tags_t)) : result (F.fs string (paramarg (E.e tags_t) (E.e tags_t))) :=
    let~ params_args := zip params args over "zipping param args failed" in
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


  Definition translate_apply tags callee : result (ST.s tags_t) :=
    let typ := get_type_of_expr callee in
    match typ with
    | TypControl (MkControlType type_params parameters) =>
      error "[FIXME] translate control apply calls"
    | TypTable _ =>
      let+ callee_name := get_name callee in
      ST.SInvoke (P4String.str callee_name) tags
    | TypParser _ =>
      error "[FIXME] translate parser apply calls"
    | _ =>
      error "Error got a type that cannot be applied."
    end.

  Definition translate_set_validity tags v callee :=
    let+ hdr := translate_expression callee in
    ST.SSetValidity hdr v tags.

  Definition translate_is_valid tags callee retvar :=
    let* hdr := translate_expression callee in
    match retvar with
    | None => error "IsValid has no return value"
    | Some rv =>
      ok (ST.SAssign (E.EVar E.TBool rv tags)
                     (E.EUop E.TBool E.IsValid hdr tags)
                     tags)
    end.

  Definition translate_extern_string (tags : tags_t) (ctx : DeclCtx) (extern_str f_str : string) args:=
    let extern_decl :=  find (decl_has_name extern_str) ctx.(externs) in
    match extern_decl with
    | None => error (String.append "ERROR expected an extern, but got " extern_str)
    | Some (TopDecl.TPExtern extn_name tparams cparams methods i) =>
      let called_method := find (fun '(nm, _) => String.eqb nm f_str) methods in
      match called_method with
      | None =>
        error (append "Couldn't find " (append (append extern_str ".") f_str))
      | Some (_, (targs, ar)) =>
        let params := paramargs ar in
        let arg_list := optionlist_to_list args in
        let* cub_args := rred (List.map translate_expression arg_list) in
        let+ paramargs := apply_args_to_params params cub_args in
        (* TODO Currently assuming method calls return None*)
        let typ : E.arrowE tags_t := {|paramargs:=paramargs; rtrns:=None|} in
        ST.SExternMethodCall extern_str f_str [] typ tags
      end
    | Some _ =>
      error "Invariant Violated. Declaration Context Extern list contained something other than an extern."
    end.


  Definition translate_expression_member_call
             (args : list (option (@Expression tags_t)))
             (tags : tags_t)
             (ctx : DeclCtx)
             (callee : Expression)
             (ret_var : option string)
             (f : P4String.t tags_t) : result (ST.s tags_t) :=
    let f_str := P4String.str f in
    if f_str =? "apply" then
      translate_apply tags callee
    else if f_str =? "setInvalid" then
      translate_set_validity tags false callee
    else if f_str =? "setValid" then
      translate_set_validity tags true callee
    else if f_str =? "isValid" then
      translate_is_valid tags callee ret_var
    else
      match get_type_of_expr callee with
      | TypTypeName extern_obj =>
        translate_extern_string tags ctx (P4String.str extern_obj) f_str args
      | _ =>
        error (String.append "ERROR: :: Cannot translate non-externs member functions that aren't `apply`s: " f_str)
      end.

  Definition translate_function_application (tags : tags_t) (fname : P4String.t tags_t) ret_var ret type_args parameters args : result (ST.s tags_t) :=
    let* cub_args := rred (List.map translate_expression (optionlist_to_list args)) in
    let* params := parameters_to_params tags parameters in
    let* paramargs := apply_args_to_params params cub_args in
    let* cub_type_params := rred (List.map (translate_exp_type tags) type_args) in
    let+ ret_typ := translate_return_type tags ret in
    let cub_ret := option_map (fun t => (E.EVar t ret_var tags)) ret_typ in
    let cub_ar := {| paramargs:=paramargs; rtrns:=cub_ret |} in
    ST.SFunCall (P4String.str fname) cub_type_params cub_ar tags.

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
          Some (translate_function_application tags n ret_var ret type_args parameters args)
        | _ => Some (error "A name, applied like a method call, must be a function or extern type; I got something else")
        end
      | _ => Some (error "ERROR :: Cannot handle this kind of expression")
      end
    | _ =>
      None
    end.

  Definition get_label_index (tenum : list (P4String.t tags_t))  (label : P4String.t tags_t) : result Z :=
    match ListUtil.findi (P4String.equivb label) tenum with
    | Some i =>
      ok (BinInt.Z.of_nat i)
    | None =>
      error ("[ERROR] Couldnt find label [" ++ P4String.str label ++ "] in enum")
    end.

  Definition get_enum_type (expression : @Expression tags_t) : result (list (P4String.t tags_t)) :=
    let '(MkExpression tags pre_expr type dir) := expression in
    match type with
    | TypEnum _ _ variants =>
      ok variants
    | _ =>
      error "could not get enum type from non-enum variant"
    end.

  Fixpoint translate_statement_switch_case ctx (match_expr : E.e tags_t) (bits : N) (tenum : list (P4String.t tags_t)) (acc : (option (E.e tags_t)) * (ST.s tags_t -> ST.s tags_t)) (ssw : @StatementSwitchCase tags_t) : result ((option (E.e tags_t)) * (ST.s tags_t -> ST.s tags_t)) :=
    (* break apart the accumulation into the aggregated condition and the aggregated if-then continuation *)
    let '(cond_opt, ifthen) := acc in
    (* Force the agggregated conditional to be a boolean *)
    let acc_cond := fun tags => SyntaxUtil.force (E.EBool false tags) cond_opt in
    (* Build the case match by building the label index check and or-ing the aggregated conditional *)
    let case_match := fun tags label =>
                        let+ val := get_label_index tenum label in
                        let mtch := E.EBop E.TBool E.Eq match_expr (E.EBit bits val tags) tags in
                        E.EBop E.TBool E.Or (acc_cond tags) mtch tags in
    (* check the cases *)
    match ssw with
    | StatSwCaseAction tags label block =>
      (* This case discharges the built up conditions. so the first part of the pair is always None *)
      match label with
      | StatSwLabName tags labname =>
        let* cond := case_match tags labname in
        let* st := translate_block ctx tags block in
        let else__ifthen : ST.s tags_t -> ST.s tags_t := fun else_ => ST.SConditional cond st else_ tags in
        (* The continuation is still "open" *)
        ok (None, ifthen ∘ else__ifthen)
      | StatSwLabDefault tags =>
        let* else_ := translate_block ctx tags block in
        (* in the default case, we throw away the argument because we have the else case, *)
        (* if anything comes after, its dead code *)
        ok (None, fun (_ : ST.s tags_t) => (ifthen else_ : ST.s tags_t))
      end
    | StatSwCaseFallThrough tags label =>
      match label with
      | StatSwLabDefault _ =>
        error "[ERROR] Cannot have default label as a fall-through case in a switch statement"
      | StatSwLabName tags labname =>
        (* This case doesn't change the continuation but accumulates a condition *)
        (* Note that the accumulation happens automagically in the [case_match function]*)
        let+ cond := case_match tags labname in
        (Some cond, (ifthen : ST.s tags_t -> ST.s tags_t))
      end
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
          translate_function_application tags n ("$RETVAR_" ++ (P4String.str n)) ret type_args parameters args
        | _ => error "A name, applied like a method call, must be a function or extern type; I got something else"
        end
      | _ => error "ERROR :: Cannot handle this kind of expression"
      end
    | StatAssignment lhs rhs =>
      let* cub_lhs := translate_expression lhs in
      let+ cub_rhs := translate_expression rhs in
      ST.SAssign cub_lhs cub_rhs i
    | StatDirectApplication typ func_typ args =>
      error "[FIXME] (StatDirectApplication) Need to translate into instantiation and then application"
    | StatConditional cond tru fls_opt =>
      let* cub_cond := translate_expression cond in
      let* cub_tru := translate_statement ctx tru in
      let+ cub_fls := match fls_opt with
                       | None => ok (ST.SSkip i)
                       | Some fls => translate_statement ctx fls
                       end in
      ST.SConditional cub_cond cub_tru cub_fls i
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
        ST.SReturn (Some cub_expr) i
      | None =>
        ok (ST.SReturn None i)
      end
    | StatSwitch expr cases =>
      let* tenum := get_enum_type expr in
      let bits := BinNat.N.of_nat (PeanoNat.Nat.log2_up (List.length tenum)) in
      let* expr := translate_expression expr in
      let+ (_, cases_as_ifs) :=
          List.fold_left (fun acc_res switch_case =>
                            let* acc := acc_res in
                            translate_statement_switch_case ctx expr bits tenum acc switch_case
                         ) cases (ok (None, fun x => x))

      in
      cases_as_ifs (ST.SSkip i)
    | StatConstant typ name value loc =>
      error "Constant Statement should not occur"
    | StatVariable typ name init loc =>
      let* t := translate_exp_type i typ in
      let vname := P4String.str name in
      let decl := ST.SVardecl vname (inl t) i in
      match init with
      | None =>
        ok decl
      | Some e =>
        match function_call_init ctx e vname with
        | None =>  (** check whether e is a function call *)
          let+ cub_e := translate_expression e in
          let var := E.EVar t vname i in
          let assign := ST.SAssign var cub_e i in
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
    let s := P4String.str state_name in
    if String.eqb s "accept"
    then Parser.STAccept
    else if String.eqb s "reject"
         then Parser.STReject
         else if String.eqb s "start"
              then Parser.STStart
              else Parser.STName s.

  Fixpoint translate_expression_to_pattern (e : @Expression tags_t) : result (Parser.pat) :=
    let '(MkExpression tags pre_expr typ dir) := e in
    translate_pre_expr tags pre_expr typ dir
  with translate_pre_expr tags pre_expr typ dir : result (Parser.pat) :=
    match pre_expr with
    | ExpDontCare => ok Parser.PATWild
    (* | ExpRange lo hi => *)
    (*   let* lopat := translate_expression_to_pattern lo in *)
    (*   let+ hipat := translate_expression_to_pattern hi in *)
    (*   Parser.PATRange lopat hipat *)
    (* | ExpMask expr mask => *)
    (*   let* expr_pat := translate_expression_to_pattern expr in *)
    (*   let+ mask_pat := translate_expression_to_pattern mask in *)
    (*   Parser.PATMask expr_pat mask_pat *)
    | ExpInt z =>
      match z.(width_signed) with
      | Some (w, signed) =>
        if signed
        then ok (Parser.PATInt (posN w) z.(value))
        else ok (Parser.PATBit w z.(value))
      | None => error "Masked ints must have a known width"
      end
    | ExpCast (TypSet (TypBit w)) (MkExpression _ (ExpInt z) _ _) =>
      match z.(width_signed) with
      | Some (_, signed) =>
        if signed
        then ok (Parser.PATInt (posN w) z.(value))
        else ok (Parser.PATBit w z.(value))
      | _ => error "ints must have a known width"
      end
    | _ => error "unknown set variant"
    end.

  Definition translate_match (m : Match) : result (Parser.pat) :=
    let '(MkMatch tags pre_match typ) := m in
    match pre_match with
    | MatchDontCare => ok Parser.PATWild
    | MatchMask e mask =>
      let* p_e := translate_expression_to_pattern e in
      let+ p_m := translate_expression_to_pattern mask in
      Parser.PATMask p_e p_m
    | MatchRange lo hi =>
      let* p_lo := translate_expression_to_pattern lo in
      let+ p_hi := translate_expression_to_pattern hi in
      Parser.PATMask p_lo p_hi
    | MatchCast typ m =>
      translate_pre_expr tags (ExpCast typ m) typ Directionless
    end.

  Definition translate_matches (ms : list Match) : result (list Parser.pat) :=
    rred (List.map translate_match ms).

  Definition total_wildcard (patterns : list Parser.pat) : bool :=
    fold_right (fun p acc => match p with
                             | Parser.PATWild => acc
                             | _ => false
                             end)
               true patterns.

  Definition
    translate_parser_case
    (pcase : @ParserCase tags_t)
    : result (Parser.e tags_t + (Parser.pat * Parser.e tags_t)) :=
    let '(MkParserCase tags matches next) := pcase in
    let transition := Parser.PGoto (translate_state_name next) tags in
    let+ patterns := translate_matches matches in
    if total_wildcard patterns
    then inl transition
    else inr (Parser.PATTuple patterns, transition).

  Definition translate_parser_case_loop pcase acc :=
    let* (def_opt, cases) := acc in
    let+ cub_case := translate_parser_case pcase in
    match cub_case with
    | inl x => (Some x, cases)
    | inr y => (def_opt, y::cases)
    end.

  (* TODO ASSUME default is the last element of case list *)
  Definition translate_cases (cases : list (@ParserCase tags_t)) : result (Parser.e tags_t * F.fs Parser.pat (Parser.e tags_t)) :=
    let* (def_opt, cases) := List.fold_right translate_parser_case_loop (ok (None, [])) cases in
    let*~ def := def_opt else "ERROR, could not retrieve default from parser case list" in
    ok (def, cases).

  Definition translate_transition (transition : ParserTransition) : result (Parser.e tags_t) :=
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

  Definition translate_parser_state (ctx : DeclCtx) (pstate : ParserState) : result (string * Parser.state_block tags_t) :=
    let '(MkParserState tags name statements transition) := pstate in
    let* ss := translate_statements ctx tags statements in
    let+ trans := translate_transition transition in
    let parser_state := {| Parser.stmt := ss; Parser.trans := trans |} in
    (P4String.str name, parser_state).

  Definition translate_parser_states_inner (ctx : DeclCtx) (p : ParserState) (res_acc : result ((option (Parser.state_block tags_t)) * F.fs string (Parser.state_block tags_t))) :=
    let* (nm, state) := translate_parser_state ctx p in
    let+ (start_opt, states) := res_acc in
    if String.eqb nm "start"
    then (Some state, (nm, state)::states)
    else (start_opt, (nm, state)::states).

  Definition translate_parser_states (ctx : DeclCtx) (pstates : list ParserState) : result (option (Parser.state_block tags_t) * F.fs string (Parser.state_block tags_t)) :=
    fold_right (translate_parser_states_inner ctx) (ok (None, [])) pstates.

  Definition lookup_params_by_ctor_name (name : string) (ctx : DeclCtx) : result (E.constructor_params) :=
    match lookup_instantiatable ctx name with
    | Some (TopDecl.TPParser _ cparams _ _ _ _ _)  =>
      ok cparams
    | Some (TopDecl.TPControl _ cparams _ _ _ _ _) =>
      ok cparams
    | Some (TopDecl.TPExtern _ _ cparams _ _) =>
      ok cparams
    | Some (_) =>
      error ("Dont kow how to get constructors for " ++ name)
    | None =>
      match List.find (String.eqb name ∘ fst) ctx.(package_types) with
      | Some (_, (_ , cparams, _)) =>
        ok cparams
      | None =>
          error (String.append "Error, couldn't find: " name)
      end
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
    let~ param_args := zip ps es over ("zipping instantiation args failed. there were " ++ string_of_nat (List.length ps) ++ "params and " ++ string_of_nat (List.length es) ++ "args") in
    (* FIXME Something is wrong here. We should be disambiguating here between CAExpr and CAName *)
    List.fold_right (fun '((str, typ), e) (acc_r : result (E.constructor_args tags_t)) =>
                       let* acc := acc_r in
                       match e with
                       | E.EVar (E.TVar s) nm _ =>
                         if String.eqb s "$DUMMY"
                         then ok ((str, E.CAName nm)::acc)
                         else ok ((str, E.CAExpr e)::acc)
                       | _ =>
                         ok ((str, E.CAExpr e)::acc)
                       end) (ok []) param_args.

  Definition constructor_paramargs (ctor_name: string) (args : list Expression) (ctx : DeclCtx) :=
    let* params := lookup_params_by_ctor_name ctor_name ctx in
    let* cub_args := rred (List.map translate_constructor_arg_expression args) in
    let~ inst := translate_instantiation_args params cub_args over "instantiation failed looking up " ++ ctor_name ++ "params: " ++ string_of_nat (List.length params) in
    ok inst.


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
    | TypSpecializedType (TypTypeName ( name)) _   =>
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
  Definition
    translate_constructor_parameter_either
    (tags : tags_t) (parameter : @P4Parameter tags_t)
    : result (string * string + string * E.ct) :=
    let '(MkParameter opt dir typ default_arg_id var) := parameter in
    let v_str := P4String.str var in
    match typ with
    | TypExtern typname =>
      (* Translate to CTExtern or to extern list? *)
      ok (inl (v_str, P4String.str typname))
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
                  | inl e => (e :: extn, ctrlr)
                  | inr c => (extn, c::ctrlr)
                  end
               ) (ok ([],[])) params.

  Definition translate_method (ext_name : P4String.t tags_t) (m : MethodPrototype) : result (string * (list string * E.arrowT)) :=
    match m with
    | ProtoMethod tags ret name type_args parameters =>
      let* cub_ret := translate_return_type tags ret in
      let* params := parameters_to_params tags parameters in
      let arrowtype := {|paramargs:=params; rtrns := cub_ret |} in
      ok (P4String.str name, ([], arrowtype))
    | ProtoConstructor tags type_args parameters  =>
      let* params := parameters_to_params tags parameters in
      let arrowtype := {|paramargs:= params; rtrns:= (Some (E.TVar (P4String.str ext_name))) |} in
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

  Definition translate_matchkind (matchkind : P4String.t tags_t) : result E.matchkind :=
    let mk_str := P4String.str matchkind in
    if String.eqb mk_str "lpm"
    then ok E.MKLpm
    else if String.eqb mk_str "ternary"
         then ok E.MKTernary
         else if String.eqb mk_str "exact"
              then ok E.MKExact
              else error ("Matchkind not supported by P4cub: " ++ mk_str).

  Definition translate_key (key : TableKey) : result (E.e tags_t * E.matchkind) :=
    let '(MkTableKey tags key_exp matchkind) := key in
    let* e := translate_expression key_exp in
    let+ mk := translate_matchkind matchkind in
    (e, mk).

  Definition translate_keys_loop (key : TableKey) (acc : result (list (E.e tags_t * E.matchkind))) : result (list (E.e tags_t * E.matchkind)) :=
    let* cub_key := translate_key key in
    let+ cub_keys := acc in
    cub_key :: cub_keys.

  Definition translate_keys (keys : list TableKey) : result (list (E.e tags_t * E.matchkind)) :=
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

  Definition get_cub_type_args (i:tags_t) typ :=
    match typ with
    | TypSpecializedType _ args =>
      rred (List.map (translate_exp_type i) args)
    | _ =>
      ok []
    end.


  Definition translate_actions (actions : list TableActionRef) : result (list string) :=
    List.fold_right translate_actions_loop (ok []) actions.


  Definition translate_decl_fields (fields : list DeclarationField) : result (F.fs string E.t) :=
    rred (List.map (fun '(MkDeclarationField i typ name) =>
                let+ t := translate_exp_type i typ in
                (P4String.str name, t)
             ) fields).


  Definition extract_type (p : paramarg E.t E.t) : E.t :=
    match p with
    | PAIn t | PAOut t | PAInOut t | PADirLess t => t
    end.

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
      let* type_args := get_cub_type_args tags typ in
      let d := TopDecl.TPInstantiate ctor_name cub_name type_args cub_paramargs tags in
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
    | DeclExternFunction tags ret name type_params parameters =>
      let* cub_ret := translate_return_type tags ret in
      let* params := parameters_to_params tags parameters in
      let arrowtype := {|paramargs:=params; rtrns:=cub_ret|} in
      let method := (P4String.str name, ([], arrowtype)) in
      (* TODO come up with better naming scheme for externs *)
      let d := TopDecl.TPExtern "_" [] [] [method] tags in
      ok (add_extern ctx d)
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
      let a := Control.CDAction cub_name cub_signature cub_body tags in
      add_action ctx a
    | DeclTable tags name keys actions entries default_action size custom_properties =>
      (* TODO High prio *)
      let name := P4String.str name in
      let* cub_keys := translate_keys keys in
      let+ cub_actions := translate_actions actions in
      let table := {| Control.table_key := cub_keys; Control.table_actions:= cub_actions|} in
      let t := Control.CDTable name table tags in
      add_action ctx t
    | DeclHeader tags name fields =>
      (* error "[FIXME] Header Declarations unimplemented" *)
      let+ fs := translate_decl_fields fields in
      let t := E.THeader fs in
      add_type ctx (P4String.str name) t
    | DeclHeaderUnion tags name fields =>
    (* error "[FIXME] Header Union Declarations unimplemented" *)
      ok ctx
    | DeclStruct tags name fields =>
      let+ fs := translate_decl_fields fields in
      let t := E.TStruct fs in
      add_type ctx (P4String.str name) t
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
      let+ (cub_methods : F.fs string (list string * Expr.arrowT)) := translate_methods name methods in
      let cparams := match List.find (String.eqb str_name ∘ fst) cub_methods with
                     | None => []
                     | Some (_, (_, ar)) => F.map (E.CTType ∘ extract_type) ar.(paramargs)
                     end in
      let cub_type_params := List.map P4String.str type_params in
      let d := TopDecl.TPExtern str_name cub_type_params cparams cub_methods tags in
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
      let p :=  (cub_name, (cub_type_params, cub_params, tags)) in
      add_package_type ctx p
      (* error "[FIXME] P4light inlining step necessary" *)
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

  Definition inline_types (decls : DeclCtx) :=
    fold_left (fun acc '(x,t) => subst_type acc x t) (decls.(types)) decls.

  Definition infer_member_types (decl : DeclCtx) :=
    let infer_ds := List.map InferMemberTypes.inf_d in
    let infer_Cds := List.map InferMemberTypes.inf_Cd in
    let infer_pts := F.map (fun '(tparams,cparams, t) =>
                                 (tparams, F.map InferMemberTypes.inf_cparam cparams, t)) in
    {| controls := infer_ds decl.(controls);
       parsers := infer_ds decl.(parsers);
       tables := infer_Cds decl.(tables);
       actions := infer_Cds decl.(actions);
       functions := infer_ds decl.(functions);
       package_types := infer_pts decl.(package_types);
       packages := infer_ds decl.(packages);
       externs := infer_ds decl.(externs);
       types := decl.(types);
    |}.

  Definition translate_program (tags : tags_t) (p : program) : result (DeclCtx) :=
    let* '(Program decls) := preprocess tags p in
    let+ cub_decls := translate_decls decls in
    infer_member_types (inline_types cub_decls).

End ToP4cub.
