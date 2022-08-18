Require Import String.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
From Poulet4 Require Import
     P4light.Transformations.SimplExpr
     P4light.Transformations.InlineTypeDecl
     Utils.Util.ListUtil.
From Poulet4 Require Export
     P4light.Syntax.Syntax
     P4cub.Syntax.Syntax
     P4cub.Syntax.Substitution
     P4cub.Syntax.InferMemberTypes
     P4cub.Syntax.HeaderStack
     Monads.Result.
Import AST Result Envn ResultNotations.
From Coq Require Import ZArith.BinInt Arith.PeanoNat.
Open Scope string_scope.

Require Import Poulet4.P4light.Transformations.HoistNameless.
Import HoistNameless.

Module ST := Stmt.
Module E := Expr.
Module Sub := Syntax.Substitution.

Definition swap {A B C : Type} (f : A -> B -> C) (b : B) (a : A) : C := f a b.

Definition append {A : Type} (l : list A) (l' : list A) : list A :=
  match l' with
  | [] => l
  | _  => List.rev_append (List.rev' l) l'
  end.

Definition fold_right {A B : Type} (f : B -> A -> A) (a0 : A) (bs : list B ) :=
  List.fold_left (fun a b => f b a) (List.rev' bs) a0.

Definition find {A : Type} (f : A -> bool) : list A -> option A :=
  fold_right (fun x found => match found with | None => if f x then Some x else None | Some _ => found end) None.

Definition optionlist_to_list {A : Type} : list (option A) -> list A :=
  fold_right (fun x_opt acc => match x_opt with
                            | None => acc
                            | Some x => x::acc
                            end) [].

Definition
  list_of_opts_map
  {A B : Type} (f : A -> B) (opt_as : list (option A)) :=
  List.map (option_map f) opt_as.

Fixpoint
  commute_result_optlist
  {A : Type} (l : list (option (result A)))
  : result (list (option A)) :=
  match l with
  | [] => ok []
  | o :: l =>
      let* l := commute_result_optlist l in
      match o with
      | None =>
          ok (None :: l)
      | Some a_res =>
          let+ a := a_res in
          Some a :: l
      end
  end.

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
    mkDeclCtx {
        controls :  list (TopDecl.d);
        parsers : list (TopDecl.d);
        tables : list (Control.d);
        actions : list (Control.d);
        functions : list (TopDecl.d);
        package_types : Field.fs string (TopDecl.constructor_params * list E.t);
        packages : list (TopDecl.d);
        externs : list (TopDecl.d);
        types : list (string * E.t);
      }.
  
  Global Instance etaDeclCtx : Settable _ :=
    settable! mkDeclCtx
    < controls ; parsers; tables ; actions
  ; functions ; package_types ; packages ; externs ; types >.
  
  Definition flatten_DeclCtx (ctx : DeclCtx) :=
    ((List.rev ctx.(controls))
       ++ (List.rev ctx.(parsers))
       ++ ctx.(functions)
                ++ ctx.(packages)
                         ++ ctx.(externs))%list.
  
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
  
  Definition add_control (decl : DeclCtx) (c : TopDecl.d) :=
    decl <| controls := c :: decl.(controls) |>.

  Definition add_parser (decl : DeclCtx) (p : TopDecl.d) :=
    decl <| parsers := p::decl.(parsers) |>.

  Definition add_package (decl : DeclCtx) (p : TopDecl.d) :=
    decl <| packages := p::decl.(packages) |>.

  Definition
    add_package_type
      (decl : DeclCtx) (pt : string * (TopDecl.constructor_params * list E.t)) :=
    decl <| package_types := pt :: decl.(package_types) |>.

  Definition add_extern (decl : DeclCtx) (e : TopDecl.d) :=
    decl <| externs := e::decl.(externs) |>.

  Definition add_table (decl : DeclCtx) (t : Control.d) :=
    decl <| tables := t::decl.(tables) |>.
  
  Definition add_action (decl : DeclCtx) (a : Control.d) :=
    decl <| actions := a::decl.(actions) |>.

  Definition add_type (decl : DeclCtx) (typvar : string) (typ : E.t) :=
    decl <| types := (typvar, typ) :: decl.(types) |>.

  (* TODO! *)
  Fail Fixpoint tsub_ts (σ : Env.t string E.t) (ts : Field.fs string E.t) :=
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

  (* TODO. *)
  Fail Definition subst_type (decl : DeclCtx) (typvar : string) (type : E.t) : DeclCtx :=
    let σ := [(typvar, type)] in
    let tsub_ds := List.map (Sub.tsub_d σ) in
    let tsub_Cds := List.map (Sub.tsub_Cd σ) in
    let tsub_pts := Field.map (fun '(cub_type_params, cub_params, tags) =>
                                 let σ' := Sub.remove_types σ cub_type_params in
                                 let cub_params' := Field.map (Sub.tsub_cparam σ') cub_params in
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
  
  Definition to_decls (decls : DeclCtx) : list TopDecl.d :=
    let decls :=
      List.concat
        [decls.(controls);
         decls.(parsers);
         decls.(functions);
         decls.(packages);
         decls.(externs)] in
    let dummy_type := {| paramargs := []; rtrns := None |} in
    let dummy_function := TopDecl.Funct "$DUMMY" 0 dummy_type ST.Skip in
    List.rev (dummy_function :: decls).
  
  Definition of_cdecl (decls : DeclCtx) (d : Control.d) :=
    match d with
    | Control.Action _ _ _ _ =>
        add_action decls d
    | Control.Table _ _ _ =>
        add_table decls d
    end.

  Definition extend (hi_prio lo_prio: DeclCtx) : DeclCtx :=
    let combine {A : Type} (f : DeclCtx -> list A) := append (f hi_prio) (f lo_prio) in
    {| controls := combine controls;
      parsers := combine parsers;
      tables := combine tables;
      actions := combine actions;
      functions := combine functions;
      package_types := combine package_types;
      packages := combine packages;
      externs := combine externs;
      types := append hi_prio.(types) lo_prio.(types);
    |}.
  
  Definition to_ctrl_decl (c: DeclCtx) : list Control.d :=
    List.rev
      (Control.Action "$DUMMY_ACTION" [] [] ST.Skip
                      :: append c.(actions) c.(tables)).
  
  Definition decl_has_name (name : string) (d : TopDecl.d) :=
    match d with
    | TopDecl.Instantiate x _ _ _ _
    | TopDecl.Extern x _ _ _ _
    | TopDecl.Control x _ _ _ _ _ _
    | TopDecl.Parser x _ _ _ _ _ _
    | TopDecl.Funct x _ _ _ => String.eqb name x
    end.
  
  Definition cdecl_has_name (name : string) (d : Control.d) :=
    match d with
    | Control.Action x _ _ _
    | Control.Table x _ _ => String.eqb name x
    end.
  
  Definition is_member (name : string) (l : list (TopDecl.d)) : bool :=
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
  
  Definition width_of_enum (members : list (P4String.t tags_t)) :=
    let num_members := List.length members in
    PeanoNat.Nat.max 1 (PeanoNat.Nat.log2_up num_members).
  
  Definition cub_type_of_enum (members : list (P4String.t tags_t)) :=
    E.TBit (Npos (pos (width_of_enum members))).
    
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
  
  Fixpoint get_enum_id_aux (idx : nat) (member_list : list (P4String.t tags_t)) (member : P4String.t tags_t) : result nat :=
    match member_list with
    | [] => error  ("Could not find member" ++ P4String.str member ++ "in member list")
    | m::ms =>
        if P4String.str member =? P4String.str m
        then ok idx
        else get_enum_id_aux (idx + 1) ms member
    end.
  
  Definition get_enum_id := get_enum_id_aux 0.
  
  Definition get_name (e : Expression) : result (P4String.t tags_t) :=
    let '(MkExpression _ pre_e _ _ ) := e in
    match pre_e with
    | ExpName (BareName n ) _ => ok n
    | ExpName _ _ => error "Qualified Names are Deprecated"
    | _ => error "Tried to get the name of an expression that wasn't an ExpName"
    end.
  
  Definition
    apply_arg_to_param
    '((typ, exp) : paramarg E.t E.t * E.e)
    (acc : result (list (paramarg E.e E.e)))
    : result (list (paramarg E.e E.e)) :=
    let+ fs := acc in
    match typ with
    | PAIn _ => PAIn exp
    | PAOut _ => PAOut exp
    | PAInOut _ => PAInOut exp
    end :: fs.
  
  Definition paramarg_fst {A B C : Set} (p : paramarg (A * B) (A * C)) : A :=
    match p with
    | PAIn (a,_)
    | PAOut (a,_)
    | PAInOut (a,_) => a
    end.
  
  Definition paramarg_elim {A : Set} (p : paramarg A A) : A :=
    match p with
    | PAIn a | PAOut a | PAInOut a => a
    end.
  
  Fixpoint
    apply_args_to_params
    (f_str : string) (params : list (string * paramarg E.t E.t))
    (args : list (option E.e)) : result (list (paramarg E.e E.e)) :=
    match params, args with
    | [], [] => ok []
    | [], _ =>
        error
          ("Passed too many arguments to "
             ++ f_str ++ " ("  ++ string_of_nat (List.length args) ++ " extra)")
    | _, [] =>
        error
          ("Insufficient arguments for "
             ++ f_str ++ " (" ++ string_of_nat (List.length params) ++ " are missing)")
    | _::params', None::args' =>
        apply_args_to_params f_str params' args'
    | (_,param)::params', (Some arg)::args' =>
        apply_arg_to_param (param, arg) (apply_args_to_params f_str params' args')
    end.
  
  Fixpoint get_hdr_stack_name (e : Expression) : result string :=
    let '(MkExpression tags pre_e typ dir) := e in
    match pre_e with
    | ExpName (BareName str) loc =>
        ok (P4String.str str)
    | ExpExpressionMember exp name =>
        let+ rec_name := get_hdr_stack_name exp in
        rec_name ++ "." ++ @P4String.str tags_t name
    | _ =>
        error "ERROR :: Failed to compute string for header stack.. didnt recognize expresssion type"
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
  
  Definition total_wildcard (patterns : list Parser.pat) : bool :=
    fold_right (fun p acc => match p with
                          | Parser.Wild => acc
                          | _ => false
                          end)
               true patterns.
  
  Definition
    lookup_params_by_ctor_name
      (name : string) (ctx : DeclCtx)
    : result (TopDecl.constructor_params * list E.t) :=
    match lookup_instantiatable ctx name with
    | Some (TopDecl.Parser _ cparams expr_cparmas _ _ _ _)  =>
        ok (cparams, expr_cparmas)
    | Some (TopDecl.Control _ cparams expr_cparmas _ _ _ _) =>
        ok (cparams, expr_cparmas)
    | Some (TopDecl.Extern _ _ cparams expr_cparmas _) =>
        ok (cparams, expr_cparmas)
    | Some _ =>
        error ("Dont kow how to get constructors for " ++ name)
    | None =>
        match List.find (String.eqb name ∘ fst) ctx.(package_types) with
        | Some (_, cparams) =>
            ok cparams
        | None =>
            error
              ("Error, couldn't find: "
                 ++ name ++ " from " ++ string_of_nat (List.length ctx.(externs)) ++ " externs")
        end
    end.
  
  Section TranslateUnderTypeParams.
    Variable typ_names : list string.

    Fixpoint
      translate_exp_type
      (typ : @P4Type tags_t) {struct typ} : result E.t :=
      let translate_fields fs :=
        sequence (List.map (fun '(_, typ) => translate_exp_type typ) fs) in
      match typ with
      | TypBool => ok E.TBool
      | TypString => ok E.TBool
      | TypInteger => error "[FIXME] P4cub doesnt support Integers"
      | TypInt w => ok (E.TInt (posN w))
      | TypBit w => ok (E.TBit w)
      | TypVarBit w => error "[FIXME] Compile to fixed-width"
      | TypArray typ n =>
          let+ t := translate_exp_type typ in
          header_stack_type t n
      | TypTuple types
      | TypList types =>
          let+ cub_types :=
            types
              ▷ List.map translate_exp_type
              ▷ sequence in
          E.TStruct false cub_types
      | TypRecord fields
      | TypStruct fields =>
          translate_fields fields >>| E.TStruct false
      | TypSet elt_type =>
          (* Shows up in typechecking a select *)
          error "A set is not an expression type"
      | TypError => ok E.TError
      | TypMatchKind =>
          error "A matchkind is not an expression type"
      | TypVoid => error "[FIXME] void is not the type of any expression literal"
      | TypHeader fields =>
          translate_fields fields >>| E.TStruct true
      | TypHeaderUnion _ =>
          error "[FIXME] Header Unions need to be compiled away or added to p4cub"
      | TypEnum name typ members =>
          ok (cub_type_of_enum members)
      | TypTypeName {| P4String.str := name |} =>
          Result.from_opt
            (ListUtil.index_of string_dec name typ_names)
            ("TypeError :: Unbound type name " ++ name)
            >>| E.TVar
      | TypNewType _ typ => translate_exp_type typ
      | TypControl _ =>
          (* FIXME Solve control type issue*)
          error ("TypeError :: A control is not an expression")
      | TypParser c =>
          (* FIXME solve control type issue*)
          error ("TypeError :: A parser is not an expression")
      | TypExtern name =>
          (* error "An extern is not an expression type" *)
          error ("TypeError :: An extern is not an expression type")
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
          translate_exp_type base
      | TypConstructor _ _ _ _ =>
          error "A type constructor is not an expression"
      end.
    
    Section Expressions.
      Variable term_names : list string.
      
      Fixpoint translate_expression (e : @Expression tags_t) {struct e} : result E.e :=
        let '(MkExpression i e_pre typ dir) := e in
        match e_pre with
        | ExpBool b =>
            ok (E.Bool b)
        | ExpInt z =>
            match z.(width_signed) with
            | Some (w, b) =>
                if b then
                  ok (E.Int (posN w) z.(value))
                else
                  ok (E.Bit w z.(value))
            | None =>
                error
                  ("[FIXME] integer didnt have a width: "
                     ++ string_of_nat (BinInt.Z.to_nat z.(value)))
            end
        | ExpString _ =>
            (* [FIXME] strings need to be compiled away *)
            ok (E.Bool false)
        | ExpName name loc =>
            match name with
            | BareName {| P4String.str := x |} =>
                let* n :=
                  Result.from_opt
                    (ListUtil.index_of string_dec x term_names)
                    ("Unbound name " ++ x) in
                let+ cub_type := translate_exp_type typ in
                E.Var cub_type x n
            | QualifiedName namespaces name =>
                error "Qualified names should be eliminated"
            end
        | ExpArrayAccess array index =>
            let* e1 := translate_expression array in
            let* e2 := translate_expression index in
            match get_type_of_expr array with
            | TypArray header_type size =>
                let+ t := translate_exp_type header_type in
                header_stack_access t size e1 e2
            | _ =>
                error
                  "TypeError :: Elements of array access do not have expected types"
            end
        | ExpBitStringAccess bits lo hi =>
            let* typ := translate_exp_type (get_type_of_expr bits) in
            let+ e := translate_expression bits in
            (* Positive doesnt let you represent 0, so increase each by one*)
            (* Make sure to check ToGCL.to_rvalue when changing *)
            E.Slice (posN (BinNatDef.N.succ hi)) (posN (BinNatDef.N.succ lo)) e
        | ExpList values =>
            let+ cub_values :=
              values
                ▷ List.map translate_expression
                ▷ sequence in
            E.Lists E.lists_struct cub_values
        | ExpRecord entries =>
            let+ cub_entries :=
              entries
                ▷ List.map (fun '(_,expr) => translate_expression expr)
                ▷ sequence in
            E.Lists E.lists_struct cub_entries
        | ExpUnaryOp op arg =>
            let eop := translate_op_uni op in
            let* typ := translate_exp_type typ in
            let+ earg := translate_expression arg in
            E.Uop typ eop earg
        | ExpBinaryOp op e1 e2 =>
            let* typ' := translate_exp_type typ in
            let* e1' := translate_expression e1 in
            let* e2' := translate_expression e2 in
            let+ eop := translate_op_bin op in
            E.Bop typ' eop e1' e2'
        | ExpCast typ expr =>
            let* expr' := translate_expression expr in
            let+ typ' := translate_exp_type typ in
            E.Cast typ' expr'
        | ExpTypeMember _ name =>
            match typ with
            | TypEnum _ _ members =>
                let w := width_of_enum members in
                let+ n := get_enum_id members name in
                E.Bit (Npos (pos w)) (BinIntDef.Z.of_nat n)
            | _ =>
                error "Type Error. Type Member had non-enum type"
            end
        | ExpErrorMember str =>
            ok (E.Error (P4String.str str))
        | ExpExpressionMember expr {| P4String.str := name |} =>
            let* cub_type := translate_exp_type typ in
            match get_type_of_expr expr with
            | TypRecord fs
            | TypHeader fs
            | TypStruct fs =>
                let keys := List.map (P4String.str ∘ fst) fs in
                let* index :=
                  Result.from_opt
                    (ListUtil.index_of string_dec name keys)
                    ("TypeError:: member field missing " ++ name) in
                let+ cub_expr := translate_expression expr in
                E.Member cub_type index cub_expr
            | _ =>
                error
                  ("TypeError :: Member expression requires a field type.")
            end
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
        end.
      
      Definition translate_return_type (ret : @P4Type tags_t) :=
        match ret with
        | TypVoid => ok None
        | _ =>
            let+ x := translate_exp_type ret in
            Some x
        end.
      
      Definition parameter_to_paramarg
                 '(MkParameter _ dir typ _ {| P4String.str := x |} : @P4Parameter tags_t)
        : result (string * paramarg E.t E.t) :=
        let+ t := translate_exp_type typ in
        (x, match dir with
            | Directionless
            | In => PAIn t
            | Out => PAOut t
            | InOut => PAInOut t
            end).

      Definition parameters_to_params (parameters : list (@P4Parameter tags_t))
        : result (list (string * paramarg E.t E.t)) :=
        rred (List.map (parameter_to_paramarg) parameters).
      
      Definition translate_expression_and_type e :=
        let* cub_t := translate_exp_type (get_type_of_expr e) in
        let+ cub_e := translate_expression e in
        (cub_t, cub_e).

      Definition translate_arglist
        : list (option (@Expression tags_t)) -> result (list (option E.e)):=
        commute_result_optlist ∘ (list_of_opts_map translate_expression).

      Definition translate_application_args
                 (callee : string)
                 (parameters : list P4Parameter)
                 (args : list (option (@Expression tags_t)))
        : result (list (paramarg E.e E.e)) :=
        let* (cub_args : list (option E.e)) := translate_arglist args in
        let* (params : list (string * paramarg E.t E.t)) := parameters_to_params parameters in
        apply_args_to_params callee params cub_args.
      
      Definition translate_apply callee args ret_var ret_type : result ST.s :=
        let typ := get_type_of_expr callee in
        match typ with
        | TypControl (MkControlType type_params parameters) =>
            let* callee_name := get_name callee in
            let callee_name_string := P4String.str callee_name in
            let+ paramargs := translate_application_args callee_name_string parameters args in
            ST.Apply callee_name_string [] paramargs
        | TypTable _ =>
            let* callee_name := get_name callee in
            let callee_string := P4String.str callee_name in
            let+ cub_name :=
              Result.from_opt
                (ListUtil.index_of string_dec callee_string term_names)
                ("TypeError :: name " ++ callee_string ++ "not found.") in
            (* TODO make this an EExprMember *)
            match ret_var, ret_type with
            | Some (original_name,rv), Some rt =>
                let switch_expr := E.Var rt original_name rv in
                let action_run_var := E.Var rt callee_string cub_name in
                (* TODO: lookup keys to make arguments. *)
                ST.Seq (ST.Invoke callee_string [])
                       (ST.Assign switch_expr action_run_var)
            | _, _ =>
                (* TODO: lookup keys to make arguments. *)
                ST.Invoke callee_string []
                          
            end
        | TypParser _ =>
            error "[FIXME] translate parser apply calls"
        | _ =>
            error "Error got a type that cannot be applied."
        end.
      
      Definition translate_set_validity v callee :=
        let+ hdr := translate_expression callee in
        ST.Assign hdr (Expr.Uop Expr.TBool (Expr.SetValidity v) hdr).
      
      Definition translate_is_valid callee retvar :=
        let* hdr := translate_expression callee in
        match retvar with
        | None => error "IsValid has no return value"
        | Some (original_name,rv) =>
            ok (ST.Assign (E.Var E.TBool original_name rv)
                          (E.Uop E.TBool E.IsValid hdr))
        end.
      
      Definition translate_extern_string (ctx : DeclCtx) (extern_str f_str : string) args :=
        let extern_decl :=  find (decl_has_name extern_str) ctx.(externs) in
        match extern_decl with
        | None => error ("ERROR expected an extern, but got " ++ extern_str)
        | Some (TopDecl.Extern extn_name tparams cparams exp_cparams methods) =>
            let called_method := find (fun '(nm, _) => String.eqb nm f_str) methods in
            match called_method with
            | None =>
                error ("Couldn't find " ++ extern_str ++ "." ++ f_str)
            | Some (_, (targs, ar)) =>
                let params := paramargs ar in
                let* cub_args := translate_arglist args in
                let+ args := apply_args_to_params f_str params cub_args in
                (* TODO Currently assuming method calls return None*)
                ST.Call (ST.Method extern_str f_str [] None) args
            end
        | Some _ =>
            error "Invariant Violated. Declaration Context Extern list contained something other than an extern."
        end.
      
      Definition translate_expression_member_call
                 (args : list (option (@Expression tags_t)))
                 (ctx : DeclCtx)
                 (callee : Expression)
                 (ret_var : option (string * nat))
                 (ret_type : option E.t)
                 (f : P4String.t tags_t) : result ST.s :=
        let f_str := P4String.str f in
        if f_str =? "apply" then
          translate_apply callee args ret_var ret_type
        else if f_str =? "setInvalid" then
               translate_set_validity false callee
             else if f_str =? "setValid" then
                    translate_set_validity true callee
                  else if f_str =? "isValid" then
                         translate_is_valid callee ret_var
                       else
                         match get_type_of_expr callee with
                         | TypTypeName extern_obj
                         | TypExtern extern_obj =>
                             translate_extern_string ctx (P4String.str extern_obj) f_str args
                         | TypSpecializedType (TypExtern extern_obj_type) extern_obj_type_args =>
                             (* [TODO] Something is weird here RE type arguments *)
                             translate_extern_string ctx (P4String.str extern_obj_type) f_str args
                         | TypArray typ n =>
                             let* op :=
                               (if f_str =? "pop_front" then ok pop_front
                                else
                                  if f_str =? "push_front" then ok push_front
                                  else error ("ERROR :: unknown header_stack operation " ++ f_str))
                             in
                             let* num_ops :=
                               match args with
                               | [Some (MkExpression tags (ExpInt int) typ dir)] =>
                                   ok int.(value)
                               | [None] | [] => ok 1%Z
                               | _ =>
                                   error ("Got an incorrect number of arguments for header stack operation "
                                            ++ f_str ++
                                            "Expected 1 or 0, got " ++ string_of_nat (List.length args))
                               end in
                             let* hdr_stack := translate_expression callee in
                             let+ cub_type := translate_exp_type typ in
                             op cub_type n num_ops hdr_stack
                         | _ =>
                             error (String.append "[ERROR] Cannot translate non-externs member functions that aren't `apply`s: " f_str)
                         end.
      
      Definition
        translate_function_application
        (fname : P4String.t tags_t) ret type_args parameters args : result ST.s :=
        let* paramargs := translate_application_args (P4String.str fname) parameters args in
        let+ cub_type_params := rred (List.map translate_exp_type type_args) in
        ST.Call (ST.Funct (P4String.str fname) cub_type_params ret) paramargs.
      
      Definition
        function_call_init
        (ctx : DeclCtx) (e : Expression)
        (ret_var : string * nat) (ret_type : E.t) : option (result ST.s) :=
        let '(MkExpression tags expr typ dir) := e in
        match expr with
        | ExpFunctionCall func type_args args =>
            let '(MkExpression tags func_pre typ dir) := func in
            match func_pre with
            | ExpExpressionMember callee f =>
                Some $
                     translate_expression_member_call
                     args ctx callee (Some ret_var) (Some ret_type) f
            | ExpName (BareName n) loc =>
                match typ with
                | TypFunction (MkFunctionType type_params parameters kind ret) =>
                    Some $
                         translate_function_application
                         n (Some (Expr.Var ret_type (fst ret_var) (snd ret_var))) type_args parameters args
                | _ =>
                    Some $
                         error
                         ("[function_call_init] A name,"
                            ++ P4String.str n
                            ++ "applied like a method call, must be a function or extern type; I got something else")
                end
            | _ => Some $ error "ERROR :: Cannot handle this kind of expression"
            end
        | _ => None
        end.
    End Expressions.
    
    Fixpoint
      translate_statement_switch_case
      (term_names : list string)
      ctx (match_expr : E.e) (bits : N)
      (tenum : list (P4String.t tags_t)) (acc : (option E.e) * (ST.s -> ST.s))
      (ssw : @StatementSwitchCase tags_t)
      : result ((option E.e) * (ST.s -> ST.s)) :=
      (* break apart the accumulation into the aggregated
         condition and the aggregated if-then continuation *)
      let '(cond_opt, ifthen) := acc in
      (* Force the agggregated conditional to be a boolean *)
      let acc_cond := SyntaxUtil.force (E.Bool false) cond_opt in
      (* Build the case match by building the label
         index check and or-ing the aggregated conditional *)
      let case_match label :=
        let+ val := get_label_index tenum label in
        let mtch := E.Bop E.TBool E.Eq match_expr (E.Bit bits val) in
        E.Bop E.TBool E.Or acc_cond mtch in
      (* check the cases *)
      match ssw with
      | StatSwCaseAction tags label block =>
          (* This case discharges the built up conditions. so the first part of the pair is always None *)
          match label with
          | StatSwLabName tags labname =>
              let* cond := case_match labname in
              let* st :=
                translate_block
                  term_names 
                  ctx block in
              let else__ifthen else_ := ST.Conditional cond st else_ in
              (* The continuation is still "open" *)
              ok (None, ifthen ∘ else__ifthen)
          | StatSwLabDefault tags =>
              let* else_ :=
                translate_block
                  term_names 
                  ctx block in
              (* in the default case, we throw away the argument because we have the else case, *)
              (* if anything comes after, its dead code *)
              ok (None, fun (_ : ST.s) => (ifthen else_ : ST.s))
          end
      | StatSwCaseFallThrough tags label =>
          match label with
          | StatSwLabDefault _ =>
              error "[ERROR] Cannot have default label as a fall-through case in a switch statement"
          | StatSwLabName tags labname =>
              (* This case doesn't change the continuation but accumulates a condition *)
              (* Note that the accumulation happens automagically in the [case_match function]*)
              let+ cond := case_match labname in
              (Some cond, (ifthen : ST.s -> ST.s))
          end
      end
    with translate_statement_pre_t
           (term_names  : list string)
           (ctx : DeclCtx) (pre_s : @StatementPreT tags_t) : result ST.s :=
           match pre_s with
           | StatMethodCall func type_args args =>
               let '(MkExpression tags func_pre typ dir) := func in
               match func_pre with
               | ExpExpressionMember callee f =>
                   translate_expression_member_call
                     term_names 
                     args ctx callee None None f
               | ExpName (BareName n) loc =>
                   match typ with
                   | TypFunction (MkFunctionType type_params parameters kind ret) =>
                       translate_function_application
                         term_names
                         n None type_args parameters args
                   | TypAction data_params ctrl_params =>
                       let+ paramargs :=
                         translate_application_args
                           term_names
                           (P4String.str n) (data_params ++ ctrl_params) args in
                       let num_of_data_args := List.length data_params in
                       let data_args := List.firstn num_of_data_args paramargs in
                       let ctrl_args :=
                         List.map
                           paramarg_elim
                           (List.skipn num_of_data_args paramargs) in
                       ST.Call (ST.Action (P4String.str n) ctrl_args) data_args
                   | _ => error ("[translate_statement_pre_t] A name," ++ P4String.str n ++"applied like a method call, must be a function or extern type; I got something else")
                   end
               | _ => error "ERROR :: Cannot handle this kind of expression"
               end
           | StatAssignment lhs rhs =>
               let* cub_lhs := translate_expression term_names lhs in
               let+ cub_rhs := translate_expression term_names rhs in
               ST.Assign cub_lhs cub_rhs
           | StatDirectApplication typ func_typ args =>
               error "[FIXME] (StatDirectApplication) Need to translate into instantiation and then application"
           | StatConditional cond tru fls_opt =>
               let* cub_cond := translate_expression term_names cond in
               let* cub_tru := translate_statement
                                 term_names  ctx tru in
               let+ cub_fls := match fls_opt with
                               | None => ok ST.Skip
                               | Some fls =>
                                   translate_statement term_names  ctx fls
                               end in
               ST.Conditional cub_cond cub_tru cub_fls
           | StatBlock block =>
               translate_block term_names  ctx block
           | StatExit =>
               ok ST.Exit
           | StatEmpty =>
               ok ST.Skip
           | StatReturn expr_opt =>
               match expr_opt with
               | Some e =>
                   let+ (cub_typ, cub_expr) := translate_expression_and_type term_names e in
                   ST.Return (Some cub_expr)
               | None =>
                   ok (ST.Return None)
               end
           | StatSwitch expr cases =>
               let* tenum := get_enum_type expr in
               let bits := BinNat.N.of_nat (PeanoNat.Nat.log2_up (List.length tenum)) in
               let* expr := translate_expression term_names expr in
               let+ (_, cases_as_ifs) :=
                 List.fold_left (fun acc_res switch_case =>
                                   let* acc := acc_res in
                                   translate_statement_switch_case
                                     term_names 
                                     ctx expr bits tenum acc switch_case
                                ) cases (ok (None, fun x => x))
                                
               in
               cases_as_ifs ST.Skip
           | StatConstant typ name value loc =>
               error "Constant Statement should not occur"
           | StatVariable typ name init loc =>
               error "Should be handled directly in translate_block"
           | StatInstantiation typ args name init =>
               error "Instantiation statement should not occur"
           end
    with translate_statement
           (term_names  : list string)
           (ctx : DeclCtx) (s : @Statement tags_t) : result ST.s :=
           match s with
           | MkStatement _ stmt _ =>
               translate_statement_pre_t
                 term_names 
                 ctx stmt
           end
    with translate_block
           (term_names  : list string)
           (ctx : DeclCtx) (b : @Block tags_t) : result ST.s :=
           match b with
           | BlockEmpty _ =>
               ok ST.Skip
           | BlockCons
               (MkStatement
                  _ (StatVariable
                       t {| P4String.str := x|} None _) _) blk =>
               let* t := translate_exp_type t in
               let+ s :=
                 translate_block
                   (x :: term_names)
                    ctx blk in
               ST.Var x (inl t) s
           | BlockCons
               (MkStatement
                  _ (StatVariable
                       t {| P4String.str := x|} (Some e) _) _) blk =>
               let* t := translate_exp_type t in
               match function_call_init
                       term_names
                       ctx e (x,0) t with
               | None =>
                   let* e := translate_expression term_names e in
                   let+ s :=
                     translate_block
                       (x :: term_names)                       
                       ctx blk in
                   ST.Var x (inr e) s
               | Some call =>
                   let* call := call in
                   let+ s :=
                     translate_block
                       (x :: term_names)                       
                       ctx blk in
                   ST.Var x (inl t) (ST.Seq call s)
               end 
           | BlockCons statement rest =>
               let* s1 :=
                 translate_statement
                   term_names 
                   ctx statement in
               let+ s2 :=
                 translate_block
                   term_names 
                   ctx rest in
               ST.Seq s1 s2
           end.
  End TranslateUnderTypeParams.
    
  Definition translate_state_name
             (parser_states : list string)
             '({|P4String.str:=state_name|} : P4String.t tags_t)
    : result Parser.state_label :=
    if  (state_name =? "accept")%string then ok Parser.Accept
    else if (state_name =? "start")%string then ok Parser.Start
         else
           let+ n :=
             Result.from_opt
               (ListUtil.index_of string_dec state_name parser_states)
               ("Parser state " ++ state_name ++ " not found.") in
           Parser.Name n.
  
  Definition translate_pre_expr_to_pattern
             pre_expr : result Parser.pat :=
    let value := @value tags_t in
    match pre_expr with
    | ExpDontCare => ok Parser.Wild
    (* | ExpRange lo hi => *)
    (*   let* lopat := translate_expression_to_pattern lo in *)
    (*   let+ hipat := translate_expression_to_pattern hi in *)
    (*   Parser.Range lopat hipat *)
    (* | ExpMask expr mask => *)
    (*   let* expr_pat := translate_expression_to_pattern expr in *)
    (*   let+ mask_pat := translate_expression_to_pattern mask in *)
    (*   Parser.Mask expr_pat mask_pat *)
    | ExpInt z =>
        match z.(width_signed) with
        | Some (w, signed) =>
            if signed
            then ok (Parser.Int (posN w) z.(value))
            else ok (Parser.Bit w z.(value))
        | None => error "Masked ints must have a known width"
        end
    | ExpCast (TypSet (TypBit w)) (MkExpression _ (ExpInt z) _ _) =>
        match z.(width_signed) with
        | Some (_, signed) =>
            if signed
            then ok (Parser.Int (posN w) z.(value))
            else ok (Parser.Bit w z.(value))
        | _ => error
                ("ints must have a known width: "
                   ++ string_of_nat (BinInt.Z.to_nat z.(value)))
        end
    | _ => error "unknown set variant"
    end.
  
  Definition translate_expression_to_pattern
             (e : @Expression tags_t) : result Parser.pat :=
    let '(MkExpression tags pre_expr typ dir) := e in
    translate_pre_expr_to_pattern pre_expr.

  Definition translate_match (m : Match) : result Parser.pat :=
    let '(MkMatch tags pre_match typ) := m in
    match pre_match with
    | MatchDontCare => ok Parser.Wild
    | MatchMask e mask =>
        let* p_e := translate_expression_to_pattern e in
        let+ p_m := translate_expression_to_pattern mask in
        Parser.Mask p_e p_m
    | MatchRange lo hi =>
        let* p_lo := translate_expression_to_pattern lo in
        let+ p_hi := translate_expression_to_pattern hi in
        Parser.Mask p_lo p_hi
    | MatchCast typ m =>
        translate_pre_expr_to_pattern (ExpCast typ m)
    end.
    
  Definition translate_matches : list Match -> result (list Parser.pat) :=
    rred ∘ (List.map translate_match).

  Definition
    translate_parser_case
    (parser_states : list string)
    (pcase : @ParserCase tags_t)
    : result (Parser.state_label + (Parser.pat * Parser.state_label)) :=
    let '(MkParserCase tags matches next) := pcase in
    let* state_id := translate_state_name parser_states next in
    let+ patterns := translate_matches matches in
    if total_wildcard patterns
    then inl state_id
    else inr (Parser.Lists patterns, state_id).
  
  Definition translate_parser_case_loop
             (parser_states : list string)
             pcase acc :=
    let* (def_opt, cases) := acc in
    let+ cub_case :=
      translate_parser_case parser_states pcase in
    match cub_case with
    | inl x => (Some x, cases)
    | inr y => (def_opt, y::cases)
    end.

  (* TODO ASSUME default is the last element of case list *)
  Definition
    translate_cases
    (parser_states : list string)
    (cases : list (@ParserCase tags_t))
    : result (Parser.state_label * Field.fs Parser.pat Parser.state_label) :=
    let* (def_opt, cases) :=
      List.fold_right
        (translate_parser_case_loop
           parser_states)
        (ok (None, [])) cases in
    let def :=
      SyntaxUtil.force
        Parser.Reject def_opt in
    ok (def, cases).
  
  Definition
    translate_transition
    (term_names parser_states : list string)
    (transition : ParserTransition)
    : result (Parser.pt) :=
    match transition with
    | ParserDirect _ next =>
        let+ next_state :=
          translate_state_name
            parser_states next in
        Parser.Direct next_state
    | ParserSelect _ exprs cases =>
        let* type_expr_list :=
          rred
            (List.map
               (translate_expression_and_type
                  [] term_names)
               exprs) in
        let expr_list := List.map snd type_expr_list in
        let+ (default, cub_cases) :=
          translate_cases parser_states cases in
        Parser.Select
          (E.Lists E.lists_struct expr_list) default cub_cases
    end.

  (** Translates the parser state block
      & inserts a transition at the end. *)
  Fixpoint
    translate_parser_state_block
    (term_names parser_states : list string)
    (ctx : DeclCtx) (parser_state_block : list Statement)
    (transition : ParserTransition) : result ST.s :=
    match parser_state_block with
    | [] =>
        let+ pe :=
          translate_transition
            term_names parser_states transition in
        Stmt.Transition pe
    | MkStatement
        _ (StatVariable
             t {| P4String.str := x|} None _) _
        :: s =>
        let* t := translate_exp_type [] t in
        let+ s :=
          translate_parser_state_block
            (x :: term_names)
            parser_states ctx s transition in
        ST.Var x (inl t) s
    | MkStatement
        _ (StatVariable
             t {| P4String.str := x|} (Some e) _) _
        :: s =>
        let* t := translate_exp_type [] t in
        match function_call_init
                [] term_names
                ctx e (x,0) t with
        | None =>
            let* e := translate_expression [] term_names e in
            let+ s :=
              translate_parser_state_block
                (x :: term_names)                
                parser_states ctx s transition in
            ST.Var x (inr e) s
        | Some call =>
            let* call := call in
            let+ s :=
              translate_parser_state_block
                (x :: term_names)
                parser_states ctx s transition in
            ST.Var x (inl t) (ST.Seq call s)
        end 
    | statement :: rest =>
        let* s1 :=
          translate_statement
            [] term_names 
            ctx statement in
        let+ s2 :=
          translate_parser_state_block
            term_names 
            parser_states ctx rest transition in
        ST.Seq s1 s2
    end.
  
  Definition
    translate_parser_state
    (term_names  parser_states : list string)
    (ctx : DeclCtx) (pstate : ParserState)
    : result ST.s :=
    let '(MkParserState
            _ _ statements transition) := pstate in
    (*let* state_id :=
      Result.from_opt
      (ListUtil.index_of
      string_dec name
      parser_states)
      ("TypeError:: unbound state name " ++ name) in *)
    let+ parser_state :=
      translate_parser_state_block
        term_names  parser_states
        ctx statements transition in
    parser_state.

  Definition
    name_of_ParserState
    '(MkParserState
        _ {| P4String.str := x |}
        _ _ : @ParserState tags_t) : string := x.
  
  Definition
    translate_parser_states_inner
      (term_names parser_states : list string)
      (ctx : DeclCtx) (p : ParserState)
      (res_acc : result (option ST.s * list ST.s)) :=
    let* state :=
      translate_parser_state
        term_names 
        parser_states ctx p in
    let+ (start_opt, states) := res_acc in
    if "start" =? (name_of_ParserState p)
    then (Some state, state::states)
    else (start_opt, state::states).

  Definition
    translate_parser_states
    (term_names : list string)
    (ctx : DeclCtx)
    (pstates : list ParserState)
    : result (option ST.s * list ST.s) :=
    let parser_states :=
      (* TODO: separate start state? *)
      List.map name_of_ParserState pstates in
    fold_right
      (translate_parser_states_inner
         term_names 
         parser_states ctx) (ok (None, [])) pstates.
  
  Definition
    translate_constructor_arg_expression
    (term_names : list string) (arg : @Expression tags_t) : result E.e :=
    match translate_expression [] term_names arg with
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

  Definition
    translate_constructor_parameter
    (typ_names : list string)
    (parameter : @P4Parameter tags_t) : result (string * TopDecl.it) :=
    let '(MkParameter opt dir typ default_arg_id var) := parameter in
    match typ with
    | TypExtern typname =>
      ok (P4String.str var, TopDecl.ExternInstType (P4String.str typname))
    | TypControl (MkControlType _ ps) =>
        (* TODO: how to get extern params? *)
        let+ params := parameters_to_params typ_names ps in
        (P4String.str var, TopDecl.ControlInstType [] params)
    | TypParser (MkControlType _ ps) =>
        (* TODO: how to get extern params? *)
        let+ params := parameters_to_params typ_names ps in
        (P4String.str var, TopDecl.ParserInstType [] params)
    | TypPackage _ _ _  =>
        ok (P4String.str var, TopDecl.PackageInstType)
    | TypSpecializedType (TypTypeName name) typ_args  =>
        (*ok (TopDecl.EType (E.TVar (P4String.str name)))*)
        error "[FIXME] need substition function"
    | _ =>
      error "[FIXME] dont khow how to translate type to constructor type"
    end.

  Definition translate_constructor_parameters typ_names :=
    fold_right
      (fun p acc =>
         let* params := acc in
         let+ param :=
           translate_constructor_parameter typ_names p in
         param :: params) (ok []).

  (* TODO write in terms of translate_constructor_parameter *)
  Definition
    translate_constructor_parameter_either
    (typ_names : list string) (parameter : @P4Parameter tags_t)
    : result (string + TopDecl.it) :=
    let '(MkParameter opt dir typ default_arg_id var) := parameter in
    let v_str := P4String.str var in
    match typ with
    | TypExtern typname =>
      (* Translate to CTExtern or to extern list? *)
      ok (inl (P4String.str typname))
    | TypControl (MkControlType _ ps) =>
        (* TODO: how to get extern params? *)
        parameters_to_params
          typ_names ps
          >>| inr ∘ TopDecl.ControlInstType []
    | TypParser (MkControlType _ ps) =>
        (* TODO: how to get extern params? *)
        parameters_to_params
          typ_names ps
          >>| inr ∘ TopDecl.ParserInstType []
    | TypPackage _ _ _  =>
        ok $ inr TopDecl.PackageInstType
    | _ =>
      error "[FIXME] dont know how to translate type to constructor type"
      (* let+ cub_type := translate_exp_type tags typ in *)
      (* Right (v_str, E.CTType cub_type) *)
    end.

  Definition
    partition_constructor_params
    (typ_names : list string)
    (params : list (@P4Parameter tags_t)) :=
    fold_right
      (fun p acc =>
         let* (extn, ctrlr) := acc in
         let+ param :=
           translate_constructor_parameter_either
             typ_names p in
         match param with
         | inl e => (e :: extn, ctrlr)
         | inr c => (extn, c::ctrlr)
         end) (ok ([],[])) params.

  Definition
    translate_key
    (typ_names term_names : list string)
    (key : TableKey) : result (E.e * string) :=
    let '(MkTableKey tags key_exp matchkind) := key in
    let+ e := translate_expression typ_names term_names key_exp in
    (e, P4String.str matchkind).

  Definition
    translate_keys_loop
    (typ_names term_names : list string) (key : TableKey)
    (acc : result (list (E.e * string)))
    : result (list (E.e * string)) :=
    let* cub_key := translate_key typ_names term_names key in
    let+ cub_keys := acc in
    cub_key :: cub_keys.

  Definition
    translate_keys
    (typ_names term_names : list string)
    (keys : list TableKey) : result (list (E.e * string)) :=
    List.fold_right (translate_keys_loop typ_names term_names) (ok []) keys.

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

  Definition get_cub_type_args typ_names typ :=
    match typ with
    | TypSpecializedType _ args =>
        rred (List.map (translate_exp_type typ_names) args)
    | _ => ok []
    end.

  Definition translate_actions (actions : list TableActionRef) : result (list string) :=
    List.fold_right translate_actions_loop (ok []) actions.

  Definition
    translate_decl_fields
    (typ_names : list string)
    (fields : list DeclarationField)
    : result (list E.t) :=
    rred (List.map
            (fun '(MkDeclarationField i typ name) =>
               translate_exp_type typ_names typ)
            fields).

  Definition will_be_p4cub_cnstr_typ (t : @P4Type tags_t) : bool :=
    match t with
    | TypControl _
    | TypParser _
    | TypExtern _
    | TypPackage _ _ _ => true
    | _ => false
    end.

  Definition translate_instantiation_args
    (term_names : list string) (args : list (@Expression tags_t))
    : result (TopDecl.constructor_args * list E.e) :=
    let '(cargs, cargs_exps) :=
      List.partition
        (will_be_p4cub_cnstr_typ ∘ get_type_of_expr) args in
    let* cargs :=
      sequence (M := result_monad_inst)
        $ List.map
        (fun '(MkExpression _ e _ _ : @Expression tags_t) =>
           match e with
           | ExpName (BareName {| P4String.str := x |}) _ => ok x
           | _ =>
               Result.error
                 "TypError:: No non-variable expressions with constructor types allowed."
           end)
        cargs in
    let+ cargs_exps :=
      sequence (M := result_monad_inst)
        $ List.map (translate_expression [] term_names) cargs_exps in
    (cargs, cargs_exps).

  Definition translate_to_constructor_params
    (typ_names : list string)
    (params : list (@P4Parameter tags_t))
    : result (TopDecl.constructor_params * list E.t) :=
    let '(cparams, expr_cparams) :=
      List.partition
        (will_be_p4cub_cnstr_typ ∘ SyntaxUtil.get_param_typ)
        params in
    Result.bind
      (translate_constructor_parameters typ_names cparams)
      (fun (cparams : TopDecl.constructor_params) =>
         let+ (expr_cparams : list E.t) :=
           sequence (M := result_monad_inst)
             (List.map (translate_exp_type typ_names)
                (List.map SyntaxUtil.get_param_typ expr_cparams)) in
         (cparams, expr_cparams)).

  Definition translate_runtime_params
    (typ_names : list string)
    (params : list (@P4Parameter tags_t))
    : result (list (string * string) * E.params) :=
    let '(eparams, params) :=
      List.partition
        (fun '(MkParameter _ _ t _ _) =>
           match t with
           | TypExtern _ => true | _ => false
           end)
        params in
    let* eparams :=
      sequence
        $ List.map
        (fun '(MkParameter _ _ t _ {| P4String.str:=x |}) =>
           match t with
           | TypExtern {| P4String.str := y |} => ok (x,y)
           | _ => error "Implementation error, should only be extern types here."
           end) eparams in
    let+ params :=
      parameters_to_params typ_names params in
    (eparams, params).

  Definition translate_method
    (typ_names : list string)
    (m : MethodPrototype)
    : result
        (TopDecl.constructor_params * list Expr.t
         + string * (nat * list string * E.arrowT)) :=
    match m with
    | ProtoMethod tags ret name type_args parameters =>
        let typ_names :=
          (List.map P4String.str type_args ++ typ_names)%list in
        let* cub_ret :=
          translate_return_type typ_names ret in
        let+ params :=
          parameters_to_params typ_names parameters in
        let arrowtype : Expr.arrowT := {| paramargs:=params; rtrns := cub_ret |} in
        (* TODO: how to get extern arguments? *)
        inr (P4String.str name,
            (List.length type_args, [], arrowtype))
    | ProtoConstructor _ _ parameters  =>
        translate_to_constructor_params typ_names parameters >>| inl
    | ProtoAbstractMethod _ _ _ _ _ =>
      error "[FIXME] Dont know how to translate abstract methods"
    end.

  Fixpoint partition_map {A B C : Type}
    (f : A -> B + C) (l : list A) : list B * list C :=
    match l with
    | [] => ([], [])
    | a :: l =>
        let '(bs, cs) := partition_map f l in
        match f a with
        | inl b => (b :: bs, cs)
        | inr c => (bs, c :: cs)
        end
    end.
  
  Definition
    translate_methods
    (typ_names : list string)
    (ms : list MethodPrototype)
    : result (TopDecl.constructor_params * list Expr.t
              * Field.fs string (nat * list string * E.arrowT)) :=
    let+ ms := rred (List.map (translate_method typ_names) ms) in
    let '(cnstrs, ms) := partition_map (fun x => x) ms in
    (hd ([],[]) cnstrs, ms).

  (* TODO: add variable names to
     [term_names] and thread it through
     compilation of program. *)
  Fixpoint translate_decl
           (term_names  : list string)
           (ctx : DeclCtx)
           (d : @Declaration tags_t) {struct d}: result DeclCtx :=
    match d with
    | DeclConstant tags typ name value =>
        error "[FIXME] Constant declarations unimplemented"
    | DeclInstantiation tags typ args name init =>
        let cub_name := P4String.str name in
        let* ctor_p4string := get_string_from_type typ in
        let ctor_name := P4String.str ctor_p4string in
        let* '(cnstr_args, exp_cnstr_args) :=
          translate_instantiation_args term_names args in
        let* type_args := get_cub_type_args [] typ in
        let d := TopDecl.Instantiate
                   ctor_name cub_name type_args cnstr_args exp_cnstr_args in
        let+ add_to_context := get_augment_from_name ctx ctor_name in
        add_to_context d
    | DeclParser tags name _ params constructor_params _ states =>
        let cub_name := P4String.str name in
        let* (cub_cparams,cub_expr_cparams) :=
          translate_to_constructor_params
            [] constructor_params in
        let* '(cub_eparams, cub_params) := translate_runtime_params [] params in
        let* (start_opt, cub_states) :=
          translate_parser_states
            term_names  ctx states in
        let*~ cub_start :=
          start_opt else
    "could not find a starting state for the parser" in
        let d :=
          TopDecl.Parser
            cub_name cub_cparams cub_expr_cparams cub_eparams
            cub_params cub_start cub_states in
        ok (add_parser ctx d)
    | DeclControl
        tags name type_params params constructor_params locals apply_blk =>
        let typ_names := List.map P4String.str type_params in
        let cub_name := P4String.str name in
        let* (cub_cparams, cub_expr_cparams) :=
          translate_to_constructor_params
            typ_names constructor_params in
        let* '(cub_eparams, cub_params) := translate_runtime_params [] params in
        let* local_ctx :=
          let loop acc decl :=
            let* ctx := acc in
            translate_decl term_names  ctx decl in
          fold_left loop locals (ok ctx)
        in
        (* This step loses information about local instantiations *)
        let cub_body := to_ctrl_decl local_ctx in
        let+ cub_block :=
          translate_block
            typ_names term_names 
            local_ctx apply_blk in
        (* Lift body decls & rename occurences in d *)
        let d :=
          TopDecl.Control
            cub_name cub_cparams cub_expr_cparams cub_eparams
            cub_params cub_body cub_block in
        (* THIS IS CERTAINLY WRONG *)
        add_control local_ctx d
    | DeclFunction tags ret name type_params params body =>
        (* let cub_name := P4String.str name in *)
        (* let* cub_signature :=
           error "[FIXME] Translate function signature" in *)
        (* let* cub_body := error "[FIXME] Translate function bodies" in *)
        (* error "[FIXME] implement function declarations" *)
        ok ctx
  | DeclExternFunction tags ret name type_params parameters =>
      let typ_names := List.map P4String.str type_params in
      let* cub_ret := translate_return_type typ_names ret in
      let* params := parameters_to_params typ_names parameters in
      let arrowtype := {|paramargs:=params; rtrns:=cub_ret|} in
      let method := (P4String.str name, (0, [], arrowtype)) in
      (* TODO come up with better naming scheme for externs *)
      let d := TopDecl.Extern "_" 0 [] [] [method] in
      ok (add_extern ctx d)
  | DeclVariable tags typ name None =>
        (* error "[FIXME] Variable Declarations unimplemented" *)
        ok ctx
    | DeclVariable tags typ name (Some e) =>
        (* error "[FIXME] Variable Declarations unimplemented" *)
        ok ctx
    | DeclValueSet tags typ size name =>
        (* error "[FIXME] Value Set declarations unimplemented" *)
        ok ctx
    | DeclAction tags name data_params ctrl_params body =>
        (* TODO High prio *)
        let cub_name := P4String.str name in
        let* ctrl_params :=
          parameters_to_params
            [] ctrl_params
            >>| map_snd paramarg_elim in
        let* data_params :=
          (* TODO: perhaps translate_decl
             needs to pass a [typ_names]
             parameter? *)
          parameters_to_params [] data_params in
        let+ cub_body :=
          translate_block
            [] term_names 
            ctx body in
        let a :=
          Control.Action
            cub_name ctrl_params data_params cub_body in
        add_action ctx a
    | DeclTable
        tags name keys actions entries
        default_action size custom_properties =>
        (* TODO High prio *)
        let name := P4String.str name in
        let* cub_keys :=
          translate_keys
            [] term_names keys
            >>| List.map (Utils.prod_map_l t_of_e) in
        let+ cub_actions := translate_actions actions in
        add_table ctx (Control.Table name cub_keys cub_actions)
    | DeclHeader tags name fields =>
        (* error "[FIXME] Header Declarations unimplemented" *)
        let+ fs := translate_decl_fields [] fields in
        let t := E.TStruct true fs in
        add_type ctx (P4String.str name) t
    | DeclHeaderUnion tags name fields =>
        (* error "[FIXME] Header Union Declarations unimplemented" *)
        ok ctx
    | DeclStruct tags name fields =>
        let+ fs := translate_decl_fields [] fields in
        let t := E.TStruct false fs in
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
        let typ_names := List.map P4String.str type_params in
        let str_name := P4String.str name in
        let+ (cparams,expr_cparams,cub_methods) :=
          translate_methods typ_names methods in
        let d :=
          TopDecl.Extern
            str_name (List.length type_params)
            cparams expr_cparams cub_methods in
        add_extern ctx d
    | DeclTypeDef tags name (inl typ) =>
        let+ typ := translate_exp_type [] typ in
        add_type ctx (P4String.str name) typ
    | DeclTypeDef tags name (inr typ) =>
        (* [FIXME] what to do here? *)
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
        let cub_type_params :=
          List.map (@P4String.str tags_t) type_params in
        let+ (cub_cparams,cub_expr_cparams) :=
          translate_to_constructor_params cub_type_params parameters in
        (* error "[FIXME] P4light inlining step necessary" *)
        let p :=
          (cub_name, (cub_cparams, cub_expr_cparams)) in
        add_package_type ctx p
    end.

  Fixpoint inline_types_decls decls :=
    match decls with
    | [] => ok []
    | d::decls =>
      let+ decls' := inline_types_decls decls in
      match substitution_from_decl d with
      | None => d::decls'
      | Some σ =>
          let decls'' :=
            List.map (@substitute_typ_Declaration tags_t σ) decls' in
          d :: decls''
      end
    end.

  Definition inline_types_prog '(Program decls) :=
    let+ decls' := inline_types_decls decls in
    Program decls'.

  (* This is redunant with the locals resolution in the previous code, but I
   * can't get it to compile using mutual fixpoints *)
  Definition translate_decls (decls : list (@Declaration tags_t)) : result DeclCtx :=
    let loop acc decl :=
      let* ctx := acc in
      translate_decl [] ctx decl in
    fold_left loop decls (ok (empty_declaration_context)).

  Definition
    seq_opt
    (d : TopDecl.d) (r : option (TopDecl.d)) : list TopDecl.d :=
    match r with
    | None => [d]
    | Some rst => [d; rst]
    end.

  Definition preprocess (tags : tags_t) p :=
    let* hoisted_simpl :=
      hoist_nameless_instantiations
        tags_t (SimplExpr.transform_prog tags p) in
    let '(_,d) := inline_typ_program Maps.IdentMap.empty hoisted_simpl in ok d.
  (*inline_types_prog hoisted_simpl.*)

  Fail Definition inline_cub_types (decls : DeclCtx) :=
    fold_left (fun acc '(x,t) => subst_type acc x t) (decls.(types)) decls.

  Definition infer_member_types (decl : DeclCtx) :=
    let infer_ds := List.map InferMemberTypes.inf_d in
    let infer_Cds := List.map InferMemberTypes.inf_Cd in
    let infer_pts := Field.map (fun '(cparams,ts) =>
                                  (cparams, (* TODO: infer member types? *) ts)) in
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
    infer_member_types ((*inline_cub_types*) cub_decls).

  Definition translate_program' (tags : tags_t) (p : program) : result (list TopDecl.d) :=
    let+ ctx := translate_program tags p in 
    flatten_DeclCtx ctx.
    
End ToP4cub.
