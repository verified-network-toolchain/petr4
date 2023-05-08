Require Import String.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
From Poulet4 Require Import
     P4light.Transformations.SimplExpr
     P4light.Transformations.InlineTypeDecl
     P4light.Transformations.InlineConstants
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

Module ST := Stm.
Module E := Exp.
Module Sub := Syntax.Substitution.

Definition map_filter {A B : Type} (f : A -> option B) : list A -> list B :=
  List.fold_right
    (fun a bs =>
       (match f a with
       | Some b => [b]
       | None => []
       end ++ bs)%list) [].

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
    {Err A : Type} (l : list (option (result Err A)))
  : result Err (list (option A)) :=
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
    | O => "_"
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

  Definition string_of_name
    (x : @Typed.name tags_t) : string :=
    match x with
    | Typed.BareName {| P4String.str := x |}
    | Typed.QualifiedName _ {| P4String.str := x |} => x
    end.
  
  Fixpoint get_func_name
    (e : @Expression tags_t) : string :=
    match e with
    | MkExpression _ (ExpName x _) _ _ => string_of_name x
    | MkExpression _
        (ExpExpressionMember e {| P4String.str := x |})
        _ _=> get_func_name e ++ "." ++ x
    | _ => "don't know"
    end.
  
  Import Typed.
  Import P4Int.

  Definition pos : (nat -> positive) := BinPos.Pos.of_nat.
  Definition posN (n : N) : positive := pos (BinNat.N.to_nat n).

  (* maybe should be:
     1. a list of top decls
     2. a list of control decls *)
  Record DeclCtx :=
    mkDeclCtx {
        variables : list Ctrl.t;
        controls :  list Top.t;
        parsers : list Top.t;
        tables : list Ctrl.t;
        actions : list Ctrl.t;
        functions : list Top.t;
        package_types : Field.fs string (Top.constructor_params * list Typ.t);
        packages : list Top.t;
        externs : list Top.t;
        types : list (string * Typ.t);
      }.
  
  Global Instance etaDeclCtx : Settable _ :=
    settable! mkDeclCtx
    < variables ; controls ; parsers; tables ; actions
  ; functions ; package_types ; packages ; externs ; types >.
  
  Definition flatten_DeclCtx (ctx : DeclCtx) :=
    ((List.rev ctx.(controls))
       ++ (List.rev ctx.(parsers))
       ++ ctx.(functions)
                ++ ctx.(packages)
                         ++ ctx.(externs))%list.
  
  Definition empty_declaration_context :=
    {| variables := [];
      controls := [];
      parsers := [];
      tables := [];
      actions := [];
      functions := [];
      package_types := [];
      packages := [];
      externs := [];
      types := []
    |}.

  Definition add_variable (decl : DeclCtx) (d : Ctrl.t) :=
    decl <| variables := d :: decl.(variables) |>.
  
  Definition add_control (decl : DeclCtx) (c : Top.t) :=
    decl <| controls := c :: decl.(controls) |>.

  Definition add_parser (decl : DeclCtx) (p : Top.t) :=
    decl <| parsers := p::decl.(parsers) |>.

  Definition add_package (decl : DeclCtx) (p : Top.t) :=
    decl <| packages := p::decl.(packages) |>.

  Definition add_action (decls : DeclCtx) (a : Ctrl.t) :=
    decls <| actions := a :: decls.(actions) |>.

  Definition add_function (decls : DeclCtx) (f : Top.t) :=
    decls <| functions := f :: decls.(functions) |>.
  
  Definition
    add_package_type
      (decl : DeclCtx) (pt : string * (Top.constructor_params * list Typ.t)) :=
    decl <| package_types := pt :: decl.(package_types) |>.

  Section AppendMethods.
    Variables (ext_name : string)
      (type_params : nat)
      (cparams : Top.constructor_params)
      (ecparams : list Typ.t)
      (methods : Field.fs string (nat * list string * Typ.arrowT)).
  
    Fixpoint append_methods (externs : list Top.t) : list Top.t :=
      match externs with
      | [] => [Top.Extern ext_name type_params cparams ecparams methods]
      | Top.Extern x n cps ecps mtds as ext :: externs =>
          (if (x =? ext_name)%string then
             Top.Extern x n cps ecps (methods ++ mtds)%list :: externs
           else ext :: append_methods externs)
      | d :: externs => d :: append_methods externs
      end.
  End AppendMethods.
  
  Definition add_extern (decl : DeclCtx) (e : Top.t) :=
    match e with
    | Top.Extern x tps cps ecps methods =>
        decl <| externs :=
      if (x =? "_")%string then
        append_methods "_" tps cps ecps methods decl.(externs)
      else e :: decl.(externs) |>
      | _ => decl
    end.

  Definition add_table (decl : DeclCtx) (t : Ctrl.t) :=
    decl <| tables := t::decl.(tables) |>.
  
  Definition add_type (decl : DeclCtx) (typvar : string) (typ : Typ.t) :=
    decl <| types := (typvar, typ) :: decl.(types) |>.

  (* TODO! *)
  Fail Fixpoint tsub_ts (σ : Env.t string Typ.t) (ts : Field.fs string Typ.t) :=
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
  Fail Definition subst_type (decl : DeclCtx) (typvar : string) (type : Typ.t) : DeclCtx :=
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
  
  Definition to_decls (decls : DeclCtx) : list Top.t :=
    let decls :=
      List.concat
        [decls.(controls);
         decls.(parsers);
         decls.(functions);
         decls.(packages);
         decls.(externs)] in
    let dummy_type := {| paramargs := []; rtrns := None |} in
    let dummy_function := Top.Funct "$DUMMY" 0 dummy_type ST.Skip in
    List.rev (dummy_function :: decls).
  
  Definition of_cdecl (decls : DeclCtx) (d : Ctrl.t) :=
    match d with
    | Ctrl.Action _ _ _ _ =>
        add_action decls d
    | Ctrl.Table _ _ _ _ =>
        add_table decls d
    | _ => decls
    end.

  Definition extend (hi_prio lo_prio: DeclCtx) : DeclCtx :=
    let combine {A : Type} (f : DeclCtx -> list A) := append (f hi_prio) (f lo_prio) in
    {| variables := combine variables;
      controls := combine controls;
      parsers := combine parsers;
      tables := combine tables;
      actions := combine actions;
      functions := combine functions;
      package_types := combine package_types;
      packages := combine packages;
      externs := combine externs;
      types := append hi_prio.(types) lo_prio.(types);
    |}.
  
  Definition to_ctrl_decl (c: DeclCtx) : list Ctrl.t :=
    List.rev
      (append c.(variables) (append c.(actions) c.(tables))).
  
  Definition decl_has_name (name : string) (d : Top.t) :=
    match d with
    | Top.Instantiate _ x _ _ _
    | Top.Extern x _ _ _ _
    | Top.Control x _ _ _ _ _ _
    | Top.Parser x _ _ _ _ _ _
    | Top.Funct x _ _ _ => String.eqb name x
    end.
  
  Definition cdecl_has_name (name : string) (d : Ctrl.t) :=
    match d with
    | Ctrl.Var x _
    | Ctrl.Action x _ _ _
    | Ctrl.Table x _ _ _ => String.eqb name x
    end.
  
  Definition is_member (name : string) (l : list (Top.t)) : bool :=
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
  
  Definition get_variables (ctx : DeclCtx) : list string :=
    map_filter
      (fun d =>
         match d with
         | Ctrl.Var x _ => Some x
         | _ => None
         end)
      ctx.(variables).
  
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
  
  Definition translate_op_uni (op : OpUni) : Una.t :=
    match op with
    | Not => Una.Not
    | BitNot => Una.BitNot
    | UMinus => Una.Minus
    end.
  
  Definition translate_op_bin (op : OpBin) : result string Bin.t :=
    match op with
    | Plus => ok Bin.Plus
    | PlusSat => ok Bin.PlusSat
    | Minus => ok Bin.Minus
    | MinusSat => ok Bin.MinusSat
    | Mul => ok Bin.Times
    | Div => error "division not supported"
    | Mod => error "mod not supported"
    | Shl => ok Bin.Shl
    | Shr => ok Bin.Shr
    | Le => ok Bin.Le
    | Ge => ok Bin.Ge
    | Lt => ok Bin.Lt
    | Gt => ok Bin.Gt
    | Eq => ok Bin.Eq
    | NotEq => ok Bin.NotEq
    | BitAnd => ok Bin.BitAnd
    | BitXor => ok Bin.BitXor
    | BitOr => ok Bin.BitOr
    | PlusPlus => ok Bin.PlusPlus
    | And => ok Bin.And
    | Or => ok Bin.Or
    end.
  
  Definition width_of_enum (members : list (P4String.t tags_t)) :=
    let num_members := List.length members in
    PeanoNat.Nat.max 1 (PeanoNat.Nat.log2_up num_members).
  
  Definition cub_type_of_enum (members : list (P4String.t tags_t)) :=
    Typ.Bit (Npos (pos (width_of_enum members))).

  Definition get_type_of_expr (e : Expression) : @P4Type tags_t :=
    let '(MkExpression _ _ typ _) := e in
    typ.
  
  Fixpoint get_string_from_type (t : P4Type) : result string (P4String.t tags_t) :=
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
  
  Fixpoint get_enum_id_aux (idx : nat) (member_list : list (P4String.t tags_t)) (member : P4String.t tags_t) : result string nat :=
    match member_list with
    | [] => error  ("Could not find member" ++ P4String.str member ++ "in member list")
    | m::ms =>
        if P4String.str member =? P4String.str m
        then ok idx
        else get_enum_id_aux (idx + 1) ms member
    end.
  
  Definition get_enum_id := get_enum_id_aux 0.
  
  Definition get_name (e : Expression) : result string (P4String.t tags_t) :=
    let '(MkExpression _ pre_e _ _ ) := e in
    match pre_e with
    | ExpName (BareName n ) _ => ok n
    | ExpName _ _ => error "Qualified Names are Deprecated"
    | _ => error "Tried to get the name of an expression that wasn't an ExpName"
    end.
  
  Definition
    apply_arg_to_param
      (pa : Exp.t -> paramarg Exp.t Exp.t) (exp : Exp.t)
      (acc : result string (list (paramarg Exp.t Exp.t)))
    : result string (list (paramarg Exp.t Exp.t)) :=
    let+ fs := acc in
    pa exp :: fs.
  
  Definition paramarg_fst {A B C : Set} (p : paramarg (A * B) (A * C)) : A :=
    match p with
    | PAIn (a,_)
    | PAOut (a,_)
    | PAInOut (a,_) => a
    end.
  
  Fixpoint
    apply_args_to_params
      (f_str : string) (paramarg_cnstrs : list (Exp.t -> paramarg Exp.t Exp.t))
      (args : list (option Exp.t)) : result string (list (paramarg Exp.t Exp.t)) :=
    match paramarg_cnstrs, args with
    | [], [] => ok []
    | [], _ =>
        error
          ("Passed too many arguments to "
             ++ f_str ++ " ("  ++ string_of_nat (List.length args) ++ " extra)")
    | _, [] =>
        error
          ("Insufficient arguments for "
             ++ f_str ++ " (" ++ string_of_nat (List.length paramarg_cnstrs) ++ " are missing)")
    | _::params', None::args' =>
        apply_args_to_params f_str params' args'
    | paramarg_cnstr::paramarg_cnstrs, (Some arg)::args' =>
        apply_arg_to_param paramarg_cnstr arg (apply_args_to_params f_str paramarg_cnstrs args')
    end.
  
  Fixpoint get_hdr_stack_name (e : Expression) : result string string :=
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
  
  Definition get_label_index (tenum : list (P4String.t tags_t)) (label : P4String.t tags_t) : result string Z :=
    match ListUtil.findi (P4String.equivb label) tenum with
    | Some i =>
        ok (BinInt.Z.of_nat i)
    | None =>
        error ("[ERROR] Couldnt find label [" ++ P4String.str label ++ "] in enum")
    end.
  
  Definition get_enum_type (expression : @Expression tags_t) : result string (list (P4String.t tags_t)) :=
    let '(MkExpression tags pre_expr type dir) := expression in
    match type with
    | TypEnum _ _ variants =>
        ok variants
    | _ =>
        error "could not get enum type from non-enum variant"
    end.
  
  Definition total_wildcard (patterns : list Pat.t) : bool :=
    fold_right (fun p acc => match p with
                          | Pat.Wild => acc
                          | _ => false
                          end)
               true patterns.
  
  Definition
    lookup_params_by_ctor_name
      (name : string) (ctx : DeclCtx)
    : result string (Top.constructor_params * list Typ.t) :=
    match lookup_instantiatable ctx name with
    | Some (Top.Parser _ cparams expr_cparmas _ _ _ _)  =>
        ok (cparams, expr_cparmas)
    | Some (Top.Control _ cparams expr_cparmas _ _ _ _) =>
        ok (cparams, expr_cparmas)
    | Some (Top.Extern _ _ cparams expr_cparmas _) =>
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
      (typ : @P4Type tags_t) {struct typ} : result string Typ.t :=
      let translate_fields fs :=
        sequence (List.map (fun '(_, typ) => translate_exp_type typ) fs) in
      match typ with
      | TypBool => ok Typ.Bool
      | TypString => ok Typ.Bool
      | TypInteger => error "[FIXME] P4cub doesnt support Integers"
      | TypInt w => ok (Typ.Int (posN w))
      | TypBit w => ok (Typ.Bit w)
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
          Typ.Struct false cub_types
      | TypRecord fields
      | TypStruct fields =>
          translate_fields fields >>| Typ.Struct false
      | TypSet elt_type =>
          (* Shows up in typechecking a select *)
          error "A set is not an expression type"
      | TypError => ok Typ.Error
      | TypMatchKind =>
          error "A matchkind is not an expression type"
      | TypVoid => error "[FIXME] void is not the type of any expression literal"
      | TypHeader fields =>
          translate_fields fields >>| Typ.Struct true
      | TypHeaderUnion _ =>
          error "[FIXME] Header Unions need to be compiled away or added to p4cub"
      | TypEnum name typ members =>
          ok (cub_type_of_enum members)
      | TypTypeName {| P4String.str := name |} =>
          Result.from_opt
            (ListUtil.index_of string_dec name typ_names)
            ("TypeError :: Unbound type name " ++ name)
            >>| Typ.Var
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
      
      Fixpoint translate_expression (e : @Expression tags_t) {struct e} : result string Exp.t :=
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
            | None => ok (E.Int (Z.to_pos z.(value)) z.(value))
                (*error
                  ("[FIXME] integer didnt have a width: "
                     ++ string_of_nat (BinInt.Z.to_nat z.(value)))*)
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
            E.Lists Lst.Struct cub_values
        | ExpRecord entries =>
            let+ cub_entries :=
              entries
                ▷ List.map (fun '(_,expr) => translate_expression expr)
                ▷ sequence in
            E.Lists Lst.Struct cub_entries
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
            if (name =? "next")%string then
              let* cub_type := translate_exp_type typ in
              let* cub_expr := translate_expression expr in
              match get_type_of_expr expr with
              | TypArray _ size => ok (header_stack_next cub_type size cub_expr)
              | _ => error "TypeError :: next operates on header stacks only!"
              end
            else if (name =? "last")%string then
              let* cub_type := translate_exp_type typ in
              let* cub_expr := translate_expression expr in
              match get_type_of_expr expr with
              | TypArray _ size => ok (header_stack_last cub_type size cub_expr)
              | _ => error "TypeError :: last operates on header stacks only!"
              end
            else if (name =? "lastIndex")%string then
              let+ cub_expr := translate_expression expr in
              header_stack_last_index cub_expr
            else if (name =? "isValid")%string then
              let+ cub_expr := translate_expression expr in
              E.Uop Typ.Bool Una.IsValid cub_expr
            else

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
              | TypSpecializedType _ _ =>
                  error
                    ("TypeError :: Member expression jives not with specialized type.")
              | TypNewType _ _ =>
                  error
                    ("TypeError :: Member expression jives not with new type.")
              | TypTypeName _ =>
                  error ("TypeError :: Member expression jives not with type name.")
              | TypHeaderUnion _ =>
                  error
                    ("TypeError :: Member expression jives not with tuple.")
              | TypTuple _ =>
                  error
                    ("TypeError :: Member expression jives not with tuple.")
              | TypList _ =>
                  error
                    ("TypeError :: Member expression jives not with list.")
              | TypArray _ _ =>
                  error
                    ("TypeError :: Member expression jives not with array.")
              | _ =>
                  error
                    ("TypeError :: Member expression requires a field type.")
              end
        | ExpTernary cond tru fls =>
            error "Ternary expressions should have been hoisted by a previous pass"
        (*| ExpFunctionCall _ =>*)
        | ExpFunctionCall func type_args args =>
            error
              ("calling " ++ get_func_name func
                 ++ ", Function Calls should have been hoisted by a previous pass")
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
        : result string (string * paramarg Typ.t Typ.t) :=
        let+ t := translate_exp_type typ in
        (x, match dir with
            | Directionless
            | In => PAIn t
            | Out => PAOut t
            | InOut => PAInOut t
            end).

      Definition parameters_to_params (parameters : list (@P4Parameter tags_t))
        : result string (list (string * paramarg Typ.t Typ.t)) :=
        rred (List.map (parameter_to_paramarg) parameters).
      
      Definition translate_expression_and_type e :=
        let* cub_t := translate_exp_type (get_type_of_expr e) in
        let+ cub_e := translate_expression e in
        (cub_t, cub_e).

      Definition translate_arglist
        : list (option (@Expression tags_t)) -> result string (list (option Exp.t)):=
        commute_result_optlist ∘ (list_of_opts_map translate_expression).

      Definition paramarg_cnstr_of_param
        '(MkParameter _ dir _ _ _ : @P4Parameter tags_t) : Exp.t -> paramarg Exp.t Exp.t :=
        match dir with
        | In | Directionless => PAIn
        | Out => PAOut
        | InOut => PAInOut
        end.
      
      Definition translate_application_args
                 (callee : string)
                 (parameters : list P4Parameter)
                 (args : list (option (@Expression tags_t)))
        : result string (list (paramarg Exp.t Exp.t)) :=
        let* (cub_args : list (option Exp.t)) := translate_arglist args in
        let paramarg_cnstrs := List.map paramarg_cnstr_of_param parameters in
        apply_args_to_params callee paramarg_cnstrs cub_args.
      
      Definition translate_apply callee args ret_var ret_type : result string ST.t :=
        let typ := get_type_of_expr callee in
        match typ with
        | TypControl (MkControlType type_params parameters) =>
            let* callee_name := get_name callee in
            let callee_name_string := P4String.str callee_name in
            let+ paramargs :=
              translate_application_args callee_name_string parameters args in
            ST.App (Call.Inst callee_name_string []) paramargs
        | TypTable _ =>
            let+ callee_name := get_name callee in
            let callee_string := P4String.str callee_name in
            (* TODO make this an Exp.Member *)
            match ret_var, ret_type with
              Some (original_name,rv), Some rt =>
                let switch_expr := E.Var rt original_name rv in
                ST.Invoke (Some switch_expr) callee_string
            | _, _ =>
                ST.Invoke None callee_string
            end
        | TypParser _ =>
            error "[FIXME] translate parser apply calls"
        | _ =>
            error "Error got a type that cannot be applied."
        end.
      
      Definition translate_set_validity v callee :=
        let+ hdr := translate_expression callee in
        ST.Asgn hdr (Exp.Uop Typ.Bool (Una.SetValidity v) hdr).
        (* ST.Asgn *)
        (*   (Exp.Uop Typ.Bool Una.IsValid hdr) *)
        (*   (exp.Bool v). *)

      Definition translate_is_valid callee retvar :=
        let* hdr := translate_expression callee in
        match retvar with
        | None => error "IsValid has no return value"
        | Some (original_name,rv) =>
            ok (ST.Asgn (E.Var Typ.Bool original_name rv)
                          (E.Uop Typ.Bool Una.IsValid hdr))
        end.
            
      Definition
        translate_function_application
          (fname : P4String.t tags_t) ret type_args parameters args : result string ST.t :=
        let* paramargs :=
          translate_application_args (P4String.str fname) parameters args in
        let+ cub_type_params := rred (List.map translate_exp_type type_args) in
        ST.App (Call.Funct (P4String.str fname) cub_type_params ret) paramargs.
    End Expressions.

    Definition translate_extern_string
      (term_names : list string) (ctx : DeclCtx) (extern_str f_str : string) args :=
      let extern_decl :=  find (decl_has_name extern_str) ctx.(externs) in
      match extern_decl with
      | None => error ("ERROR expected an extern, but got " ++ extern_str)
      | Some (Top.Extern extn_name tparams cparams exp_cparams methods) =>
          let called_method := find (fun '(nm, _) => String.eqb nm f_str) methods in
          match called_method with
          | None =>
              error ("Couldn't find " ++ extern_str ++ "." ++ f_str)
          | Some (_, (targs, ar)) =>
              let params := List.map
                              (fun '(_,pa) =>
                                 match pa with
                                 | PAIn _ => PAIn
                                 | PAOut _ => PAOut
                                 | PAInOut _ => PAInOut
                                 end)
                              (paramargs ar) in
              let* cub_args := translate_arglist (term_names ++ get_variables ctx) args in
              let+ args := apply_args_to_params f_str params cub_args in
              (* TODO Currently assuming method calls return None*)
              ST.App (Call.Method extern_str f_str [] None) args
          end
      | Some _ =>
          error "Invariant Violated. Declaration Context Extern list contained something other than an extern."
      end.
    
    Definition translate_expression_member_call
      (term_names : list string)
      (args : list (option (@Expression tags_t)))
      (ctx : DeclCtx)
      (callee : Expression)
      (ret_var : option (string * nat))
      (ret_type : option Typ.t)
      (f : P4String.t tags_t) : result string ST.t :=
      let f_str := P4String.str f in
      if f_str =? "apply" then
        translate_apply (term_names ++ get_variables ctx) callee args ret_var ret_type
      else if f_str =? "setInvalid" then
             translate_set_validity (term_names ++ get_variables ctx) false callee
           else if f_str =? "setValid" then
                  translate_set_validity (term_names ++ get_variables ctx) true callee
                else if f_str =? "isValid" then
                       translate_is_valid (term_names ++ get_variables ctx) callee ret_var
                     else
                       match get_type_of_expr callee with
                       | TypTypeName extern_obj
                       | TypExtern extern_obj =>
                           translate_extern_string term_names ctx (P4String.str extern_obj) f_str args
                       | TypSpecializedType (TypExtern extern_obj_type) extern_obj_type_args =>
                           (* [TODO] Something is weird here RE type arguments *)
                           translate_extern_string term_names ctx (P4String.str extern_obj_type) f_str args
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
                           let* hdr_stack := translate_expression (term_names ++ get_variables ctx) callee in
                           let+ cub_type := translate_exp_type typ in
                           op cub_type n num_ops hdr_stack
                       | _ =>
                           error
                             ("[ERROR] Cannot translate non-externs member functions that aren't `apply`s: "
                                ++ f_str)
                       end.

    Definition
      function_call_init
        (term_names : list string)
        (ctx : DeclCtx) (e : Expression)
        (ret_var : string * nat) (ret_type : Typ.t) : option (result string ST.t) :=
      let '(MkExpression tags expr typ dir) := e in
      match expr with
      | ExpFunctionCall func type_args args =>
          let '(MkExpression tags func_pre typ dir) := func in
          match func_pre with
          | ExpExpressionMember callee f =>
              Some $
                translate_expression_member_call
                term_names args ctx callee (Some ret_var) (Some ret_type) f
          | ExpName (BareName n) loc =>
              match typ with
              | TypFunction (MkFunctionType type_params parameters kind ret) =>
                  Some $
                    match kind with
                    | FunExtern =>
                        let* 'paramargs := translate_application_args
                                             (term_names ++ get_variables ctx) (P4String.str n) parameters args in
                        let+ cub_type_args := rred (lmap translate_exp_type type_args) in
                        (* TODO: need "_" to be initialized *)
                        ST.App
                          (Call.Method
                             "_" (P4String.str n) cub_type_args
                             (Some (Exp.Var ret_type (fst ret_var) (snd ret_var))))
                          paramargs
                    | _ => translate_function_application
                            (term_names ++ get_variables ctx)
                            n (Some (Exp.Var ret_type (fst ret_var) (snd ret_var))) type_args parameters args
                    end
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
    
    Fixpoint
      translate_statement_switch_case
        (term_names : list string)
      ctx (match_expr : Exp.t) (bits : N)
      (tenum : list (P4String.t tags_t)) (acc : (option Exp.t) * (ST.t -> ST.t))
      (ssw : @StatementSwitchCase tags_t)
      : result string ((option Exp.t) * (ST.t -> ST.t)) :=
      (* break apart the accumulation into the aggregated
         condition and the aggregated if-then continuation *)
      let '(cond_opt, ifthen) := acc in
      (* Force the agggregated conditional to be a boolean *)
      let acc_cond := SyntaxUtil.force (E.Bool false) cond_opt in
      (* Build the case match by building the label
         index check and or-ing the aggregated conditional *)
      let case_match label :=
        let+ val := get_label_index tenum label in
        let mtch := E.Bop Typ.Bool Bin.Eq match_expr (E.Bit bits val) in
        E.Bop Typ.Bool Bin.Or acc_cond mtch in
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
              let else__ifthen else_ := ST.Cond cond st else_ in
              (* The continuation is still "open" *)
              ok (None, ifthen ∘ else__ifthen)
          | StatSwLabDefault tags =>
              let* else_ :=
                translate_block
                  term_names 
                  ctx block in
              (* in the default case, we throw away the argument because we have the else case, *)
              (* if anything comes after, its dead code *)
              ok (None, fun (_ : ST.t) => (ifthen else_ : ST.t))
          end
      | StatSwCaseFallThrough tags label =>
          match label with
          | StatSwLabDefault _ =>
              error "[ERROR] Cannot have default label as a fall-through case in a switch statement"
          | StatSwLabName tags labname =>
              (* This case doesn't change the continuation but accumulates a condition *)
              (* Note that the accumulation happens automagically in the [case_match function]*)
              let+ cond := case_match labname in
              (Some cond, (ifthen : ST.t -> ST.t))
          end
      end
    with translate_statement_pre_t
           (term_names  : list string)
           (ctx : DeclCtx) (pre_s : @StatementPreT tags_t) : result string ST.t :=
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
                       match kind with
                       | FunExtern =>
                           let* 'paramargs := translate_application_args term_names (P4String.str n) parameters args in
                           let+ cub_type_args := rred (lmap translate_exp_type type_args) in
                           (* TODO: need "_" to be initialized *)
                           ST.App
                             (Call.Method
                                "_" (P4String.str n) cub_type_args None)
                             paramargs
                       | _ =>
                           translate_function_application
                             term_names
                             n None type_args parameters args
                       end
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
                       ST.App (Call.Action (P4String.str n) ctrl_args) data_args
                   | _ => error
                           ("[translate_statement_pre_t] A name,"
                              ++ P4String.str n
                              ++ " applied like a method call, must be a function or extern type; I got something else")
                   end
               | _ => error "ERROR :: Cannot handle this kind of expression"
               end
           | StatAssignment lhs rhs =>
               let* cub_lhs := translate_expression (term_names ++ get_variables ctx) lhs in
               let+ cub_rhs := translate_expression (term_names ++ get_variables ctx) rhs in
               ST.Asgn cub_lhs cub_rhs
           | StatDirectApplication typ func_typ args =>
               error "[FIXME] (StatDirectApplication) Need to translate into instantiation and then application"
           | StatConditional cond tru fls_opt =>
               let* cub_cond := translate_expression (term_names ++ get_variables ctx) cond in
               let* cub_tru := translate_statement
                                 term_names  ctx tru in
               let+ cub_fls := match fls_opt with
                               | None => ok ST.Skip
                               | Some fls =>
                                   translate_statement term_names  ctx fls
                               end in
               ST.Cond cub_cond cub_tru cub_fls
           | StatBlock block =>
               translate_block term_names  ctx block
           | StatExit =>
               ok ST.Exit
           | StatEmpty =>
               ok ST.Skip
           | StatReturn expr_opt =>
               match expr_opt with
               | Some e =>
                   let+ (cub_typ, cub_expr) :=
                     translate_expression_and_type (term_names ++ get_variables ctx) e in
                   ST.Ret (Some cub_expr)
               | None =>
                   ok (ST.Ret None)
               end
           | StatSwitch expr cases =>
               let* tenum := get_enum_type expr in
               let bits := BinNat.N.of_nat (PeanoNat.Nat.log2_up (List.length tenum)) in
               let* expr := translate_expression (term_names ++ get_variables ctx) expr in
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
           (ctx : DeclCtx) (s : @Statement tags_t) : result string ST.t :=
           match s with
           | MkStatement _ stmt _ =>
               translate_statement_pre_t
                 term_names 
                 ctx stmt
           end
    with translate_block
           (term_names  : list string)
           (ctx : DeclCtx) (b : @Block tags_t) : result string ST.t :=
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
               ST.LetIn x (inl t) s
           | BlockCons
               (MkStatement
                  _ (StatVariable
                       t {| P4String.str := x|} (Some e) _) _) blk =>
               let* t := translate_exp_type t in
               match function_call_init
                       term_names
                       ctx e (x,0) t with
               | None =>
                   let* e := translate_expression (term_names ++ get_variables ctx) e in
                   let+ s :=
                     translate_block
                       (x :: term_names)                       
                       ctx blk in
                   ST.LetIn x (inr e) s
               | Some call =>
                   let* call := call in
                   let+ s :=
                     translate_block
                       (x :: term_names)                       
                       ctx blk in
                   ST.LetIn x (inl t) (ST.Seq call s)
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
    : result string Lbl.t :=
    if  (state_name =? "accept")%string then ok Lbl.Accept
    else if (state_name =? "start")%string then ok Lbl.Start
         else
           let+ n :=
             Result.from_opt
               (ListUtil.index_of string_dec state_name parser_states)
               ("Parser state " ++ state_name ++ " not found.") in
           Lbl.Name n.
  
  Definition translate_pre_expr_to_pattern
    pre_expr : result string Pat.t :=
    let value := @value tags_t in
    match pre_expr with
    | ExpDontCare => ok Pat.Wild
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
            then ok (Pat.Int (posN w) z.(value))
            else ok (Pat.Bit w z.(value))
        | None => error "Masked ints must have a known width"
        end
    | ExpCast (TypSet (TypBit w)) (MkExpression _ (ExpInt z) _ _) =>
        match z.(width_signed) with
        | Some (_, signed) =>
            if signed
            then ok (Pat.Int (posN w) z.(value))
            else ok (Pat.Bit w z.(value))
        | _ => error
                ("ints must have a known width: "
                   ++ string_of_nat (BinInt.Z.to_nat z.(value)))
        end
    | _ => error "unknown set variant"
    end.
  
  Definition translate_expression_to_pattern
             (e : @Expression tags_t) : result string Pat.t :=
    let '(MkExpression tags pre_expr typ dir) := e in
    translate_pre_expr_to_pattern pre_expr.

  Definition translate_match (m : Match) : result string Pat.t :=
    let '(MkMatch tags pre_match typ) := m in
    match pre_match with
    | MatchDontCare => ok Pat.Wild
    | MatchMask e mask =>
        let* p_e := translate_expression_to_pattern e in
        let+ p_m := translate_expression_to_pattern mask in
        Pat.Mask p_e p_m
    | MatchRange lo hi =>
        let* p_lo := translate_expression_to_pattern lo in
        let+ p_hi := translate_expression_to_pattern hi in
        Pat.Mask p_lo p_hi
    | MatchCast typ m =>
        translate_pre_expr_to_pattern (ExpCast typ m)
    end.
    
  Definition translate_matches : list Match -> result string (list Pat.t) :=
    rred ∘ (List.map translate_match).

  Definition
    translate_parser_case
    (parser_states : list string)
    (pcase : @ParserCase tags_t)
    : result string (Lbl.t + (Pat.t * Lbl.t)) :=
    let '(MkParserCase tags matches next) := pcase in
    let* state_id := translate_state_name parser_states next in
    let+ patterns := translate_matches matches in
    if total_wildcard patterns
    then inl state_id
    else inr (Pat.Lists patterns, state_id).
  
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
    : result string (Lbl.t * Field.fs Pat.t Lbl.t) :=
    let* (def_opt, cases) :=
      List.fold_right
        (translate_parser_case_loop
           parser_states)
        (ok (None, [])) cases in
    let def :=
      SyntaxUtil.force
        Lbl.Reject def_opt in
    ok (def, cases).
  
  Definition
    translate_transition
    (term_names parser_states : list string)
    (transition : ParserTransition)
    : result string Trns.t :=
    match transition with
    | ParserDirect _ next =>
        let+ next_state :=
          translate_state_name
            parser_states next in
        Trns.Direct next_state
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
        Trns.Select
          (E.Lists Lst.Struct expr_list) default cub_cases
    end.

  (** Translates the parser state block
      & inserts a transition at the end. *)
  Fixpoint
    translate_parser_state_block
    (term_names parser_states : list string)
    (ctx : DeclCtx) (parser_state_block : list Statement)
    (transition : ParserTransition) : result string ST.t :=
    match parser_state_block with
    | [] =>
        let+ pe :=
          translate_transition
            (term_names ++ get_variables ctx) parser_states transition in
        Stm.Trans pe
    | MkStatement
        _ (StatVariable
             t {| P4String.str := x|} None _) _
        :: s =>
        let* t := translate_exp_type [] t in
        let+ s :=
          translate_parser_state_block
            (x :: term_names)
            parser_states ctx s transition in
        ST.LetIn x (inl t) s
    | MkStatement
        _ (StatVariable
             t {| P4String.str := x|} (Some e) _) _
        :: s =>
        let* t := translate_exp_type [] t in
        match function_call_init
                [] term_names
                ctx e (x,0) t with
        | None =>
            let* e := translate_expression [] (term_names ++ get_variables ctx) e in
            let+ s :=
              translate_parser_state_block
                (x :: term_names)                
                parser_states ctx s transition in
            ST.LetIn x (inr e) s
        | Some call =>
            let* call := call in
            let+ s :=
              translate_parser_state_block
                (x :: term_names)
                parser_states ctx s transition in
            ST.LetIn x (inl t) (ST.Seq call s)
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
    : result string ST.t :=
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
      (res_acc : result string (option ST.t * list ST.t)) :=
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
    : result string (option ST.t * list ST.t) :=
    let parser_states :=
      (* TODO: separate start state? *)
      List.map name_of_ParserState pstates in
    fold_right
      (translate_parser_states_inner
         term_names 
         parser_states ctx) (ok (None, [])) pstates.
  
  Definition
    translate_constructor_arg_expression
    (term_names : list string) (arg : @Expression tags_t) : result string Exp.t :=
    match translate_expression [] term_names arg with
    | Ok e =>
        (* try to reuse translation*)
        ok e
    | Error msg =>
        (* if the naive translation fails, try something better  *)
        let '(MkExpression tags expr typ dir) := arg in
        match expr with
        | _ =>
            error ("naive expression translation for constructor arguments failed with message: " ++ msg)
        end
    end.

  Definition translate_runtime_params
    (typ_names : list string)
    (params : list (@P4Parameter tags_t))
    : result string (list (string * string) * Typ.params) :=
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
  
  Definition
    translate_constructor_parameter
    (typ_names : list string)
    (parameter : @P4Parameter tags_t) : result string (string * InstTyp.t) :=
    let '(MkParameter opt dir typ default_arg_id var) := parameter in
    match typ with
    | TypExtern typname =>
        ok (P4String.str var, InstTyp.Extern (P4String.str typname))
    | TypControl (MkControlType _ ps) =>
        let+ (eparams,params) := translate_runtime_params typ_names ps in
        (P4String.str var, InstTyp.Ctr Cnstr.Control (List.map snd eparams) params)
    | TypParser (MkControlType _ ps) =>
        let+ (eparams,params) := translate_runtime_params typ_names ps in
        (P4String.str var, InstTyp.Ctr Cnstr.Parser (List.map snd eparams) params)
    | TypPackage _ _ _  =>
        ok (P4String.str var, InstTyp.Package)
    | TypSpecializedType (TypTypeName name) typ_args  =>
        (*ok (Top.EType (Typ.Var (P4String.str name)))*)
        error "[FIXME] need substition function"
    (*| TypSpecializedType _ _ => error "problem is here"*)
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
    : result string (string + InstTyp.t) :=
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
          >>| inr ∘ InstTyp.Ctr Cnstr.Control []
    | TypParser (MkControlType _ ps) =>
        (* TODO: how to get extern params? *)
        parameters_to_params
          typ_names ps
          >>| inr ∘ InstTyp.Ctr Cnstr.Parser []
    | TypPackage _ _ _  =>
        ok $ inr InstTyp.Package
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
    (key : TableKey) : result string (Exp.t * string) :=
    let '(MkTableKey tags key_exp matchkind) := key in
    let+ e := translate_expression typ_names term_names key_exp in
    (e, P4String.str matchkind).

  Definition
    translate_keys_loop
    (typ_names term_names : list string) (key : TableKey)
    (acc : result string (list (Exp.t * string)))
    : result string (list (Exp.t * string)) :=
    let* cub_key := translate_key typ_names term_names key in
    let+ cub_keys := acc in
    cub_key :: cub_keys.

  Definition
    translate_keys
    (typ_names term_names : list string)
    (keys : list TableKey) : result string (list (Exp.t * string)) :=
    List.fold_right (translate_keys_loop typ_names term_names) (ok []) keys.

  Definition translate_action
    (decls : DeclCtx) (term_names : list string) (action : TableActionRef)
    : result string (string * Exp.args) :=
    let '(MkTableActionRef tags pre_action typ) := action in
    let '(MkTablePreActionRef name args) := pre_action in
    match name with
    | BareName {|P4String.str := act_name |} =>
        match find_action decls act_name with
        | Some (Ctrl.Action _ _ params _) =>
            let paramarg_cnstrs :=
              List.map
                (fun '(_,p) =>
                   match p with
                   | PAIn _ => PAIn
                   | PAOut _ => PAOut
                   | PAInOut _ => PAInOut
                   end) params in
            let* (cub_args : list (option Exp.t))
              := translate_arglist [] term_names args in
            let+ args :=
              apply_args_to_params act_name paramarg_cnstrs cub_args in
            (act_name, args)
        | _ => error "could not find action for action ref"
        end
    | QualifiedName _ _ =>
      error "don't know how to deal with quantified names"
    end.

  Definition translate_actions_loop
    (decls : DeclCtx) (term_names : list string)
    (action : TableActionRef) (acc : result string (list (string * Exp.args)))
    : result string (list (string * Exp.args)) :=
    let* cub_act := translate_action decls term_names action in
    let+ cub_acts := acc in
    cub_act :: cub_acts.

  Definition get_cub_type_args typ_names typ :=
    match typ with
    | TypSpecializedType _ args =>
        rred (List.map (translate_exp_type typ_names) args)
    | _ => ok []
    end.

  Definition translate_actions
    (decls : DeclCtx) (term_names : list string)
    (actions : list TableActionRef) : result string (list (string * Exp.args)) :=
    List.fold_right
      (translate_actions_loop decls term_names)
         (ok []) actions.

  Definition
    translate_decl_fields
    (typ_names : list string)
    (fields : list DeclarationField)
    : result string (list Typ.t) :=
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
    : result string (Top.constructor_args * list Exp.t) :=
    let '(cargs, cargs_exps) :=
      List.partition
        (will_be_p4cub_cnstr_typ ∘ get_type_of_expr) args in
    let* cargs :=
      sequence
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
      sequence
        $ List.map (translate_expression [] term_names) cargs_exps in
    (cargs, cargs_exps).

  Definition translate_to_constructor_params
    (typ_names : list string)
    (params : list (@P4Parameter tags_t))
    : result string (Top.constructor_params * list (string * Typ.t)) :=
    let '(cparams, expr_cparams) :=
      List.partition
        (will_be_p4cub_cnstr_typ ∘ SyntaxUtil.get_param_typ)
        $ List.map collapse_P4Parameter params in
    let* cparams := translate_constructor_parameters typ_names cparams in
    let+ expr_cparams :=
      sequence
        (List.map
           (fun '(MkParameter _ _ t _ {| P4String.str := x |})
            => let+ t := translate_exp_type typ_names t in (x,t))
           expr_cparams) in
    (cparams, expr_cparams).

  Definition translate_method
    (typ_names : list string)
    (m : MethodPrototype)
    : result string
        (Top.constructor_params * list Typ.t
         + string * (nat * list string * Typ.arrowT)) :=
    match m with
    | ProtoMethod tags ret name type_args parameters =>
        let typ_names :=
          (List.map P4String.str type_args ++ typ_names)%list in
        let* cub_ret :=
          translate_return_type typ_names ret in
        let+ params :=
          parameters_to_params typ_names parameters in
        let arrowtype : Typ.arrowT := {| paramargs:=params; rtrns := cub_ret |} in
        (* TODO: how to get extern arguments? *)
        inr (P4String.str name,
            (List.length type_args, [], arrowtype))
    | ProtoConstructor _ _ parameters  =>
        let+ (cps, ecps) := translate_to_constructor_params typ_names parameters in
        inl (cps, List.map snd ecps)
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
    : result string (Top.constructor_params * list Typ.t
              * Field.fs string (nat * list string * Typ.arrowT)) :=
    let+ ms := rred (List.map (translate_method typ_names) ms) in
    let '(cnstrs, ms) := partition_map (fun x => x) ms in
    (hd ([],[]) cnstrs, ms).

  (* TODO: add variable names to
     [term_names] and thread it through
     compilation of program. *)
  Fixpoint translate_decl
           (term_names  : list string)
           (ctx : DeclCtx)
           (d : @Declaration tags_t) {struct d}: result string DeclCtx :=
    match d with
    | DeclConstant _ _ _ _ =>
      ok ctx (* inlined in previous pass *)
    | DeclInstantiation tags typ args name init =>
        let cub_name := P4String.str name in
        let* ctor_p4string := get_string_from_type typ in
        let ctor_name := P4String.str ctor_p4string in
        let* '(cnstr_args, exp_cnstr_args) :=
          translate_instantiation_args (term_names ++ get_variables ctx) args in
        let* type_args := get_cub_type_args [] typ in
        let d := Top.Instantiate
                   ctor_name cub_name type_args cnstr_args exp_cnstr_args in
        let+ add_to_context := get_augment_from_name ctx ctor_name in
        add_to_context d
    | DeclParser _ name _ params constructor_params locals states =>
        let cub_name := P4String.str name in
        let* (cub_cparams,cub_expr_cparams) :=
          translate_to_constructor_params
            [] constructor_params in
        let (names1, cub_expr_cparams) := List.split cub_expr_cparams in
        let* '(cub_eparams, cub_params) := translate_runtime_params [] params in
        let names2 := List.map fst cub_params in
        let* local_ctx :=
          let loop acc decl :=
            let* ctx := acc in
            translate_decl term_names ctx decl in
          fold_left loop locals (ok ctx) in
        let term_names := (names2 ++ names1 ++ term_names)%list in
        let* (start_opt, cub_states) :=
          translate_parser_states
            term_names local_ctx states in
        let*~ cub_start :=
          start_opt else
    "could not find a starting state for the parser" in
        let d :=
          Top.Parser
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
        let (names1,cub_expr_cparams) := List.split cub_expr_cparams in
        let* '(cub_eparams, cub_params) := translate_runtime_params [] params in
        let names2 := List.map fst cub_params in
        let term_names := (names2 ++ names1 ++ term_names)%list in
        let* local_ctx :=
          let loop acc decl :=
            let* ctx := acc in
            translate_decl term_names ctx decl in
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
          Top.Control
            cub_name cub_cparams cub_expr_cparams cub_eparams
            cub_params cub_body cub_block in
        (* THIS IS CERTAINLY WRONG
           should be [ctx] not [local_ctx]
           b/c actions and tables will leak out. *)
        add_control ctx d
| DeclFunction _ ret {| P4String.str := name |} type_params params body =>
    let typ_names := List.map P4String.str type_params in
    let* params := parameters_to_params typ_names params in
    let* ret :=
      match ret with
      | TypVoid => ok None
      | _ => translate_exp_type typ_names ret >>| Some
      end in
    let+ body := translate_block typ_names (List.map fst params) ctx body in
    add_function
      ctx
      (Top.Funct
         name (List.length typ_names)
         {| paramargs:=params; rtrns:=ret |} body)
  | DeclExternFunction tags ret {| P4String.str:=name |} type_params parameters =>
      let typ_names := List.map P4String.str type_params in
      let* cub_ret :=
        translate_return_type typ_names ret in
      let* (eparams,params) :=
        translate_runtime_params typ_names parameters in
      let arrowtype := {|paramargs:=params; rtrns:=cub_ret|} in
      let method := (name, (List.length type_params, List.map snd eparams, arrowtype)) in
      (* TODO come up with better naming scheme for externs *)
      let d := Top.Extern "_" 0 [] [] [method] in
      ok (add_extern ctx d)
  | DeclVariable _ typ {| P4String.str := x  |} None =>
      let+ t := translate_exp_type [] typ in
      add_variable ctx (Ctrl.Var x (inl t))
    | DeclVariable _ typ {| P4String.str := x |}  (Some e) =>
        let* t := translate_exp_type [] typ in
        let+ e := translate_expression [] term_names e in
        add_variable ctx (Ctrl.Var x (inr e))
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
        let term_names :=
          (List.map fst ctrl_params ++ List.map fst data_params ++ term_names)%list in
        let+ cub_body :=
          translate_block
            [] term_names 
            ctx body in
        let a :=
          Ctrl.Action
            cub_name ctrl_params data_params cub_body in
        add_action ctx a
    | DeclTable
        tags name keys actions entries
        default_action size custom_properties =>
        (* TODO High prio *)
        let name := P4String.str name in
        let* cub_keys :=
          translate_keys
            [] (term_names ++ get_variables ctx) keys in
        let+ cub_actions := translate_actions ctx term_names actions in
        (* TODO: correct default action:
           needs to split to get control-plane args *)
         add_table ctx (Ctrl.Table name cub_keys cub_actions None)
    | DeclHeader tags name fields =>
        (* error "[FIXME] Header Declarations unimplemented" *)
        let+ fs := translate_decl_fields [] fields in
        let t := Typ.Struct true fs in
        add_type ctx (P4String.str name) t
    | DeclHeaderUnion tags name fields =>
        (* error "[FIXME] Header Union Declarations unimplemented" *)
        ok ctx
    | DeclStruct tags name fields =>
        let+ fs := translate_decl_fields [] fields in
        let t := Typ.Struct false fs in
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
        let typ_names := List.map P4String.str type_params in
        let str_name := P4String.str name in
        let+ (cparams,expr_cparams,cub_methods) :=
          translate_methods typ_names methods in
        let d :=
          Top.Extern
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
      (cub_name, (cub_cparams, List.map snd cub_expr_cparams)) in
    add_package_type ctx p
    end.

  Fixpoint inline_types_decls (decls : list Declaration) : result string (list Declaration) :=
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
  Definition translate_decls (decls : list (@Declaration tags_t)) : result string DeclCtx :=
    let loop acc decl :=
      let* ctx := acc in
      translate_decl [] ctx decl in
    fold_left loop decls (ok (empty_declaration_context)).

  Definition
    seq_opt
    (d : Top.t) (r : option (Top.t)) : list Top.t :=
    match r with
    | None => [d]
    | Some rst => [d; rst]
    end.

  Definition preprocess (tags : tags_t) p :=
    let p := SimplExpr.transform_prog tags p in
    let+ p := hoist_nameless_instantiations tags_t p in
    let  p := inline_constants p in
    let '(_,p) := inline_typ_program Maps.IdentMap.empty p in
    p.

  Fail Definition inline_cub_types (decls : DeclCtx) :=
    fold_left (fun acc '(x,t) => subst_type acc x t) (decls.(types)) decls.

  Definition infer_member_types (decl : DeclCtx) :=
    let infer_ds := List.map InferMemberTypes.inf_top in
    let infer_Cds := List.map InferMemberTypes.inf_Cd in
    let infer_pts := Field.map (fun '(cparams,ts) =>
                                  (cparams, (* TODO: infer member types? *) ts)) in
    {| variables := infer_Cds decl.(variables);
       controls := infer_ds decl.(controls);
       parsers := infer_ds decl.(parsers);
       tables := infer_Cds decl.(tables);
       actions := infer_Cds decl.(actions);
       functions := infer_ds decl.(functions);
       package_types := infer_pts decl.(package_types);
       packages := infer_ds decl.(packages);
       externs := infer_ds decl.(externs);
       types := decl.(types);
    |}.

  Definition translate_program (tags : tags_t) (p : program) : result string DeclCtx :=
    let* '(Program decls) := preprocess tags p in
    let+ cub_decls := translate_decls decls in
    infer_member_types ((*inline_cub_types*) cub_decls).

  Definition translate_program' (tags : tags_t) (p : program) : result string (list Top.t) :=
    let+ ctx := translate_program tags p in 
    flatten_DeclCtx ctx.
    
End ToP4cub.
