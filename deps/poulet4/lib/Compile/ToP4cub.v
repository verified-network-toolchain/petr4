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
     Monads.Result
     (*P4cub.Semantics.Dynamic.BigStep.InstUtil*).
Import AST Result Envn ResultNotations.
From Coq Require Import ZArith.BinInt.

Require Import String.
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

Definition list_of_opts_map {A B : Type} (f : A -> B) (opt_as : list (option A)) :=
  List.map (option_map f) opt_as.

Fixpoint commute_result_optlist {A : Type} (l : list (option (result A))) : result (list (option A)) :=
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
        package_types : Field.fs string (list string * list TopDecl.it);
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

  Definition add_package_type (decl : DeclCtx) pt :=
    decl <| package_types := pt::decl.(package_types) |>.

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
    let matches := String.eqb name in
    match d with
    | TopDecl.Instantiate _ _ _ => false
    | TopDecl.Extern extern_name _ _ _ => matches extern_name
    | TopDecl.Control control_name _ _ _ _ _ => matches control_name
    | TopDecl.Parser parser_name _ _ _ _ _ => matches parser_name
    | TopDecl.Funct function_name _ _ _ => matches function_name
    end.

  Definition cdecl_has_name (name : string) (d : Control.d) :=
    let matches := String.eqb name in
    match d with
    | Control.Action action_name _ _ _ => matches action_name
    | Control.Table table_name _ _ => matches table_name
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

  Definition realize_array_index (e : @Expression tags_t) : result nat :=
    match e with
    | MkExpression _ (ExpInt z) _ _  =>
      (*TODO Do we have to do some normalizaztion here?*)
      ok (BinInt.Z.abs_nat z.(value))
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
    (f_str : string) (params : list (paramarg E.t E.t))
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
    | param::params', (Some arg)::args' =>
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
    (name : string) (ctx : DeclCtx) : result (TopDecl.constructor_params) :=
    match lookup_instantiatable ctx name with
    | Some (TopDecl.Parser _ cparams _ _ _ _)  =>
        ok cparams
    | Some (TopDecl.Control _ cparams _ _ _ _) =>
        ok cparams
    | Some (TopDecl.Extern _ _ cparams _) =>
        ok cparams
    | Some (_) =>
        error ("Dont kow how to get constructors for " ++ name)
    | None =>
        match List.find (String.eqb name ∘ fst) ctx.(package_types) with
        | Some (_, (_ , cparams)) =>
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
      | TypArray typ _ =>
          match typ with
          | TypStruct fields
          | TypHeader fields =>
              let+ cub_fields := translate_fields fields in
              E.TStruct cub_fields false
          | TypTypeName s =>
              error
                ("Typerror:: Arrays must contain headers, got type variable: "
                   ++ @P4String.str tags_t s)
          | TypNewType s _ =>
              error
                ("Typerror:: Arrays must contain headers, got type variable: "
                   ++ @P4String.str tags_t s)
          | _ => error "Typeerror:: Arrays must contain Headers"
          end
      | TypTuple types
      (* TODO ensure are cast-able *)
      | TypList types =>
          let+ cub_types :=
            types
              ▷ List.map translate_exp_type
              ▷ sequence in
          E.TStruct cub_types false
      | TypRecord fields
      | TypStruct fields =>
          let+ fields' := translate_fields fields in
          E.TStruct fields' false
      | TypSet elt_type =>
          (* Shows up in typechecking a select *)
          error "A set is not an expression type"
      | TypError => ok E.TError
      | TypMatchKind =>
          error "A matchkind is not an expression type"
      | TypVoid => error "[FIXME] void is not the type of any expression literal"
      | TypHeader fields =>
          let+ fields' := translate_fields fields in
          E.TStruct fields' true
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
                let* x :=
                  Result.from_opt
                    (ListUtil.index_of string_dec x term_names)
                    ("Unbound name " ++ x) in
                let+ cub_type := translate_exp_type typ in
                E.Var cub_type x
            | QualifiedName namespaces name =>
                error "Qualified names should be eliminated"
            end
        | ExpArrayAccess array index =>
            let* cub_typ := translate_exp_type typ in
            match cub_typ, get_type_of_expr array with
            | Expr.TStruct header_type true, TypArray _ size =>
                let* stck := translate_expression array in
                let~ index := realize_array_index index over "Failed to realize array index" in
                ok (header_stack_access header_type (BinNat.N.to_nat size) index stck)
            | _, _ => error "TypeError :: Elements of array access do not have expected types"
            end
        | ExpBitStringAccess bits lo hi =>
            let* typ := translate_exp_type (get_type_of_expr bits) in
            let+ e := translate_expression bits in
            (* Positive doesnt let you represent 0, so increase each by one*)
            (* Make sure to check ToGCL.to_rvalue when changing *)
            E.Slice e (posN (BinNatDef.N.succ hi)) (posN (BinNatDef.N.succ lo))
        | ExpList values =>
            let+ cub_values :=
              values
                ▷ List.map translate_expression
                ▷ sequence in
            E.Struct cub_values None
        | ExpRecord entries =>
            let+ cub_entries :=
              entries
                ▷ List.map (fun '(_,expr) => translate_expression expr)
                ▷ sequence in
            E.Struct cub_entries None
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
                 '(MkParameter _ dir typ _ _ : @P4Parameter tags_t)
        : result (paramarg E.t E.t) :=
        let+ t := translate_exp_type typ in
        match dir with
        | Directionless
        | In => PAIn t
        | Out => PAOut t
        | InOut => PAInOut t
        end.

      Definition parameters_to_params (parameters : list (@P4Parameter tags_t))
        : result (list (paramarg E.t E.t)) :=
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
        let* (params : list (paramarg E.t E.t)) := parameters_to_params parameters in
        apply_args_to_params callee params cub_args.

      Variable instance_names : list string.
      
      Definition translate_apply callee args ret_var ret_type : result ST.s :=
        let typ := get_type_of_expr callee in
        match typ with
        | TypControl (MkControlType type_params parameters) =>
            let* callee_name := get_name callee in
            let callee_name_string := P4String.str callee_name in
            let* cub_inst_name :=
              Result.from_opt
                (ListUtil.index_of string_dec callee_name_string instance_names)
                ("TypeError :: instance name " ++ callee_name_string ++ " not found") in
            let+ paramargs := translate_application_args callee_name_string parameters args in
            ST.Apply cub_inst_name [] paramargs
        | TypTable _ =>
            let* callee_name := get_name callee in
            let callee_string := P4String.str callee_name in
            let+ cub_name :=
              Result.from_opt
                (ListUtil.index_of string_dec callee_string term_names)
                ("TypeError :: name " ++ callee_string ++ "not found.") in
            (* TODO make this an EExprMember *)
            match ret_var, ret_type with
            | Some rv, Some rt =>
                let switch_expr := E.Var rt rv in
                let action_run_var := E.Var rt cub_name in
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
        | Some rv =>
            ok (ST.Assign (E.Var E.TBool rv)
                          (E.Uop E.TBool E.IsValid hdr))
        end.
      
      Definition translate_extern_string (ctx : DeclCtx) (extern_str f_str : string) args :=
        let extern_decl :=  find (decl_has_name extern_str) ctx.(externs) in
        match extern_decl with
        | None => error ("ERROR expected an extern, but got " ++ extern_str)
        | Some (TopDecl.Extern extn_name tparams cparams methods) =>
            let called_method := find (fun '(nm, _) => String.eqb nm f_str) methods in
            match called_method with
            | None =>
                error ("Couldn't find " ++ extern_str ++ "." ++ f_str)
            | Some (_, (targs, ar)) =>
                let params := paramargs ar in
                let* cub_args := translate_arglist args in
                let+ args := apply_args_to_params f_str params cub_args in
                (* TODO Currently assuming method calls return None*)
                (* TODO: need to find extern instance name *)
                ST.Call (ST.Method 0 f_str [] None) args
            end
        | Some _ =>
            error "Invariant Violated. Declaration Context Extern list contained something other than an extern."
        end.

      Definition translate_expression_member_call
                 (args : list (option (@Expression tags_t)))
                 (ctx : DeclCtx)
                 (callee : Expression)
                 (ret_var : option nat)
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
                             let* cub_type := translate_exp_type typ in
                             match cub_type with
                             | Expr.TStruct header_type true =>
                                 ok (op header_type (BinNat.N.to_nat n) num_ops hdr_stack)
                             | _ => error "TypeError :: expected to have header stack type"
                             end
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
        (ret_var : nat) (ret_type : E.t) : option (result ST.s) :=
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
                         n (Some (Expr.Var ret_type ret_var)) type_args parameters args
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
      (term_names instance_names : list string)
      ctx (match_expr : E.e) (bits : N)
      (tenum : list (P4String.t tags_t)) (acc : (option E.e) * (ST.s -> ST.s))
      (ssw : @StatementSwitchCase tags_t) : result ((option E.e) * (ST.s -> ST.s)) :=
      (* break apart the accumulation into the aggregated condition and the aggregated if-then continuation *)
      let '(cond_opt, ifthen) := acc in
      (* Force the agggregated conditional to be a boolean *)
      let acc_cond := SyntaxUtil.force (E.Bool false) cond_opt in
      (* Build the case match by building the label index check and or-ing the aggregated conditional *)
      let case_match := fun label =>
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
                  term_names instance_names
                  ctx block in
              let else__ifthen : ST.s -> ST.s := fun else_ => ST.Conditional cond st else_ in
              (* The continuation is still "open" *)
              ok (None, ifthen ∘ else__ifthen)
          | StatSwLabDefault tags =>
              let* else_ :=
                translate_block
                  term_names instance_names
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
           (term_names instance_names : list string)
           (ctx : DeclCtx) (pre_s : @StatementPreT tags_t) : result ST.s :=
           match pre_s with
           | StatMethodCall func type_args args =>
               let '(MkExpression tags func_pre typ dir) := func in
               match func_pre with
               | ExpExpressionMember callee f =>
                   translate_expression_member_call
                     term_names instance_names
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
                                 term_names instance_names ctx tru in
               let+ cub_fls := match fls_opt with
                               | None => ok ST.Skip
                               | Some fls =>
                                   translate_statement term_names instance_names ctx fls
                               end in
               ST.Conditional cub_cond cub_tru cub_fls
           | StatBlock block =>
               translate_block term_names instance_names ctx block
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
                                     term_names instance_names
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
           (instance_names term_names : list string)
           (ctx : DeclCtx) (s : @Statement tags_t) : result ST.s :=
           match s with
           | MkStatement _ stmt _ =>
               translate_statement_pre_t
                 instance_names
                 term_names ctx stmt
           end
    with translate_block
           (instance_names term_names : list string)
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
                   instance_names ctx blk in
               ST.Var (inl t) s
           | BlockCons
               (MkStatement
                  _ (StatVariable
                       t {| P4String.str := x|} (Some e) _) _) blk =>
               let* t := translate_exp_type t in
               match function_call_init
                       term_names
                       instance_names
                       ctx e 0 t with
               | None =>
                   let* e := translate_expression term_names e in
                   let+ s :=
                     translate_block
                       (x :: term_names)
                       instance_names
                       ctx blk in
                   ST.Var (inr e) s
               | Some call =>
                   let* call := call in
                   let+ s :=
                     translate_block
                       (x :: term_names)
                       instance_names
                       ctx blk in
                   ST.Var (inl t) (ST.Seq call s)
               end 
           | BlockCons statement rest =>
               let* s1 :=
                 translate_statement
                   term_names instance_names
                   ctx statement in
               let+ s2 :=
                 translate_block
                   term_names instance_names
                   ctx rest in
               ST.Seq s1 s2
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

  Definition translate_pre_expr (tags : tags_t) pre_expr : result (Parser.pat) :=
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
      | _ => error ("ints must have a known width: " ++ string_of_nat (BinInt.Z.to_nat z.(value)))
      end
    | _ => error "unknown set variant"
    end.

  Definition translate_expression_to_pattern (e : @Expression tags_t) : result (Parser.pat) :=
    let '(MkExpression tags pre_expr typ dir) := e in
    @translate_pre_expr tags pre_expr.

  Definition translate_match (m : Match) : result (Parser.pat) :=
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
      @translate_pre_expr tags (ExpCast typ m)
    end.

  Definition translate_matches (ms : list Match) : result (list Parser.pat) :=
    rred (List.map translate_match ms).

  Definition
    translate_parser_case
    (pcase : @ParserCase tags_t)
    : result (Parser.e tags_t + (Parser.pat * Parser.e tags_t)) :=
    let '(MkParserCase tags matches next) := pcase in
    let transition := Parser.PGoto (translate_state_name next) tags in
    let+ patterns := translate_matches matches in
    if total_wildcard patterns
    then inl transition
    else inr (Parser.Tuple patterns, transition).

  Definition translate_parser_case_loop pcase acc :=
    let* (def_opt, cases) := acc in
    let+ cub_case := translate_parser_case pcase in
    match cub_case with
    | inl x => (Some x, cases)
    | inr y => (def_opt, y::cases)
    end.

    (* TODO ASSUME default is the last element of case list *)
  Definition translate_cases (tags : tags_t) (cases : list (@ParserCase tags_t)) : result (Parser.e tags_t * Field.fs Parser.pat (Parser.e tags_t)) :=
    let* (def_opt, cases) := List.fold_right translate_parser_case_loop (ok (None, [])) cases in
    let def := SyntaxUtil.force (Parser.PGoto Parser.STReject tags) def_opt in
    ok (def, cases).

  Definition translate_transition (transition : ParserTransition) : result (Parser.e tags_t) :=
    match transition with
    | ParserDirect tags next =>
      let next_state := translate_state_name next in
      ok (Parser.PGoto next_state tags)
    | ParserSelect tags exprs cases =>
      let* type_expr_list := rred (List.map (translate_expression_and_type tags) exprs) in
      let expr_list := List.map snd type_expr_list in
      let+ (default, cub_cases) := translate_cases tags cases in
      Parser.PSelect (E.Tuple expr_list tags) default cub_cases tags
    end.

  Definition translate_statements (ctx : DeclCtx) (tags : tags_t) (statements : list Statement) : result ST.s :=
    fold_left (fun res_acc s => let* cub_s := translate_statement ctx s in
                                 let+ acc := res_acc in
                                 ST.Seq cub_s acc tags)
              statements
              (ok (ST.Skip tags)).

  Definition translate_parser_state (ctx : DeclCtx) (pstate : ParserState) : result (string * Parser.state_block tags_t) :=
    let '(MkParserState tags name statements transition) := pstate in
    let* ss := translate_statements ctx tags statements in
    let+ trans := translate_transition transition in
    let parser_state := {| Parser.stmt := ss; Parser.trans := trans |} in
    (P4String.str name, parser_state).

  Definition translate_parser_states_inner (ctx : DeclCtx) (p : ParserState) (res_acc : result ((option (Parser.state_block tags_t)) * Field.fs string (Parser.state_block tags_t))) :=
    let* (nm, state) := translate_parser_state ctx p in
    let+ (start_opt, states) := res_acc in
    if String.eqb nm "start"
    then (Some state, (nm, state)::states)
    else (start_opt, (nm, state)::states).

  Definition translate_parser_states (ctx : DeclCtx) (pstates : list ParserState) : result (option (Parser.state_block tags_t) * Field.fs string (Parser.state_block tags_t)) :=
    fold_right (translate_parser_states_inner ctx) (ok (None, [])) pstates.

  Definition translate_constructor_arg_expression (arg : @Expression tags_t) : result E.e :=
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

  Definition translate_instantiation_args (ps : E.constructor_params) (es : list E.e) : result (E.constructor_args tags_t) :=
    let~ param_args := zip ps es over ("zipping instantiation args failed. there were " ++ string_of_nat (List.length ps) ++ "params and " ++ string_of_nat (List.length es) ++ "args") in
    (* FIXME Something is wrong here. We should be disambiguating here between CAExpr and CAName *)
    List.fold_right (fun '((str, typ), e) (acc_r : result (E.constructor_args tags_t)) =>
                       let* acc := acc_r in
                       match e with
                       | E.Var (E.TVar s) nm _ =>
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

  Definition translate_methods (ext_name : P4String.t tags_t) (ms : list MethodPrototype) : result (Field.fs string (list string * E.arrowT)) :=
    rred (List.map (translate_method ext_name) ms).

  Definition translate_action_params tags data_params ctrl_params :=
    let* cub_data_params := parameters_to_params tags data_params in
    let+ cub_ctrl_params := parameters_to_params tags ctrl_params in
    (* TODO ensure ctrl params are directionless? *)
    append cub_data_params cub_ctrl_params.

  Definition translate_matchkind (matchkind : P4String.t tags_t) : result E.matchkind :=
    let mk_str := P4String.str matchkind in
    if String.eqb mk_str "lpm"
    then ok E.MKLpm
    else if String.eqb mk_str "ternary"
         then ok E.MKTernary
         else if String.eqb mk_str "exact"
              then ok E.MKExact
              else error ("Matchkind not supported by P4cub: " ++ mk_str).

  Definition translate_key (key : TableKey) : result (E.e * E.matchkind) :=
    let '(MkTableKey tags key_exp matchkind) := key in
    let* e := translate_expression key_exp in
    let+ mk := translate_matchkind matchkind in
    (e, mk).

  Definition translate_keys_loop (key : TableKey) (acc : result (list (E.e * E.matchkind))) : result (list (E.e * E.matchkind)) :=
    let* cub_key := translate_key key in
    let+ cub_keys := acc in
    cub_key :: cub_keys.

  Definition translate_keys (keys : list TableKey) : result (list (E.e * E.matchkind)) :=
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


  Definition translate_decl_fields (fields : list DeclarationField) : result (Field.fs string E.t) :=
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
      let cub_name := P4String.str name in
      let* ctor_p4string := get_string_from_type typ in
      let ctor_name := P4String.str ctor_p4string in
      let* cub_paramargs := constructor_paramargs ctor_name args ctx in
      let* type_args := get_cub_type_args tags typ in
      let d := TopDecl.Instantiate ctor_name cub_name type_args cub_paramargs tags in
      let+ add_to_context := get_augment_from_name ctx ctor_name in
      add_to_context d
    | DeclParser tags name _ params constructor_params _ states =>
        let cub_name := P4String.str name in
        let* (cub_eparams,cub_cparams) := partition_constructor_params tags constructor_params in
        let* cub_params := parameters_to_params tags params in
        let* (start_opt, cub_states) := translate_parser_states ctx states in
        let*~ cub_start := start_opt else "could not find a starting state for the parser" in
        let d := TopDecl.Parser cub_name cub_cparams cub_eparams cub_params cub_start cub_states tags in
        ok (add_parser ctx d)
    | DeclControl tags name type_params params constructor_params locals apply_blk =>
      let cub_name := P4String.str name in
      let* (cub_eparams, cub_cparams) := partition_constructor_params tags constructor_params in
      let* cub_params := parameters_to_params tags params in
      let* local_ctx :=
         let loop := fun acc decl => let* ctx := acc in
                                     translate_decl ctx decl in
         fold_left loop locals (ok ctx)
      in
      (* This step loses information about local instantiations *)
      let cub_body := to_ctrl_decl tags local_ctx in
      let+ cub_block := translate_block local_ctx tags apply_blk in
      (* Lift body decls & rename occurences in d *)
      let d := TopDecl.Control cub_name cub_cparams cub_eparams cub_params cub_body cub_block tags in
      (* THIS IS CERTAINLY WRONG *)
      add_control local_ctx d
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
      let d := TopDecl.Extern "_" [] [] [method] tags in
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
      let* cub_signature := translate_action_params tags data_params ctrl_params in
      let+ cub_body := translate_block ctx tags body in
      let a := Control.Action cub_name cub_signature cub_body tags in
      add_action ctx a
    | DeclTable tags name keys actions entries default_action size custom_properties =>
      (* TODO High prio *)
      let name := P4String.str name in
      let* cub_keys := translate_keys keys in
      let+ cub_actions := translate_actions actions in
      let table := {| Control.table_key := cub_keys; Control.table_actions:= cub_actions|} in
      let t := Control.Table name table tags in
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
      let+ (cub_methods : Field.fs string (list string * Expr.arrowT)) := translate_methods name methods in
      let cparams := match List.find (String.eqb str_name ∘ fst) cub_methods with
                     | None => []
                     | Some (_, (_, ar)) => Field.map (E.CTType ∘ extract_type) ar.(paramargs)
                     end in
      let cub_type_params := List.map P4String.str type_params in
      let d := TopDecl.Extern str_name cub_type_params cparams cub_methods tags in
      add_extern ctx d
    | DeclTypeDef tags name (inl typ) =>
      let+ typ := translate_exp_type tags typ in
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
      let cub_type_params := List.map (@P4String.str tags_t) type_params in
      let+ cub_params := translate_constructor_parameters tags parameters in
      let p :=  (cub_name, (cub_type_params, cub_params, tags)) in
      add_package_type ctx p
      (* error "[FIXME] P4light inlining step necessary" *)
  end.

  Fixpoint inline_types_decls decls :=
    match decls with
    | [] => ok []
    | d::decls =>
      let+ decls' := inline_types_decls decls in
      match substitution_from_decl d with
      | None => d::decls'
      | Some σ =>
        let decls'' := List.map (@substitute_typ_Declaration tags_t σ) decls' in
        d :: decls''
      end
    end.

  Definition inline_types_prog '(Program decls) :=
    let+ decls' := inline_types_decls decls in
    Program decls'.

  (* This is redunant with the locals resolution in the previous code, but I
   * can't get it to compile using mutual fixpoints *)
  Definition translate_decls (decls : list (@Declaration tags_t)) : result DeclCtx :=
    let loop := fun acc decl => let* ctx := acc in
                                translate_decl ctx decl in
    fold_left loop decls (ok (empty_declaration_context)).

  Definition seq_opt (i : tags_t) (d : TopDecl.d) (r : option (TopDecl.d)) : option (TopDecl.d) :=
    match r with
    | None => Some d
    | Some rst => Some (TopDecl.Seq d rst i)
    end.

  Definition preprocess (tags : tags_t) p :=
    let* hoisted_simpl := hoist_nameless_instantiations tags_t (SimplExpr.transform_prog tags p) in
    inline_types_prog hoisted_simpl.

  Definition inline_cub_types (decls : DeclCtx) :=
    fold_left (fun acc '(x,t) => subst_type acc x t) (decls.(types)) decls.

  Definition infer_member_types (decl : DeclCtx) :=
    let infer_ds := List.map InferMemberTypes.inf_d in
    let infer_Cds := List.map InferMemberTypes.inf_Cd in
    let infer_pts := Field.map (fun '(tparams,cparams, t) =>
                                 (tparams, Field.map InferMemberTypes.inf_cparam cparams, t)) in
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
    infer_member_types (inline_cub_types cub_decls).

  Definition translate_program' (tags : tags_t) (p : program) : result (TopDecl.d) :=
    let* ctx := translate_program tags p in 
    flatten_DeclCtx ctx.
    
End ToP4cub.
