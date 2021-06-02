Require Import Poulet4.P4cub.Metamorphosis.
Require Import Poulet4.Monads.Error.
Require Import Poulet4.P4cub.Syntax.P4Field.
Require Import Coq.Strings.String.
Require Import Poulet4.P4automata.Compiler.
Module S := P4cub.Stmt.
Module P := P4cub.Parser.
Module TD := P4cub.TopDecl.


Open Scope string_scope.
(* some utilities for converting between P4Light and P4Cub programs *)

Section ParserTranslation.
  Context (tags_t: Type).

  Definition decl_to_type 
    (d: @Declaration tags_t) 
    : @P4Type tags_t :=
    match d with 
    | DeclConstant _ t _ _ => t
    | DeclStruct tag _ ts => 
        let ftys := map (fun '(MkDeclarationField _ ty nme) => (nme, ty)) ts in 
        TypStruct ftys
    | _ => TypVoid
    end. 

  Fixpoint map_ty
    (f: @P4Type tags_t -> @P4Type tags_t)
    (ty: @P4Type tags_t)
    : @P4Type tags_t := 
    let recur := map_ty f in 
    let ty' := match ty with 
    | TypArray t sz => TypArray (recur t) sz
    | TypTuple ts => TypTuple (map recur ts)
    | TypList ts => TypTuple (map recur ts)
    | TypRecord fs => 
        let fs' := map (fun '(k, t) => (k, recur t)) fs in
        TypRecord fs'
    | TypSet t => TypSet (recur t)
    | TypHeader fs => 
        let fs' := map (fun '(k, t) => (k, recur t)) fs in
        TypHeader fs'
    | TypHeaderUnion fs => 
        let fs' := map (fun '(k, t) => (k, recur t)) fs in
        TypHeaderUnion fs'
    | TypStruct fs => 
        let fs' := map (fun '(k, t) => (k, recur t)) fs in
        TypStruct fs'
    | TypFunction (MkFunctionType t_params params kind rty) => 
        let p_worker := 
              fun '(MkParameter o d ty dai p_name) => MkParameter o d (recur ty) dai p_name in 
        TypFunction (MkFunctionType t_params (map p_worker params) kind (recur rty))


    (* | TypBool
    | TypeName (name: P4String)
    | TypString
    | TypInteger
    | TypError
    | TypMatchKind
    | TypVoid
    | TypInt (width: nat)
    | TypBit (width: nat) 
    | TypEnum (name: P4String) (typ: option P4Type) (members: list P4String)
    | TypVarBit (width: nat)
    | TypControl (_: ControlType)
    | TypParser (_: ControlType)
    | TypExtern (extern_name: P4String)
    | TypNewType (name: P4String) (typ: P4Type)
    | TypAction (data_params: list P4Parameter) (ctrl_params: list P4Parameter)
    | TypTable (result_typ_name: P4String)
    | TypPackage (type_params: list P4String) (wildcard_params: list P4String)
                  (parameters: list P4Parameter)
    | TypSpecializedType (base: P4Type) (args: list P4Type)
    | TypConstructor (type_params: list P4String) (wildcard_params: list P4String)
                  (parameters: list P4Parameter) (ret: P4Type) *)
    | _ => ty
    end in 
    f ty'.

  Fixpoint map_expr
    (ft : @P4Type tags_t -> @P4Type tags_t)
    (fe: @Expression tags_t -> @Expression tags_t)
    (e: @Expression tags_t)
    : @Expression tags_t := 
    let recur := map_expr ft fe in 
    let 'MkExpression tag e ty loc := e in 
    let e' := 
      match e with 
      | ExpArrayAccess arr idx => ExpArrayAccess (recur arr) (recur idx)
      | ExpBitStringAccess bits lo hi => ExpBitStringAccess (recur bits) lo hi
      | ExpList vs => ExpList (map recur vs)
      | ExpUnaryOp o i => ExpUnaryOp o (recur i)
      | ExpBinaryOp o (l, r) => ExpBinaryOp o (recur l, recur r)
      | ExpCast to_ty i => ExpCast (map_ty ft to_ty) (recur i)
      | ExpExpressionMember i name => ExpExpressionMember (recur i) name
      | ExpTernary c t f => ExpTernary (recur c) (recur t) (recur f)
      | ExpFunctionCall f tys args => 
            let arg_worker := fun arg => option_map recur arg in 
            ExpFunctionCall (recur f) (map (map_ty ft) tys) (map arg_worker args)
      | ExpNamelessInstantiation t args => ExpNamelessInstantiation (map_ty ft t) (map recur args)
      | ExpMask i mask => ExpMask (recur i) (recur mask)
      (* | ExpRange (lo: Expression) (hi: Expression)
      | ExpBool (b: bool)
      | ExpInt (_: P4Int)
      | ExpString (_: P4String)
      | ExpName (_: @Typed.name tags_t) (loc: Locator)
      | ExpDontCare
      | ExpRecord (entries: list KeyValue)
      | ExpTypeMember (typ: @Typed.name tags_t) (name: P4String)
      | ExpErrorMember (_: P4String) *)
      | _ => e
      end in 
    fe (MkExpression tag e' (map_ty ft ty) loc).

  Fixpoint map_stmt
    (fe: @Expression tags_t -> @Expression tags_t)
    (ft: @P4Type tags_t -> @P4Type tags_t)
    (fs : @Statement tags_t -> @Statement tags_t)
    (s: @Statement tags_t) 
    : @Statement tags_t :=
    let recur := map_stmt fe ft fs in 
    let 'MkStatement t inner ty := s in 
    let fix block_worker (b: Block) := 
      match b with 
      | BlockEmpty t => BlockEmpty t
      | BlockCons s r => BlockCons (recur s) r
      end in  
    let inner' := 
      match inner with 
      | StatMethodCall f ty_args args => 
          let f' := map_expr ft fe f in 
          let args' := map (option_map (map_expr ft fe)) args in 
          StatMethodCall f' (map (map_ty ft) ty_args) args'
      | StatAssignment l r => StatAssignment (map_expr ft fe l) (map_expr ft fe r)
      | StatDirectApplication t args => 
          StatDirectApplication (map_ty ft t) (map (map_expr ft fe) args)
      | StatConditional c tru fls => 
          StatConditional (map_expr ft fe c) (recur tru) (option_map recur fls)
      | StatReturn (Some e) => StatReturn (Some (map_expr ft fe e))
      | StatConstant t n v l => StatConstant (map_ty ft t) n v l
      | StatVariable t n init l => 
          StatVariable (map_ty ft t) n (option_map (map_expr ft fe) init) l
      
      | StatBlock blk => StatBlock (block_worker blk)
      (* 
      | StatInstantiation t args name init => 
      | StatSwitch 
      | StatExit
      | StatEmpty *)
      | _ => inner
      end in 
    fs (MkStatement t inner' ty).

  
  (* Translating from P4light to P4cub is mostly straightforward, but there are several warts: 
  1) sometimes there are type decls that are not inlined, e.g. there will be a decl
      Definition struct_ty := DeclStruct ... a flat normal type ... 
      and expressions of type struct_ty will instead use the struct_ty's name
      using TypName.
      
      We handle this with an inlining pass.
  2) P4cub assumes that all constants have a definite width, while P4light casts from 
     infinite width constants to a particular width. 
     
     We handle this with a modest cast-elimination pass that replaces <5>(n) with 5wn
     and then by stripping all casts (this is probably unsound).
     
     *)
  Definition inline_decls_ty
    (env: P4String.AList tags_t (@P4Type tags_t))
    (ty: @P4Type tags_t)
    : @P4Type tags_t := 
    match ty with 
    | TypTypeName (BareName name) => 
        match AList.get env name with 
        | Some t' => t'
        | None => ty
        end
    | _ => ty
    end.

  Definition inline_none_casts (e: @Expression tags_t) : @Expression tags_t := 
    let 'MkExpression tag ei ty loc := e in 
    let ei' := 
      match ei with 
      | ExpCast to_ty (MkExpression tag' ei' tyi loc') => 
        let '(ei'', tyi') := 
          match to_ty, ei' with 
          (* TODO: these two cases are basically the same except for the snd part of width_signed, refactor  *)
          | TypBit w, ExpInt p4i => 
            match P4Int.width_signed p4i with 
            | None => 
              (ExpInt {| P4Int.tags := P4Int.tags p4i; P4Int.value := P4Int.value p4i; P4Int.width_signed := Some (w, false); |}, to_ty)
            | _ => (ExpInt p4i, tyi)
            end
          | TypInt w, ExpInt p4i => 
            match P4Int.width_signed p4i with 
            | None => 
              (ExpInt {| P4Int.tags := P4Int.tags p4i; P4Int.value := P4Int.value p4i; P4Int.width_signed := Some (w, true); |}, to_ty)
            | _ => (ExpInt p4i, tyi)
            end
          | _, _ => (ei', tyi)
          end in 
        ExpCast to_ty (MkExpression tag' ei'' tyi' loc')
      | _ => ei
      end in 
    MkExpression tag ei' ty loc.

  Definition strip_casts (e: @Expression tags_t) : @Expression tags_t := 
    let 'MkExpression tag ei ty loc := e in 
    match ei with 
    | ExpCast to_ty x => x
    | _ => e
    end.

  Definition map_trans 
    (ft: @P4Type tags_t -> @P4Type tags_t) 
    (fe: @Expression tags_t -> @Expression tags_t)
    (p: @ParserTransition tags_t) : @ParserTransition tags_t  :=  
    let map_match := fun '(MkMatch tag m ty) => 
      let m' := 
        match m with 
        | MatchExpression e => MatchExpression (map_expr ft fe e)
        | _ => m
        end in 
      MkMatch tag m' (map_ty ft ty) in
    let map_case := fun '(MkParserCase tag matches next) => 
      MkParserCase tag (map map_match matches) next in  
    match p with 
    | ParserSelect tag exprs cases =>
      ParserSelect tag (map (map_expr ft fe) exprs) (map map_case cases)
    | _ => p
    end.
  
  Definition states_to_cub 
    (decl_env : P4String.AList tags_t (@P4Type tags_t))
    (ss: list (@ParserState tags_t)) 
    : @error_monad MorphError (F.fs string (P.state_block tags_t)) :=
    let ty_trans := inline_decls_ty decl_env in 
    let expr_trans := map_expr ty_trans (fun e => strip_casts (inline_none_casts e)) in 
    let stmt_trans := map_stmt expr_trans ty_trans id in 
    let s_worker := fun '(MkParserState tag name ss' trans) => 
      let ss'' := map stmt_trans ss' in 
      MkParserState tag name ss'' (map_trans ty_trans expr_trans trans) in
    sequence (map (fun s => parser_state_morph (s_worker s)) ss).

  Definition get_start 
    (states: F.fs string (P.state_block tags_t))
    : @error_monad (@MorphError tags_t) (P.state_block tags_t) := 
    match Field.find_value (fun s => s ==b "start") states with 
    | Some x => mret x
    | None => err $ Inconceivable "could not find start state"
    end.

  Definition decl_to_cub 
    (decl_env : P4String.AList tags_t (@P4Type tags_t))
    (p: @Declaration tags_t)
    : @error_monad MorphError (TD.d tags_t) :=
    match p with 
    (* ignores locals and params, TODO *)
    | DeclParser tag name _ _ _ _ states => 
      cub_states <- states_to_cub decl_env states ;; 
      start <- get_start cub_states ;;
      mret (TD.TPParser (P4String.str name) nil nil start cub_states tag)
    | _ => err $ Inconceivable "translating a non-parser decl"
    end. 

  Definition decl_to_autos 
    (decl_env : P4String.AList tags_t (@P4Type tags_t))
    (p: @Declaration tags_t) := 
    td <- decl_to_cub decl_env p ;; 
    let out := sequence (topdecl_to_p4automata _ td) in 
    match out with 
    | None => err $ Inconceivable "automata compiler error"
    | Some xs => mret xs
    end.
  
    
End ParserTranslation.