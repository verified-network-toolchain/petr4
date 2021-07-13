From compcert Require Import Clight Ctypes Integers Cop.
From compcert Require AST.
Require Import Poulet4.P4cub.Syntax.Syntax.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.PArith.BinPos.
Require Import Poulet4.P4cub.Envn.
Require Import Poulet4.Monads.Monad.
Require Import Poulet4.Monads.Option.
Require Import Poulet4_Ccomp.CCompEnv.
Require Import List.
Require Import Coq.ZArith.BinIntDef.
Require Import String.
Require Import Poulet4_Ccomp.Helloworld.
Open Scope string_scope.
Open Scope list_scope.
Module P := P4cub.
Module F := P.F.
Module E := P.Expr.
Module ST := P.Stmt.
Module PA := P.Parser.
Module CT := P.Control.
Module TD := P.TopDecl.
Parameter print_Clight: Clight.program -> unit.
(** P4Cub -> Clight **)
Section CComp.
  
  Context (tags_t: Type).
  Notation tpdecl := (P4cub.TopDecl.d tags_t).
  (*map between string and ident*)
  Definition identMap : Type := Env.t string AST.ident.
    (*TODO: implement integers with width larger than 64
      and optimize integers with width smaller than 32 *)
  Notation long_unsigned := (Tlong Unsigned noattr).
  Notation long_signed := (Tlong Signed noattr).
  Notation int_unsigned := (Tint I32 Unsigned noattr).
  Notation int_signed := (Tint I32 Signed noattr).
  Import P4cub.P4cubNotations.
  Fixpoint CTranslateType (p4t : E.t) (env: ClightEnv) : Ctypes.type * ClightEnv:=
    match p4t with
    | {{Bool}} => (Ctypes.type_bool, env)
    | {{bit < w >}} => (long_unsigned,env)
    | {{int < w >}} => (long_signed, env)
    | {{error}} => (Ctypes.Tvoid, env) (*what exactly is an error type?*)
    | {{matchkind}} => (Ctypes.Tvoid, env) (*TODO: implement*)
    | {{tuple ts}} => (Ctypes.Tvoid, env) (*TODO: implement*)
    | {{struct { fields } }}
    | {{hdr { fields } }} => 
        match lookup_composite env p4t with
        | Some comp => (Ctypes.Tstruct (Ctypes.name_composite_def comp) noattr, env)
        | None => 
        let (env_top_id, top_id) := CCompEnv.new_ident env in
        let (members ,env_fields_declared):= 
        F.fold 
        (fun (k: string) (field: E.t) (cumulator: Ctypes.members*ClightEnv) 
        => let (members_prev, env_prev) := cumulator in 
           let (new_t, new_env):= CTranslateType field env_prev in
           let (new_env, new_id):= CCompEnv.new_ident new_env in
           ((new_id, new_t) :: members_prev, new_env))
        fields ([],env_top_id) in
        let comp_def := Ctypes.Composite top_id Ctypes.Struct members Ctypes.noattr in
        let env_comp_added := CCompEnv.add_composite_typ env_fields_declared p4t comp_def in
        (Ctypes.Tstruct top_id noattr, env_comp_added)
        end

    | {{stack fields [n]}}=> (Ctypes.Tvoid, env) (*TODO: implement*)
    end.
  (* Definition CubTypeOf (e : E.e tags_t) : E.t.
    Admitted.
  Definition CTranslateCast (e: Clight.expr) (typefrom typeto: E.t) (env: ClightEnv) 
  : option (Clight.expr * ClightEnv).
      Admitted. *)
  
  Definition CTranslateSlice (x: Clight.expr) (hi lo: positive) (type: E.t) (env: ClightEnv)
  : option (Clight.expr * ClightEnv) := 
    (* x[hi : lo] = [x >> lo] & (1<<(hi-lo+1) - 1)*)
    let hi' := Econst_int (Integers.Int.repr (Zpos hi)) (int_unsigned) in
    let lo' := Econst_int (Integers.Int.repr (Zpos lo)) (int_unsigned) in
    let one' := Econst_long (Integers.Int64.one) (long_unsigned) in
    Some (Ebinop Oand (Ebinop Oshr x lo' long_unsigned) 
          (Ebinop Osub (Ebinop Oshl one' (Ebinop Oadd one' 
          (Ebinop Osub hi' lo' long_unsigned) long_unsigned) long_unsigned) 
            (one') long_unsigned) long_unsigned, env).
  
  (* TODO: figure out what cast rules does clight support and then implement this*)
  (* See https://opennetworking.org/wp-content/uploads/2020/10/P416-Language-Specification-wd.html#sec-casts *)
  
  (* input is an expression with tags_t and an idents map,
     output would be statement list , expression, needed variables/temps (in ident) and their corresponding types*)
  Fixpoint CTranslateExpr (e: E.e tags_t) (env: ClightEnv)
    : option (Clight.expr * ClightEnv) :=
    
    match e with
    | <{TRUE @ i}> =>   Some (Econst_int (Integers.Int.one) (type_bool), env)
    | <{FALSE @ i}> =>  Some (Econst_int (Integers.Int.zero) (type_bool), env)
    (*currently all integers (bit strings) are represented by long*)
    | <{w W n @ i}> =>  if (Pos.leb w (Pos.of_nat 64))
                        then Some (Econst_long (Integers.Int64.repr n) (long_unsigned), env)
                        else None 
    | <{w S n @ i}> =>  if (Pos.leb w (Pos.of_nat 64))
                        then Some(Econst_long (Integers.Int64.repr n) (long_signed), env)
                        else None
    | <{Var x : ty @ i}> => (*first find if x has been declared. If not, declare it by putting it into vars*)
                        let (cty, env_ty) := CTranslateType ty env in
                        match find_ident_temp_arg env_ty x with (*first look for if this is an argument and has its own temp for copy in/out *)
                        | Some (_,tempid) => Some (Etempvar tempid cty, env_ty)
                        | None =>
                        match find_ident env_ty x with
                        | Some id => Some (Evar id cty, env_ty)
                        | None => let env' := add_var env_ty x cty in
                                  match find_ident env' x with
                                  | Some id' => Some (Evar id' cty, env')
                                  | None => None
                                  end
                        end
                        end 
    | <{Slice n : τ [ hi : lo ] @ i}> => 
                        match CTranslateExpr n env with
                        | Some (n', env') => (CTranslateSlice n' hi lo τ env')
                        | _ => None
                        end
    | <{Cast e : τ @ i}> => None
                        (* match CTranslateExpr e env with
                        | Some (e', env') => let typefrom := (CubTypeOf e) in 
                                      (CTranslateCast e' typefrom τ env')
                        | _ => None
                        end *)
    | <{UOP op x : ty @ i}> => 
                        let (cty, env_ty) := CTranslateType ty env in
                        match CTranslateExpr x env_ty with
                        | None => None
                        | Some (x', env') => 
                          match op with
                          | _{!}_ => Some (Eunop Onotbool x' cty, env')
                          | _{~}_ => Some (Eunop Onotint x' cty, env')
                          | _{-}_ => Some (Eunop Oneg x' cty, env')
                          | _{isValid}_ => None (*TODO: *)
                          | _{setValid}_ => None (*TODO: *)
                          | _{setInValid}_ => None (*TODO: *)
                          | _{Next}_ => None (*TODO: *)
                          | _{Size}_ => None (*TODO: *)
                          | _{Push n}_ => None (*TODO: *)
                          | _{Pop n}_ => None (*TODO: *)
                          end
                        end
    | <{BOP x : tx op y : ty @ i}> =>
                        let (ctx, env_tx) := CTranslateType tx env in
                        let (cty, env_ty) := CTranslateType ty env_tx in 
                        match CTranslateExpr x env_ty with
                        | None => None
                        | Some (x', env') =>  
                          match CTranslateExpr y env' with
                          | None => None
                          | Some (y', env'') => 
                            match op with
                            | +{+}+ =>  Some (Ebinop Oadd x' y' ctx, env'')
                            | +{-}+ =>  Some (Ebinop Osub x' y' ctx, env'')
                            | +{|+|}+ =>None
                            | +{|-|}+ =>None
                            | E.Times =>  Some (Ebinop Omul x' y' ctx, env'')
                            | +{<<}+ => Some (Ebinop Oshl x' y'  ctx, env'')
                            | +{>>}+ => Some (Ebinop Oshr x' y' ctx, env'')
                            | +{<=}+ => Some (Ebinop Ole x' y' type_bool, env'')                         
                            | +{>=}+ => Some (Ebinop Oge x' y' type_bool, env'')
                            | +{<}+ =>  Some (Ebinop Olt x' y' type_bool, env'')
                            | +{>}+ =>  Some (Ebinop Ogt x' y' type_bool, env'')
                            | +{==}+ => Some (Ebinop Oeq x' y' type_bool, env'')
                            | +{!=}+ => Some (Ebinop One x' y' type_bool, env'')
                            | +{&&}+
                            | +{&}+ =>  Some (Ebinop Oand x' y' ctx, env'')
                            | +{^}+ =>  Some (Ebinop Oxor x' y' ctx, env'')
                            | +{||}+
                            | +{|}+ =>  Some (Ebinop Oor x' y' ctx, env'')
                            | +{++}+ => (*x ++ y = x<< widthof(y) + y*)
                                        let shift_amount := Econst_long (Integers.Int64.repr (Z.of_nat (SynDefs.width_of_typ ty))) long_unsigned in 
                                        Some (Ebinop Oadd (Ebinop Oshl x' shift_amount ctx) y' ctx, env'')
                            end
                          end
                        end
    | <{tup es @ i}> => None (*first create a temp of this tuple. then assign all the values to it. then return this temp *) 
    | <{struct { fields } @ i}> => None (*first create a temp of this struct. then assign all the values to it. then return this temp *)
                        
    | <{hdr { fields } valid := b @ i}> => None (*first create a temp of this header. then assign all the values to it. then return this temp*)
    | <{Mem x : ty dot y @ i}> => 
                        let(cty, env_ty):= CTranslateType ty env in
                        match CTranslateExpr x env_ty with
                        | None => None
                        | Some (x', env') =>
                          match ty with
                          | E.TStruct(f)
                          | E.THeader(f) => 
                            match F.get_index y f, F.get y f with
                            | Some n , Some t_member => 
                              let (ctm, env_ctm) := CTranslateType t_member env' in
                              Some ((Clight.Efield x' (Pos.of_nat n) ctm), env_ctm)
                            | _, _ => None
                            end
                          | _ => None
                          end
                        end

    (* | Error x @ i => *)
    (* | Matchkind mk @ i => *)
    (* | Stack hdrs : ts [ n ] nextIndex := ni @ i => *)
    (* | Access e1 [ e2 ] @ i =>  *)
    | _ =>  None
    end.

  Definition CTranslateExprList (el : list (E.e tags_t)) (env: ClightEnv): option ((list Clight.expr) * ClightEnv) :=
    let Cumulator: Type := option (list Clight.expr * ClightEnv) in 
    let transformation (A: Cumulator) (B: E.e tags_t) : Cumulator := 
      match A with
      |None => None
      |Some (el', env') => 
      match CTranslateExpr B env' with
      |None => None
      |Some (B', env'') => Some(el' ++ [B'], env'')
      end end in
    List.fold_left  (transformation) el (Some ([],env)).
  
  Definition CTranslateDirExprList (el: E.args tags_t) (env: ClightEnv) : option ((list Clight.expr) * ClightEnv) := 
    let Cumulator : Type := option (list Clight.expr * ClightEnv) in 
    let transformation (A: Cumulator) (B: string * (P.paramarg (E.t*(E.e tags_t)) (E.t*(E.e tags_t)))) : Cumulator := 
      match A with
      |None => None
      |Some (el', env') =>
      match B with 
      | (_, P.PAIn(t, e)) => 
        match CTranslateExpr e env' with 
        | None => None
        | Some (e', env'') => Some (el' ++ [e'], env'')
        end
      | (_, P.PAOut(t, e)) 
      | (_, P.PAInOut(t, e)) =>
        let (ct, env_ct):= CTranslateType t env' in 
        match CTranslateExpr e env_ct with 
        | None => None
        | Some (e', env'') => 
        let e' := Eaddrof e' (Tpointer ct noattr) in 
        Some (el' ++ [e'], env'')
        end
      end
      end
    in 
    List.fold_left  (transformation) el (Some ([],env)).
  
  Fixpoint CTranslateStatement (s: ST.s tags_t) (env: ClightEnv) : option (Clight.statement * ClightEnv) :=
    match s with
    | -{skip @ i}- => Some (Sskip, env)
    | -{s1;s2 @ i}- => match CTranslateStatement s1 env with
                       |None => None
                       |Some(s1', env1) => 
                       match CTranslateStatement s2 env1 with
                       |None => None
                       |Some(s2', env2) =>
                       Some (Ssequence s1' s2', env2)
                       end end
    | -{b{s}b}- => CTranslateStatement s env
    | -{var x : t @ i}- => 
                      let (cty, env_cty):= CTranslateType t env in
                      Some (Sskip, CCompEnv.add_var env_cty x cty)
    | -{asgn e1 := e2 : t @ i}- => match CTranslateExpr e1 env with
                                   |None => None
                                   |Some(e1', env1) => 
                                   match CTranslateExpr e2 env1 with
                                   |None => None
                                   |Some(e2', env2) =>
                                   Some (Sassign e1' e2', env2)
                                   end end
    | -{if e : t then s1 else s2 @ i}- => match CTranslateExpr e env with
                                          |None => None
                                          |Some(e', env1) =>
                                          match CTranslateStatement s1 env1 with
                                          |None => None
                                          |Some(s1', env2) =>
                                          match CTranslateStatement s2 env2 with
                                          |None => None
                                          |Some(s2', env3) =>
                                          Some(Sifthenelse e' s1' s2', env3)
                                          end end end
    | -{calling f with args @ i}- 
    | -{call f with args @ i}- => match CCompEnv.lookup_function env f with
                                  |None => None
                                  |Some(f', id) =>
                                    match CTranslateDirExprList args env with
                                    | None => None
                                    | Some (elist, env') => 
                                    Some(Scall None (Evar id (Clight.type_of_function f')) elist, env')
                                    end 
                                  end 
    | -{let e : t := call f with args @ i}- =>
                                  let (ct, env_ct) := CTranslateType t env in
                                  match CCompEnv.lookup_function env_ct f with
                                  |None => None
                                  |Some(f', id) =>
                                    match CTranslateDirExprList args env_ct with
                                    | None => None
                                    | Some (elist, env') => 
                                    let (env', tempid) := CCompEnv.add_temp_nameless env' ct in
                                    match CTranslateExpr e env' with 
                                    | None => None
                                    | Some (lvalue, env') =>
                                    Some(
                                      (Ssequence 
                                      (Scall (Some tempid) (Evar id (Clight.type_of_function f')) elist)
                                      (Sassign lvalue (Etempvar tempid ct) ))
                                      , 
                                      env')
                                    end
                                    end 
                                  end 
    
    (* | -{extern e calls f with args gives x @ i}- *)
    | -{return e : t @ i}- => match CTranslateExpr e env with
                              | None => None
                              | Some (e', env') => Some ((Sreturn (Some e')), env')
                              end
    | -{returns @ i}- => Some (Sreturn None, env)
    (* | -{exit @ i}- *)
    (* | -{apply x with args @ i}- *)
    (* | -{invoke tbl @ i}- => None *)
    | _ => None
    end.

  Definition CTranslateParserState (st : PA.state_block tags_t) (env: ClightEnv) (params: list (AST.ident * Ctypes.type)): option (Clight.function * ClightEnv) :=
  match st with
  | &{state {stmt} transition pe}& => 
  match CTranslateStatement stmt env with
    | None => None
    | Some(stmt', env') =>
    match pe with 
    | p{goto st @ i}p => 
      match st with
      | ={start}= =>
        match (lookup_function env' "start") with
        | None => None
        | Some (start_f, start_id) =>
        Some (Clight.mkfunction
          Ctypes.Tvoid
          (AST.mkcallconv None true true)
          params
          (CCompEnv.get_vars env')
          (CCompEnv.get_temps env')
          (Ssequence stmt'
          (Scall None (Evar start_id (Clight.type_of_function start_f)) []))
          , env')
        end
      | ={accept}= =>
        Some (Clight.mkfunction
          Ctypes.Tvoid
          (AST.mkcallconv None true true)
          params
          (CCompEnv.get_vars env')
          (CCompEnv.get_temps env')
          (Ssequence stmt' (Sreturn None))
          , env') 
      | ={reject}= => None (*TODO: implement*)
      | ={δ x}= => 
      match lookup_function env' x with
      | None => None
      | Some (x_f, x_id) =>
      Some (Clight.mkfunction
          Ctypes.Tvoid
          (AST.mkcallconv None true true)
          params
          (CCompEnv.get_vars env')
          (CCompEnv.get_temps env')
          (Ssequence stmt'
          (Scall None (Evar x_id (Clight.type_of_function x_f)) []))
          , env')
      end
      end
    | p{select exp { cases } default := def @ i}p => None (*unimplemented*)
  end
  end
  end.

  Definition CTranslateParams (params : E.params) (env : ClightEnv) 
  : list (AST.ident * Ctypes.type) * ClightEnv :=
  List.fold_left 
    (fun (cumulator: (list (AST.ident * Ctypes.type))*ClightEnv) (p: string * P.paramarg E.t E.t)
    =>let (l, env') := cumulator in
      let (env', new_id) := new_ident env' in
      let (ct,env_ct) := match p with 
        | (_, P.PAIn x) => (CTranslateType x env')
        | (_, P.PAOut x)
        | (_, P.PAInOut x) => let (ct', env_ct') := CTranslateType x env' in
                         (Ctypes.Tpointer ct' noattr, env_ct')
      end in
      let s := fst p in
      let env_temp_added := add_temp_arg env_ct s ct new_id in  (*the temps here are for copy in copy out purpose*)
      ((new_id, ct) :: l, env_temp_added)) 
  (params) ([],env)
  . 

  (*try to do copy in copy out*)
  Definition CCopyIn (fn_params: E.params) (env: ClightEnv)
  : Clight.statement * ClightEnv:= 
  List.fold_left 
    (fun (cumulator: Clight.statement * ClightEnv) (fn_param: string * (P.paramarg E.t E.t))
    =>let (name, t) := fn_param in 
      let (prev_stmt, prev_env) := cumulator in
      match find_ident_temp_arg env name with
      | None => cumulator
      | Some (oldid, tempid) => 
        match t with
        | P.PAIn t
        | P.PAOut t
        | P.PAInOut t => 
        let (ct, env_ct) := CTranslateType t prev_env in
        let new_stmt := Sassign (Evar tempid ct) (Evar oldid ct) in
        (Ssequence prev_stmt new_stmt, env_ct)
        end
      end
    ) fn_params (Sskip, env).

Definition CCopyOut (fn_params: E.params) (env: ClightEnv)
  : Clight.statement * ClightEnv:= 
  List.fold_left 
    (fun (cumulator: Clight.statement * ClightEnv) (fn_param: string * (P.paramarg E.t E.t))
    =>let (name, t) := fn_param in 
      let (prev_stmt, prev_env) := cumulator in
      match find_ident_temp_arg env name with
      | None => cumulator
      | Some (oldid, tempid) => 
        match t with
        | P.PAIn t
        | P.PAOut t
        | P.PAInOut t => 
        let (ct, env_ct) := CTranslateType t prev_env in
        let new_stmt := Sassign (Evar oldid ct) (Evar tempid ct) in
        (Ssequence prev_stmt new_stmt, env_ct)
        end
      end
    ) fn_params (Sskip, env).


Definition CTranslateArrow (signature : E.arrowT) (env : ClightEnv)
  : (list (AST.ident * Ctypes.type)) * Ctypes.type * ClightEnv 
  := 
  match signature with 
  | P.Arrow pas ret =>
   let (fn_params, env_params_created) := CTranslateParams pas env in 
   match ret with 
   | None => (fn_params, Ctypes.Tvoid, env_params_created)
   | Some return_t => let (ct, env_ct):= CTranslateType return_t env_params_created in 
                      (fn_params, ct , env_ct)
   end
  end.
    
Definition PaFromArrow (arrow: E.arrowT) : (E.params):=
  match arrow with
  | P.Arrow pas ret => 
  pas
  end.

Definition CTranslateTopParser (parsr: TD.d tags_t) (env: ClightEnv): option (ClightEnv)
  :=
  match parsr with
  | %{parser p (cparams) (params) start := st {states} @ i}% =>
    (*ignore constructor params for now*)
    
    let (fn_params, env):= CTranslateParams params env in
    let (copyin, env) := CCopyIn params env in 
    let (copyout, env) := CCopyOut params env in
    let state_names := F.keys states in 
    let env_fn_sig_declared := 
      (*all functions inside one top parser declaration should have the same parameter*)
      let fn_sig := 
      (Clight.mkfunction 
      Ctypes.Tvoid 
      (AST.mkcallconv None true true) 
      fn_params
      []
      []
      Sskip ) in
      let env_start_fn_sig_declared := 
        CCompEnv.add_function env "start" fn_sig
      in
      List.fold_left 
        (fun (cumulator : ClightEnv) (state_name: string) =>
          CCompEnv.add_function cumulator state_name fn_sig
        ) state_names  env_start_fn_sig_declared in
    
    let env_fn_declared := 
      List.fold_left
      (fun (cumulator: option ClightEnv) (state_name: string)
      => match cumulator with | None => None | Some env' =>
        match Env.find state_name states with | None => None |Some sb =>
        match CTranslateParserState sb env' fn_params with | None => None | Some (f , _) =>
        Some (CCompEnv.update_function env' state_name f)
        end end end
      ) state_names (Some env_fn_sig_declared) in
    (*finished declaring all the state blocks except start state*)
    match env_fn_declared with |None => None |Some env_fn_declared =>
    match CTranslateParserState st env_fn_declared fn_params with 
    | None => None 
    | Some (f_start, _)=>
      let env_start_declared := CCompEnv.add_function env_fn_declared "start" f_start in
      match (lookup_function env_start_declared "start") with
      | None => None
      | Some (start_f, start_id) =>
      let fn_body := 
      Ssequence copyin 
      (Ssequence 
      (Scall None (Evar start_id (Clight.type_of_function start_f)) [])
       copyout) in 
      let top_function := 
        (Clight.mkfunction
        Ctypes.Tvoid
        (AST.mkcallconv None true true)
        fn_params
        []
        []
        fn_body)
      in
      let env_topfn_added := CCompEnv.add_function env_start_declared p top_function in
      Some(env_topfn_added)
        
      end end end 

  | _ => None
  end.


  Definition CTranslateAction 
  (signature: E.params) (body: ST.s tags_t) 
  (env: ClightEnv) (top_fn_params: list (AST.ident * Ctypes.type))
  (top_signature: E.params)
  : option Clight.function:= 
  let (fn_params, env_params_created) := CTranslateParams signature env in
  let fn_params := top_fn_params ++ fn_params in 
  let full_signature := top_signature ++ signature in
  let (copyin, env_copyin) := CCopyIn full_signature env_params_created in
  let (copyout, env_copyout) := CCopyOut full_signature env_copyin in
  match CTranslateStatement body env_copyout with
  | None => None 
  | Some (c_body, env_body_translated) =>
    let body:= Ssequence copyin (Ssequence c_body copyout) in
    Some(
      (Clight.mkfunction 
        Ctypes.Tvoid
        (AST.mkcallconv None true true)
        fn_params 
        (get_vars env_body_translated)
        (get_temps env_body_translated)
        body))
  end.
  Fixpoint CTranslateControlLocalDeclaration 
  (ct : CT.ControlDecl.d tags_t) (env: ClightEnv) 
  (top_fn_params: list (AST.ident * Ctypes.type))
  (top_signature: E.params)
  : option (ClightEnv)
  := match ct with
  | c{d1 ;c; d2 @i}c => 
    match (CTranslateControlLocalDeclaration d1 env top_fn_params top_signature) with
    | None => None
    | Some (env1) =>
      match (CTranslateControlLocalDeclaration d2 env1 top_fn_params top_signature) with 
      | None => None
      | Some (env2) => Some (env2)
      end
    end
  | c{action a (params) {body} @ i}c => 
    match CTranslateAction params body env top_fn_params top_signature with
    | None => None
    | Some f => Some (CCompEnv.add_function env a f)
    end
  | c{table t key := ems actions := acts @ i}c => Some env (*TODO: implement table*)
  end.
  
  Definition CTranslateTopControl (ctrl: TD.d tags_t) (env: ClightEnv): option (ClightEnv)
  := 
  match ctrl with
  | %{control c (cparams) (params) apply {blk} where {body} @ i}%
    => (*ignoring constructor params for now*)
       let (fn_params, env_top_fn_param) := CTranslateParams params env in
       let (copyin, env_copyin) := CCopyIn params env_top_fn_param in 
       let (copyout, env_copyout) := CCopyOut params env_copyin in 
       match CTranslateControlLocalDeclaration body env_copyout fn_params params with 
       | None => None
       | Some env_local_decled => 
        match CTranslateStatement blk env_local_decled with
        | None => None
        | Some (apply_blk, env_apply_block_translated)=>
          let body:= Ssequence copyin (Ssequence apply_blk copyout) in
          let top_fn := Clight.mkfunction 
          Ctypes.Tvoid 
          (AST.mkcallconv None true true)
          fn_params 
          (get_vars env_apply_block_translated)
          (get_temps env_apply_block_translated)
          body in
          let env_top_fn_declared := 
          CCompEnv.add_function env_local_decled c top_fn in
          Some (env_top_fn_declared) 
        end
       end
  | _ => None
  end.


  
  Definition CTranslateFunction 
  (funcdecl : TD.d tags_t)
  (env: ClightEnv)
  : option ClightEnv:= 
  match funcdecl with
  | TD.TPFunction name signature body _ => 
    match CTranslateArrow signature env with 
    |(fn_params, fn_return, env_params_created) =>
      let paramargs := PaFromArrow signature in
      let (copyin, env_copyin) := CCopyIn paramargs env_params_created in
      let (copyout, env_copyout) := CCopyOut paramargs env_copyin in
      match CTranslateStatement body env_copyout with
      | None => None 
      | Some (c_body, env_body_translated) =>
        let body:= Ssequence copyin (Ssequence c_body copyout) in
        let top_function := 
          (Clight.mkfunction 
            fn_return
            (AST.mkcallconv None true true)
            fn_params 
            (get_vars env_body_translated)
            (get_temps env_body_translated)
            body) in
        Some (CCompEnv.add_function env_params_created name top_function)
      end
    end 
  | _ => None
  end.

  Fixpoint CTranslateTopDeclaration (d: tpdecl) (env: ClightEnv) : option ClightEnv
  := 
  match d with
  | %{d1 ;%; d2 @ i}% => 
    match CTranslateTopDeclaration d1 env with
    | None => None
    | Some env1 => 
      match CTranslateTopDeclaration d2 env1 with
      | None => None
      | Some env2 => Some env2
      end end
  | %{Instance x of c (args) @i }% => Some env (*TODO: implement*) 
  | %{void f (params) {body} @i }% => CTranslateFunction d env
  | %{fn f (params) -> t {body} @i }% => CTranslateFunction d env
  | %{extern e (cparams) {methods} @i }% => None (*TODO: implement*)
  | %{control c (cparams) (params) apply {blk} where {body} @ i}% => CTranslateTopControl d env
  | %{parser p (cparams) (params) start := st {states} @ i}% => CTranslateTopParser d env
  | %{package _ (_) @ _}% => None (*TODO: implement*)
  end.
  (* currently just an empty program *)
  Definition Compile (prog: tpdecl) : Errors.res (Clight.program) := 
    let main_decl : AST.globdef (fundef function) type :=
      AST.Gfun (Ctypes.Internal (Clight.mkfunction 
        Ctypes.Tvoid 
        (AST.mkcallconv None true true)
        []
        []
        []
        Sskip
      ))
    in
    let init_env := CCompEnv.newClightEnv in
    let (init_env, main_id) := CCompEnv.new_ident init_env in 
    match CTranslateTopDeclaration prog init_env with
    | None => Errors.Error (Errors.msg "something went wrong")
    | Some env_all_declared => 
      match CCompEnv.get_functions env_all_declared with
      | None => Errors.Error (Errors.msg "can't find all the declared functions")
      | Some f_decls => 
      let f_decls := List.map 
        (fun (x: AST.ident * Clight.function) 
        => let (id, f) := x in 
        (id, AST.Gfun(Ctypes.Internal f))) f_decls in
      let typ_decls := CCompEnv.get_composites env_all_declared in 
      let res_prog : Errors.res (program function) := make_program 
        typ_decls ((main_id, main_decl):: f_decls) [] main_id
      in
      res_prog
      end
    end.

  Definition Compile_print (prog: tpdecl): unit := 
    match Compile prog with
    | Errors.Error e => tt
    | Errors.OK prog => print_Clight prog
    end.  
End CComp.
Definition test := CComp.Compile nat helloworld_program.


