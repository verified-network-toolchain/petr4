From compcert Require Import Clight Ctypes Integers Cop.
From compcert Require AST.
Require Import Poulet4.P4cub.Syntax.Syntax.
Require Import Poulet4.P4cub.Envn.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.PArith.BinPos.
Require Import Poulet4.P4sel.P4sel.
Require Import Poulet4.Monads.Monad.
Require Import Poulet4.Monads.Option.
Require Poulet4.P4sel.RemoveSideEffect.
Require Import Poulet4.Ccomp.CCompEnv.
Require Import Poulet4.Ccomp.Helloworld.
Require Import Poulet4.Ccomp.CV1Model.
Require Import List.
Require Import Coq.ZArith.BinIntDef.
Require Import String.
Require Coq.PArith.BinPosDef.
Open Scope string_scope.
Open Scope list_scope.
Module P := P4sel.
Module F := P.F.
Module E := P.Expr.
Module ST := P.Stmt.
Module PA := P.Parser.
Module CT := P.Control.ControlDecl.
Module TD := P.TopDecl.
Parameter print_Clight: Clight.program -> unit.
(** P4Sel -> Clight **)
Section CCompSel.
  
  Context (tags_t: Type).
  (*map between string and ident*)
    (*TODO: implement integers with width larger than 64
      and optimize integers with width smaller than 32 *)
  Definition long_unsigned := (Tlong Unsigned noattr).
  Definition long_signed := (Tlong Signed noattr).
  Definition int_unsigned := (Tint I32 Unsigned noattr).
  Definition int_signed := (Tint I32 Signed noattr).
  Definition bit_vec := 
    (Tstruct (Pos.of_nat 3) noattr).
  Definition packet_in := 
    (Tstruct (Pos.of_nat 1) noattr).
  Definition packet_out :=
    (Tstruct (Pos.of_nat 2) noattr).
  Fixpoint CTranslateType (p4t : P4cub.Expr.t) (env: ClightEnv tags_t) : Ctypes.type * ClightEnv tags_t:=
    match p4t with
    | P4cub.Expr.TBool => (Ctypes.type_bool, env)
    | P4cub.Expr.TBit (w) => (bit_vec,env)
    | P4cub.Expr.TInt (w) => (bit_vec, env)
    | P4cub.Expr.TVar name => (Ctypes.Tvoid, env) (*TODO: implement*)
    | P4cub.Expr.TError => (Ctypes.Tvoid, env) (*TODO: implement what exactly is an error type?*)
    | P4cub.Expr.TMatchKind => (Ctypes.Tvoid, env) (*TODO: implement*)
    | P4cub.Expr.TTuple (ts) => (Ctypes.Tvoid, env) (*TODO: implement*)
    | P4cub.Expr.TStruct (fields) => 
        match lookup_composite tags_t env p4t with
        | Some comp => (Ctypes.Tstruct (Ctypes.name_composite_def comp) noattr, env)
        | None => 
        let (env_top_id, top_id) := CCompEnv.new_ident tags_t env in
        let (members ,env_fields_declared):= 
        F.fold 
        (fun (k: string) (field: E.t) (cumulator: Ctypes.members*ClightEnv tags_t) 
        => let (members_prev, env_prev) := cumulator in 
           let (new_t, new_env):= CTranslateType field env_prev in
           let (new_env, new_id):= CCompEnv.new_ident tags_t new_env in
           (members_prev ++ [(new_id, new_t)], new_env))
        fields ([],env_top_id) in
        let comp_def := Ctypes.Composite top_id Ctypes.Struct members Ctypes.noattr in
        let env_comp_added := CCompEnv.add_composite_typ tags_t env_fields_declared p4t comp_def in
        (Ctypes.Tstruct top_id noattr, env_comp_added)
        end
    | P4cub.Expr.THeader (fields) => 
    (* need a validity boolean value *)
        match lookup_composite tags_t env p4t with
        | Some comp => (Ctypes.Tstruct (Ctypes.name_composite_def comp) noattr, env)
        | None => 
        let (env_top_id, top_id) := CCompEnv.new_ident tags_t env in
        let (env_valid, valid_id) := new_ident tags_t env_top_id in 
        let (members ,env_fields_declared):= 
        F.fold 
        (fun (k: string) (field: E.t) (cumulator: Ctypes.members*ClightEnv tags_t ) 
        => let (members_prev, env_prev) := cumulator in 
           let (new_t, new_env):= CTranslateType field env_prev in
           let (new_env, new_id):= CCompEnv.new_ident tags_t new_env in
           (members_prev++[(new_id, new_t)], new_env))
        fields ([(valid_id, type_bool)],env_valid) in
        let comp_def := Ctypes.Composite top_id Ctypes.Struct members Ctypes.noattr in
        let env_comp_added := CCompEnv.add_composite_typ tags_t env_fields_declared p4t comp_def in
        (Ctypes.Tstruct top_id noattr, env_comp_added)
        end

    | P4cub.Expr.THeaderStack fields n=> (Ctypes.Tvoid, env) (*TODO: implement*)
    end.

  Definition CTranslateConstructorType (ct: P4cub.Expr.ct) (env: ClightEnv tags_t) : Ctypes.type * ClightEnv tags_t :=
  match ct with 
  | P4cub.Expr.CTType type => (Ctypes.Tvoid, env) (*TODO: implement*) 
  | P4cub.Expr.CTControl cparams _ parameters => (Ctypes.Tvoid, env) (*TODO: implement*)
  | P4cub.Expr.CTParser cparams  _ parameters => (Ctypes.Tvoid, env) (*TODO: implement*)
  | P4cub.Expr.CTPackage cparams => (Ctypes.Tvoid, env) (*TODO: implement*)
  | P4cub.Expr.CTExtern extern_name => 
    match extern_name with
    | "packet_in" => (packet_in,env)
    | "packet_out" => (packet_out, env)
    | _ => (Ctypes.Tvoid, env) (*TODO: implement*) 
    end
  end.
  
  Fixpoint CTranslateExpr (e: E.e tags_t) (env: ClightEnv tags_t )
    : option (Clight.expr * ClightEnv tags_t ) :=
    match e with
    | E.EBool true i =>   Some (Econst_int (Integers.Int.one) (type_bool), env)
    | E.EBool false i =>  Some (Econst_int (Integers.Int.zero) (type_bool), env)
    | E.EVar ty x i => (*first find if x has been declared. If not, declare it *)
                        let (cty, env_ty) := CTranslateType ty env in
                        match find_ident_temp_arg tags_t env_ty x with 
                        (*first look for if this is an argument and has its own temp for copy in/out *)
                        | Some (_,tempid) => Some (Etempvar tempid cty, env_ty)
                        | None =>
                        match find_ident tags_t env_ty x with
                        | Some id => Some (Evar id cty, env_ty)
                        | None => let env' := add_var tags_t env_ty x cty in
                                  match find_ident tags_t env' x with
                                  | Some id' => Some (Evar id' cty, env')
                                  | None => None
                                  end
                        end
                        end
    | E.EExprMember y ty x i => 
                        let(cty, env_ty):= CTranslateType ty env in
                        match CTranslateExpr x env_ty with
                        | None => None
                        | Some (x', env') =>
                          match ty with
                          | E.TStruct(f) =>
                            match F.get_index y f, F.get y f with
                            | Some n , Some t_member => 
                              let (ctm, env_ctm) := CTranslateType t_member env' in
                              Some ((Clight.Efield x' (Pos.of_nat n) ctm), env_ctm)
                            | _, _ => None
                            end
                          | E.THeader(f) => 
                          (* +1 for the valid bit *)
                            match F.get_index y f, F.get y f with
                            | Some n , Some t_member => 
                              let (ctm, env_ctm) := CTranslateType t_member env' in
                              Some ((Clight.Efield x' (Pos.of_nat (n+1)) ctm), env_ctm)
                            | _, _ => None
                            end
                          | _ => None
                          end
                        end 
    | E.EError x i => None (*TODO: implement*)
    | E.EMatchKind mk i => None (*TODO : implement*)
    
    end.

  Definition CTranslateExprList (el : list (E.e tags_t)) (env: ClightEnv tags_t ): option ((list Clight.expr) * ClightEnv tags_t ) :=
    let Cumulator: Type := option (list Clight.expr * ClightEnv tags_t ) in 
    let transformation (A: Cumulator) (B: E.e tags_t) : Cumulator := 
      match A with
      |None => None
      |Some (el', env') => 
      match CTranslateExpr B env' with
      |None => None
      |Some (B', env'') => Some(el' ++ [B'], env'')
      end end in
    List.fold_left  (transformation) el (Some ([],env)).
  
  Definition CTranslateDirExprList (el: E.args tags_t) (env: ClightEnv tags_t ) : option ((list Clight.expr) * ClightEnv tags_t ) := 
    let Cumulator : Type := option (list Clight.expr * ClightEnv tags_t ) in 
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
  

  Definition slice_function := 
    AST.EF_runtime "slice" (AST.mksignature
    [AST.Tptr; AST.Tptr; AST.Tptr; AST.Tptr]
    (AST.Tvoid)
    AST.cc_default
    ).
  Definition typelist_slice := 
    let Tpointer := Ctypes.Tpointer bit_vec noattr in 
    Ctypes.Tcons Tpointer 
    (Ctypes.Tcons Tpointer 
    (Ctypes.Tcons Tpointer 
    (Ctypes.Tcons Tpointer Ctypes.Tnil))).

  Definition uop_function (op: string) := 
    AST.EF_runtime op (AST.mksignature
    [AST.Tptr; AST.Tptr]
    (AST.Tvoid)
    AST.cc_default
    ).
  Definition typelist_uop := 
    let Tpointer := Ctypes.Tpointer bit_vec noattr in 
    Ctypes.Tcons Tpointer 
    (Ctypes.Tcons Tpointer Ctypes.Tnil).

  Definition bop_function (op: string) := 
    AST.EF_runtime op (AST.mksignature
    [AST.Tptr; AST.Tptr; AST.Tptr]
    (AST.Tvoid)
    AST.cc_default
    ).

  Definition typelist_bop_bitvec := 
    let Tpointer := Ctypes.Tpointer bit_vec noattr in 
    Ctypes.Tcons Tpointer 
    (Ctypes.Tcons Tpointer 
    (Ctypes.Tcons Tpointer
    Ctypes.Tnil)).

  Definition typelist_bop_bool := 
    let Tpointer := Ctypes.Tpointer bit_vec noattr in
    let TpointerBool := Ctypes.Tpointer type_bool noattr in  
    Ctypes.Tcons Tpointer 
    (Ctypes.Tcons Tpointer 
    (Ctypes.Tcons TpointerBool
    Ctypes.Tnil)).

  Definition ValidBitIndex (arg: E.e tags_t) (env: ClightEnv tags_t ) : option AST.ident
  :=
  match lookup_composite tags_t env (E.SelTypeOf tags_t arg) with
  | Some (Ctypes.Composite _ Ctypes.Struct m _)=>
  match m with
  | [] => None
  | (id,t) :: _ => Some id
  end
  | _ => None
  end.     


  Definition CTranslateUop 
  (dst_t: P4cub.Expr.t)
  (op: P4cub.Expr.uop)
  (arg: E.e tags_t)
  (dst: string)
  (env: ClightEnv tags_t ): option(Clight.statement * ClightEnv tags_t ) := 
  match find_ident tags_t env dst with
  | None => None
  | Some dst' => 
  let (dst_t', env') := CTranslateType dst_t env in 
  let dst' := Evar dst' dst_t' in
  match CTranslateExpr arg env' with
  | None => None
  | Some (arg', env_arg) =>
  let arg_ref := Eaddrof arg' (Tpointer (Clight.typeof arg') noattr) in
  let dst_ref := Eaddrof dst' (Tpointer dst_t' noattr) in  
  match op with
  | P4cub.Expr.Not => 
    let not_expr := Eunop Onotbool arg' Ctypes.type_bool in 
    Some (Sassign dst' not_expr, env_arg)
  | P4cub.Expr.BitNot => 
    Some (Sbuiltin None (uop_function "eval_bitnot") typelist_uop [arg_ref; dst_ref], env_arg)
  | P4cub.Expr.UMinus => 
    Some (Sbuiltin None (uop_function "eval_uminus") typelist_uop [arg_ref; dst_ref], env_arg)
  | P4cub.Expr.IsValid =>
    match ValidBitIndex arg env_arg with
    | None => None
    | Some index =>
    let member :=  Efield arg' index type_bool in
    Some (Sassign dst' member, env_arg)
    end
  | P4cub.Expr.SetValid =>
    match ValidBitIndex arg env_arg with
    | None => None
    | Some index =>
    let member :=  Efield arg' index type_bool in
    Some (Sassign member (Econst_int (Integers.Int.one) (type_bool)), env_arg)
    end
  | P4cub.Expr.SetInValid =>
    match ValidBitIndex arg env_arg with
    | None => None
    | Some index =>
    let member :=  Efield arg' index type_bool in
    Some (Sassign member (Econst_int (Integers.Int.zero) (type_bool)), env_arg)
    end
  | P4cub.Expr.NextIndex (*TODO:*)
  | P4cub.Expr.Size => None(*TODO:*)
  | P4cub.Expr.Push n(*TODO:*)
  | P4cub.Expr.Pop n => None(*TODO:*)
  end
  end
  end.

  Definition CTranslateBop 
  (dst_t: P4cub.Expr.t)
  (op: P4cub.Expr.bop)
  (le: E.e tags_t)
  (re: E.e tags_t)
  (dst: string)
  (env: ClightEnv tags_t ) : option (Clight.statement * ClightEnv tags_t )
  := 
  match find_ident tags_t env dst with
  | None => None
  | Some dst' => 
  let (dst_t', env') := CTranslateType dst_t env in 
  let dst' := Evar dst' dst_t' in
  match CTranslateExpr le env' with
  | None => None
  | Some (le', env_le) =>
  match CTranslateExpr re env_le with
  | None => None
  | Some (re', env_re) => 
  let le_ref := Eaddrof le' (Tpointer (Clight.typeof le') noattr) in
  let re_ref := Eaddrof re' (Tpointer (Clight.typeof re') noattr) in
  let dst_ref := Eaddrof dst' (Tpointer dst_t' noattr) in  
  let signed := 
  match dst_t with
  | P4cub.Expr.TInt _ => true
  | _ => false
  end in
  match op with
  | P4cub.Expr.Plus => 
  let fn_name := if signed then "eval_add_signed" else "eval_add_unsigned" in
  Some (Sbuiltin None (bop_function fn_name) typelist_bop_bitvec [le_ref; re_ref; dst_ref], env_re)
  | P4cub.Expr.PlusSat =>
  let fn_name := if signed then "eval_addsat_signed" else "eval_addsat_unsigned" in
  Some (Sbuiltin None (bop_function fn_name) typelist_bop_bitvec [le_ref; re_ref; dst_ref], env_re)
  | P4cub.Expr.Minus =>
  let fn_name := if signed then "eval_sub_signed" else "eval_sub_unsigned" in
  Some (Sbuiltin None (bop_function fn_name) typelist_bop_bitvec [le_ref; re_ref; dst_ref], env_re)
  | P4cub.Expr.MinusSat =>
  let fn_name := if signed then "eval_subsat_signed" else "eval_subsat_unsigned" in
  Some (Sbuiltin None (bop_function fn_name) typelist_bop_bitvec [le_ref; re_ref; dst_ref], env_re)
  | P4cub.Expr.Times =>
  let fn_name := if signed then "eval_mul_signed" else "eval_mul_unsigned" in
  Some (Sbuiltin None (bop_function fn_name) typelist_bop_bitvec [le_ref; re_ref; dst_ref], env_re)
  | P4cub.Expr.Shl =>
  Some (Sbuiltin None (bop_function "eval_shl") typelist_bop_bitvec [le_ref; re_ref; dst_ref], env_re)
  | P4cub.Expr.Shr =>
  Some (Sbuiltin None (bop_function "eval_shr") typelist_bop_bitvec [le_ref; re_ref; dst_ref], env_re)
  | P4cub.Expr.Le => 
  let fn_name := if signed then "eval_le_signed" else "eval_le_unsigned" in
  Some (Sbuiltin None (bop_function fn_name) typelist_bop_bool [le_ref; re_ref; dst_ref], env_re)
  | P4cub.Expr.Ge => 
  let fn_name := if signed then "eval_ge_signed" else "eval_ge_unsigned" in
  Some (Sbuiltin None (bop_function fn_name) typelist_bop_bool [le_ref; re_ref; dst_ref], env_re)
  | P4cub.Expr.Lt => 
  let fn_name := if signed then "eval_lt_signed" else "eval_lt_unsigned" in
  Some (Sbuiltin None (bop_function fn_name) typelist_bop_bool [le_ref; re_ref; dst_ref], env_re)
  | P4cub.Expr.Gt => 
  let fn_name := if signed then "eval_gt_signed" else "eval_gt_unsigned" in
  Some (Sbuiltin None (bop_function fn_name) typelist_bop_bool [le_ref; re_ref; dst_ref], env_re)
  | P4cub.Expr.Eq => 
  match Clight.typeof le' with
  | Tint IBool Signed noattr =>
  let eq_expr :=  Ebinop Oeq le' re' type_bool in
  Some (Sassign dst' eq_expr, env_re)
  | _ =>
  let fn_name := "eval_eq" in
  Some (Sbuiltin None (bop_function fn_name) typelist_bop_bool [le_ref; re_ref; dst_ref], env_re)
  end
  | P4cub.Expr.NotEq => 
  match Clight.typeof le' with
  | Tint IBool Signed noattr =>
  let eq_expr :=  Ebinop Oeq le' re' type_bool in
  Some (Sassign dst' eq_expr, env_re)
  | _ =>
  let fn_name := "eval_neq" in
  Some (Sbuiltin None (bop_function fn_name) typelist_bop_bool [le_ref; re_ref; dst_ref], env_re)
  end
  | P4cub.Expr.BitAnd => 
  Some (Sbuiltin None (bop_function "eval_bitand") typelist_bop_bitvec [le_ref; re_ref; dst_ref], env_re)
  | P4cub.Expr.BitXor => 
  Some (Sbuiltin None (bop_function "eval_bitxor") typelist_bop_bitvec [le_ref; re_ref; dst_ref], env_re)
  | P4cub.Expr.BitOr => 
  Some (Sbuiltin None (bop_function "eval_bitor") typelist_bop_bitvec [le_ref; re_ref; dst_ref], env_re)
  | P4cub.Expr.PlusPlus => 
  Some (Sbuiltin None (bop_function "eval_plusplus") typelist_bop_bitvec [le_ref; re_ref; dst_ref], env_re)
  | P4cub.Expr.And => 
  let and_expr :=  Ebinop Oand le' re' type_bool in
  Some (Sassign dst' and_expr, env_re)
  | P4cub.Expr.Or => 
  let or_expr :=  Ebinop Oor le' re' type_bool in
  Some (Sassign dst' or_expr, env_re)
  end
  end
  end
  end
  .
  


  Fixpoint CTranslateStatement (s: ST.s tags_t) (env: ClightEnv tags_t ) : option (Clight.statement * ClightEnv tags_t ) :=
    match s with
    | ST.SSkip i => Some (Sskip, env)
    | ST.SSeq s1 s2 i => match CTranslateStatement s1 env with
                       |None => None
                       |Some(s1', env1) => 
                       match CTranslateStatement s2 env1 with
                       |None => None
                       |Some(s2', env2) =>
                       Some (Ssequence s1' s2', env2)
                       end end
    | ST.SBlock s => CTranslateStatement s env
    | ST.SVardecl t x i => 
                      let (cty, env_cty):= CTranslateType t env in
                      Some (Sskip, CCompEnv.add_var tags_t env_cty x cty)
    | ST.SAssign t e1 e2 i => match CTranslateExpr e1 env with
                                   |None => None
                                   |Some(e1', env1) => 
                                   match CTranslateExpr e2 env1 with
                                   |None => None
                                   |Some(e2', env2) =>
                                   Some (Sassign e1' e2', env2)
                                   end end
    | ST.SConditional t e s1 s2 i => match CTranslateExpr e env with
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
    | ST.SFunCall f (P4cub.Arrow args None) i 
    | ST.SActCall f args i => match CCompEnv.lookup_function tags_t env f with
                                  |None => None
                                  |Some(f', id) =>
                                    match CTranslateDirExprList args env with
                                    | None => None
                                    | Some (elist, env') => 
                                    Some(Scall None (Evar id (Clight.type_of_function f')) elist, env')
                                    end 
                                  end 
    | ST.SFunCall f (P4cub.Arrow args (Some (t,e))) i =>
                                  let (ct, env_ct) := CTranslateType t env in
                                  match CCompEnv.lookup_function tags_t env_ct f with
                                  |None => None
                                  |Some(f', id) =>
                                    match CTranslateDirExprList args env_ct with
                                    | None => None
                                    | Some (elist, env') => 
                                    let (env', tempid) := CCompEnv.add_temp_nameless tags_t env' ct in
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
    
    | ST.SExternMethodCall e f (P4cub.Arrow args x) i => Some (Sskip, env) (*TODO: implement*)
    | ST.SReturnFruit t e i => match CTranslateExpr e env with
                              | None => None
                              | Some (e', env') => Some ((Sreturn (Some e')), env')
                              end
    | ST.SReturnVoid i => Some (Sreturn None, env)
    | ST.SExit i => Some (Sskip, env) (*TODO: implement*)
    | ST.SApply x args i => Some (Sskip, env) (*TODO: implement*)
    | ST.SInvoke tbl i => Some (Sskip, env) (*TODO: implement*)

    | ST.SBitAssign dst_t dst width val i => Some (Sskip, env) (*TODO: implement*)
    | ST.SIntAssign dst_t dst width val z => Some (Sskip, env) (*TODO: implement*)
    | ST.SSlice n τ hi lo dst i => 
                        match CTranslateExpr n env with
                        | None => None
                        | Some (n', env') =>
                        let hi' := Econst_int (Integers.Int.repr (Zpos hi)) (int_unsigned) in
                        let lo' := Econst_int (Integers.Int.repr (Zpos lo)) (int_unsigned) in
                        match find_ident tags_t env dst with 
                        | None => None
                        | Some dst' =>
                        let (tau', env') := CTranslateType τ env' in 
                        let dst' := Evar dst' tau' in
                        Some (Sbuiltin None slice_function typelist_slice [n'; hi'; lo'; dst'], env')
                        end
                        end

    | ST.SCast τ e dst i => None (*TODO:*)
                        
    | ST.SUop dst_t op x dst i => CTranslateUop dst_t op x dst env
    | ST.SBop dst_t op x y dst i => CTranslateBop dst_t op x y dst env
                        
    | ST.STuple es dst i => None (*first create a temp of this tuple. then assign all the values to it. then return this temp  *) 
    | ST.SStruct fields dst i => None (*first create a temp of this struct. then assign all the values to it. then return this temp *)
                        
    | ST.SHeader fields dst b i => None (*first create a temp of this header. then assign all the values to it. then return this temp*)
    

    
    
    (* | Stack hdrs : ts [ n ] nextIndex := ni @ i => *)
    (* | Access e1 [ e2 ] @ i =>  *)
    | _ =>  None
    end.

  Definition CTranslateParserState (st : PA.state_block tags_t) (env: ClightEnv tags_t ) (params: list (AST.ident * Ctypes.type)): option (Clight.function * ClightEnv tags_t ) :=
  match st with
  | PA.State stmt pe => 
  match CTranslateStatement stmt env with
    | None => None
    | Some(stmt', env') =>
    match pe with 
    | PA.PGoto st i => 
      match st with
      | P4cub.Parser.STStart =>
        match (lookup_function tags_t env' "start") with
        | None => None
        | Some (start_f, start_id) =>
        Some (Clight.mkfunction
          Ctypes.Tvoid
          (AST.mkcallconv None true true)
          params
          (CCompEnv.get_vars tags_t env')
          (CCompEnv.get_temps tags_t env')
          (Ssequence stmt'
          (Scall None (Evar start_id (Clight.type_of_function start_f)) [])) (*TODO: add args*)
          , env')
        end
      | P4cub.Parser.STAccept =>
        Some (Clight.mkfunction
          Ctypes.Tvoid
          (AST.mkcallconv None true true)
          params
          (CCompEnv.get_vars tags_t env')
          (CCompEnv.get_temps tags_t env')
          (Ssequence stmt' (Sreturn None))
          , env') 
      | P4cub.Parser.STReject => None (*TODO: implement*)
      | P4cub.Parser.STName x => 
      match lookup_function tags_t env' x with
      | None => None
      | Some (x_f, x_id) =>
      Some (Clight.mkfunction
          Ctypes.Tvoid
          (AST.mkcallconv None true true)
          params
          (CCompEnv.get_vars tags_t env')
          (CCompEnv.get_temps tags_t env')
          (Ssequence stmt'
          (Scall None (Evar x_id (Clight.type_of_function x_f)) [])) (*TODO: add args*)
          , (set_temp_vars tags_t env env'))
      end
      end
    | PA.PSelect exp def cases i => None (*unimplemented*)
  end
  end
  end.

  Definition CTranslateParams (params : E.params) (env : ClightEnv tags_t ) 
  : list (AST.ident * Ctypes.type) * ClightEnv tags_t  :=
  List.fold_left 
    (fun (cumulator: (list (AST.ident * Ctypes.type))*ClightEnv tags_t ) (p: string * P.paramarg E.t E.t)
    =>let (l, env') := cumulator in
      let (env', new_id) := new_ident tags_t env' in
      let (ct,env_ct) := match p with 
        | (_, P.PAIn x) 
        | (_, P.PAOut x)
        | (_, P.PAInOut x) => (CTranslateType x env')
      end in
      let ct_param := match p with 
      | (_, P.PAIn _) => ct
      | (_, P.PAOut x)
      | (_, P.PAInOut x) => Ctypes.Tpointer ct noattr
      end in
      let s := fst p in
      let env_temp_added := add_temp_arg tags_t env_ct s ct new_id in  (*the temps here are for copy in copy out purpose*)
      (l ++ [(new_id, ct_param)], env_temp_added)) 
  (params) ([],env)
  . 

  Definition CTranslateConstructorParams (cparams : P4cub.Expr.constructor_params) (env : ClightEnv tags_t)
  : list (AST.ident * Ctypes.type) * ClightEnv tags_t 
  := 
  List.fold_left 
    (fun (cumulator: (list (AST.ident * Ctypes.type)) * ClightEnv tags_t ) (p: string * P4cub.Expr.ct)
    =>let (l, env') := cumulator in
      let (env', new_id) := new_ident tags_t env' in
      let (pname, typ) := p in
      let (ct,env_ct) :=  (CTranslateConstructorType typ env') in
      (*currently don't do copy in copy out*)
      (l ++ [(new_id, ct)], env_ct)) 
  (cparams) ([],env) 
  .
  

  (*try to do copy in copy out*)
  Definition CCopyIn (fn_params: E.params) (env: ClightEnv tags_t )
  : Clight.statement * ClightEnv tags_t := 
  List.fold_left 
    (fun (cumulator: Clight.statement * ClightEnv tags_t ) (fn_param: string * (P.paramarg E.t E.t))
    =>let (name, t) := fn_param in 
      let (prev_stmt, prev_env) := cumulator in
      match find_ident_temp_arg tags_t env name with
      | None => cumulator
      | Some (oldid, tempid) => 
        match t with
        | P.PAIn t => 
        let (ct, env_ct) := CTranslateType t prev_env in
        let new_stmt := Sassign (Evar tempid ct) (Evar oldid ct) in
        (Ssequence prev_stmt new_stmt, env_ct)
        | P.PAOut t
        | P.PAInOut t => 
        let (ct, env_ct) := CTranslateType t prev_env in
        let new_stmt := Sassign (Evar tempid ct) (Ederef (Evar oldid (Ctypes.Tpointer ct noattr)) ct) in
        (Ssequence prev_stmt new_stmt, env_ct)
        end
      end
    ) fn_params (Sskip, env).

Definition CCopyOut (fn_params: E.params) (env: ClightEnv tags_t )
  : Clight.statement * ClightEnv tags_t := 
  List.fold_left 
    (fun (cumulator: Clight.statement * ClightEnv tags_t ) (fn_param: string * (P.paramarg E.t E.t))
    =>let (name, t) := fn_param in 
      let (prev_stmt, prev_env) := cumulator in
      match find_ident_temp_arg tags_t env name with
      | None => cumulator
      | Some (oldid, tempid) => 
        match t with
        | P.PAIn t => 
        let (ct, env_ct) := CTranslateType t prev_env in
        let new_stmt := Sassign (Evar oldid ct) (Evar tempid ct) in
        (Ssequence prev_stmt new_stmt, env_ct)
        | P.PAOut t
        | P.PAInOut t => 
        let (ct, env_ct) := CTranslateType t prev_env in
        let new_stmt := Sassign (Ederef (Evar oldid (Ctypes.Tpointer ct noattr)) ct) (Evar tempid ct) in
        (Ssequence prev_stmt new_stmt, env_ct)
        end
      end
    ) fn_params (Sskip, env).

(*return the list of args for the params*)
Definition CFindTempArgs (fn_params: E.params) (env: ClightEnv tags_t )
 : list Clight.expr := 
 List.fold_left 
  (fun (cumulator: list Clight.expr) (fn_param: string * (P.paramarg E.t E.t))
  =>let (name, t) := fn_param in
    match find_ident_temp_arg tags_t env name with
    | None => cumulator
    | Some (oldid, tempid) =>
      match t with 
      | P.PAIn t
      | P.PAOut t
      | P.PAInOut t =>
      let (ct, _) := CTranslateType t env in
      cumulator ++ [Evar tempid ct]
      end
    end
  ) fn_params [].

 (*return the list of args for the params but adding directions.
 change the temp to ref temp if it is a out parameter.
 *)
Definition CFindTempArgsForCallingSubFunctions (fn_params: E.params) (env: ClightEnv tags_t )
: list Clight.expr := 
List.fold_left 
 (fun (cumulator: list Clight.expr) (fn_param: string * (P.paramarg E.t E.t))
 =>let (name, t) := fn_param in
   match find_ident_temp_arg tags_t env name with
   | None => cumulator
   | Some (oldid, tempid) =>
    let (ct, _) := 
    match t with 
     | P.PAIn t
     | P.PAOut t
     | P.PAInOut t => CTranslateType t env 
    end in 
    let var := 
    match t with
     | P.PAIn t => Evar tempid ct
     | P.PAOut t
     | P.PAInOut t => Eaddrof (Evar tempid ct) (Tpointer ct noattr)
    end in
     cumulator ++ [var]

  end
   
 ) fn_params [].


Definition CTranslateArrow (signature : E.arrowT) (env : ClightEnv tags_t )
  : (list (AST.ident * Ctypes.type)) * Ctypes.type * ClightEnv tags_t  
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

Definition CTranslateTopParser (parsr: TD.d tags_t) (env: ClightEnv tags_t ): option (ClightEnv tags_t )
  :=
  match parsr with
  | TD.TPParser p cparams eps params st states i =>
    let (fn_cparams, env_cparams) := CTranslateConstructorParams cparams env in
    let (fn_params, env_params):= CTranslateParams params env_cparams in
    let (copyin, env_copyin) := CCopyIn params env_params in 
    let (copyout, env_copyout) := CCopyOut params env_copyin in
    let state_names := F.keys states in 
    let fn_params := fn_cparams ++ fn_params in 
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
        CCompEnv.add_function tags_t env_copyout "start" fn_sig
      in
      List.fold_left 
        (fun (cumulator : ClightEnv tags_t ) (state_name: string) =>
          CCompEnv.add_function tags_t cumulator state_name fn_sig
        ) state_names  env_start_fn_sig_declared in
    
    let env_fn_declared := 
      List.fold_left
      (fun (cumulator: option (ClightEnv tags_t )) (state_name: string)
      => match cumulator with | None => None | Some env' =>
        match Env.find state_name states with | None => None |Some sb =>
        match CTranslateParserState sb env' fn_params with | None => None | Some (f , env_f_translated) =>
        Some(CCompEnv.update_function tags_t env_f_translated state_name f)
        end end end
      ) state_names (Some (set_temp_vars tags_t env env_fn_sig_declared)) in
    (*finished declaring all the state blocks except start state*)
    match env_fn_declared with |None => None |Some env_fn_declared =>
    match CTranslateParserState st (set_temp_vars tags_t env env_fn_declared) fn_params with 
    | None => None 
    | Some (f_start, env_start_translated)=>
      let env_start_declared := CCompEnv.update_function tags_t env_start_translated "start" f_start in
      let env_start_declared := set_temp_vars tags_t env_copyout env_start_declared in
      match (lookup_function tags_t env_start_declared "start") with
      | None => None
      | Some (start_f, start_id) =>
      let call_args := CFindTempArgsForCallingSubFunctions params env_start_declared in
      let fn_body := 
      Ssequence copyin 
      (Ssequence 
      (Scall None (Evar start_id (Clight.type_of_function start_f)) call_args)
       copyout) in 
      let top_function := 
        (Clight.mkfunction
        Ctypes.Tvoid
        (AST.mkcallconv None true true)
        fn_params
        (get_vars tags_t env_start_declared)
        (get_temps tags_t env_start_declared)
        fn_body)
      in
      let env_topfn_added := CCompEnv.add_function tags_t env_start_declared p top_function in
      Some( set_temp_vars tags_t env env_topfn_added)
      end end end 
  | _ => None
  end.


  Definition CTranslateAction 
  (signature: E.params) (body: ST.s tags_t) 
  (env: ClightEnv tags_t ) (top_fn_params: list (AST.ident * Ctypes.type))
  (top_signature: E.params)
  : option (Clight.function* ClightEnv tags_t ):= 
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
        (get_vars tags_t env_body_translated)
        (get_temps tags_t env_body_translated)
        body), (set_temp_vars tags_t env env_body_translated))
  end.

  Fixpoint CTranslateControlLocalDeclaration 
  (ct : CT.d tags_t) (env: ClightEnv tags_t ) 
  (top_fn_params: list (AST.ident * Ctypes.type))
  (top_signature: E.params)
  : option (ClightEnv tags_t )
  := match ct with
  | CT.CDSeq d1 d2 i=> 
    match (CTranslateControlLocalDeclaration d1 env top_fn_params top_signature) with
    | None => None
    | Some (env1) =>
      match (CTranslateControlLocalDeclaration d2 env1 top_fn_params top_signature) with 
      | None => None
      | Some (env2) => Some (env2)
      end
    end
  | CT.CDAction a params body i => 
    match CTranslateAction params body env top_fn_params top_signature with
    | None => None
    | Some (f, env_action_translated) => Some (CCompEnv.add_function tags_t env_action_translated a f)
    end
  | CT.CDTable t (CT.Table ems actc init) i => Some env (*TODO: implement table*)
  end.
  
  Definition CTranslateTopControl (ctrl: TD.d tags_t) (env: ClightEnv tags_t ): option (ClightEnv tags_t )
  := 
  match ctrl with
  | TD.TPControl c cparams eps params body blk i
    => 
       let (fn_cparams, env_top_fn_cparam) := CTranslateConstructorParams cparams env in
       let (fn_params, env_top_fn_param) := CTranslateParams params env_top_fn_cparam in
       let (copyin, env_copyin) := CCopyIn params env_top_fn_param in 
       let (copyout, env_copyout) := CCopyOut params env_copyin in 
       let fn_params := fn_cparams ++ fn_params in 
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
          (get_vars tags_t env_apply_block_translated)
          (get_temps tags_t env_apply_block_translated)
          body in
          let env_top_fn_declared := 
          CCompEnv.add_function tags_t env_local_decled c top_fn in
          Some (set_temp_vars tags_t env env_top_fn_declared) 
        end
       end
  | _ => None
  end.


  
  Definition CTranslateFunction 
  (funcdecl : TD.d tags_t)
  (env: ClightEnv tags_t )
  : option (ClightEnv tags_t ):= 
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
            (get_vars tags_t env_body_translated)
            (get_temps tags_t env_body_translated)
            body) in
        Some (set_temp_vars tags_t env (CCompEnv.add_function tags_t env_params_created name top_function))
      end
    end 
  | _ => None
  end.

  Fixpoint CTranslateTopDeclaration (d: TD.d tags_t) (env: ClightEnv tags_t ) : option (ClightEnv tags_t )
  := 
  match d with
  | TD.TPSeq d1 d2 i => 
    match CTranslateTopDeclaration d1 env with
    | None => None
    | Some env1 => 
      match CTranslateTopDeclaration d2 env1 with
      | None => None
      | Some env2 => Some env2
      end end
  | TD.TPInstantiate c x args args_init i => 
    match CTranslateStatement args_init env with
    | None => None
    | Some (init', env') =>
    Some (set_main_init tags_t (set_instantiate_cargs tags_t env' args) init')
    end 
  | TD.TPFunction _ _ _ _ => CTranslateFunction d env
  | TD.TPExtern e cparams methods i => None (*TODO: implement*)
  | TD.TPControl _ _ _ _ _ _ _ => CTranslateTopControl d env
  | TD.TPParser _ _ _ _ _ _ _ => CTranslateTopParser d env
  | TD.TPPackage _ _ _ => None (*TODO: implement*)
  end.
  (* currently just an empty program *)
  Definition Compile (prog: TD.d tags_t) : Errors.res (Clight.program) := 
    let init_env := CCompEnv.newClightEnv tags_t in
    let (init_env1, _) :=  CCompEnv.new_ident tags_t (init_env) in 
    let (init_env2, _) :=  CCompEnv.new_ident tags_t (init_env1) in 
    let (init_env3, _) :=  CCompEnv.new_ident tags_t (init_env2) in 
    let (init_env4, _) :=  CCompEnv.new_ident tags_t (init_env3) in 
    let (init_env, main_id) := CCompEnv.new_ident tags_t (init_env4) in 
    match CTranslateTopDeclaration prog init_env with
    | None => Errors.Error (Errors.msg "something went wrong")
    | Some env_all_declared => 
      match CCompEnv.get_functions tags_t env_all_declared with
      | None => Errors.Error (Errors.msg "can't find all the declared functions")
      | Some f_decls => 
      let f_decls := List.map 
        (fun (x: AST.ident * Clight.function) 
        => let (id, f) := x in 
        (id, AST.Gfun(Ctypes.Internal f))) f_decls in
      let typ_decls := CCompEnv.get_composites tags_t env_all_declared in
      let main_decl :=
      AST.Gfun (Ctypes.Internal (main_fn tags_t env_all_declared (get_instantiate_cargs tags_t env_all_declared)))
      in 
      let res_prog : Errors.res (program function) := make_program 
        typ_decls ((main_id, main_decl):: f_decls) [] main_id
      in
      res_prog
      end
    end.

  Definition TypeDecls (prog: TD.d tags_t)  : Errors.res (list composite_definition) := 
    let init_env := CCompEnv.newClightEnv tags_t in
    let (init_env, _) :=  CCompEnv.new_ident tags_t (init_env) in 
    let (init_env, _) :=  CCompEnv.new_ident tags_t (init_env) in 
    let (init_env, _) :=  CCompEnv.new_ident tags_t (init_env) in 
    let (init_env, main_id) := CCompEnv.new_ident tags_t (init_env) in 
    match CTranslateTopDeclaration prog init_env with
    | None => Errors.Error (Errors.msg "something went wrong")
    | Some env_all_declared => 
      let typ_decls := CCompEnv.get_composites tags_t env_all_declared in
      Errors.OK typ_decls
    end.
  Definition Compile_print (prog: TD.d tags_t): unit := 
    match Compile prog with
    | Errors.Error e => tt
    | Errors.OK prog => print_Clight prog
    end.  
End CCompSel.
Definition helloworld_program_sel := RemoveSideEffect.TranslateProgram nat helloworld_program.
Definition test_compile_only := CCompSel.Compile nat helloworld_program_sel.
Definition test_type_decls := CCompSel.TypeDecls nat helloworld_program_sel.
Definition test := CCompSel.Compile_print nat helloworld_program_sel.
