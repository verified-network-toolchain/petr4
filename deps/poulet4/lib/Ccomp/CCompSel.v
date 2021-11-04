From compcert Require Import AST Clight Ctypes Integers Cop Clightdefs.
Require Import BinaryString.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.PArith.BinPos.
Require Import List.
Require Import Coq.ZArith.BinIntDef.
Require Import String.
Require Coq.PArith.BinPosDef.
Require Import Poulet4.P4cub.Syntax.Syntax.
Require Import Poulet4.P4cub.Envn.
Require Import Poulet4.P4cub.Transformations.Statementize.
Require Import Poulet4.Monads.Monad.
Require Import Poulet4.Monads.Option.
Require Import Poulet4.Monads.Error.
Require Import Poulet4.Ccomp.CCompEnv.
Require Import Poulet4.Ccomp.Helloworld.
Require Import Poulet4.Ccomp.CV1Model.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope clight_scope.
Import Clightdefs.ClightNotations.
Require Import Poulet4.Ccomp.Petr4Runtime.
Module RunTime := Petr4Runtime.
Parameter print_Clight: Clight.program -> unit.
(** P4Sel -> Clight **)
Section CCompSel.
  
  Context (tags_t: Type).
  (*common values*)
  Definition long_unsigned := Tlong Unsigned noattr.
  Definition long_signed := Tlong Signed noattr.
  Definition int_unsigned := Tint I32 Unsigned noattr.
  Definition int_signed := Tint I32 Signed noattr.
  Definition char := Tint I8 Unsigned noattr.
  Definition Cstring := Tpointer char noattr.
  Definition bit_vec := 
    (Tstruct (RunTime._BitVec) noattr).
  Definition TpointerBitVec := Ctypes.Tpointer bit_vec noattr.
  Definition TpointerBool := Ctypes.Tpointer type_bool noattr.  
  
  Fixpoint CTranslateType (p4t : Expr.t) (env: ClightEnv tags_t) : Ctypes.type * ClightEnv tags_t:=
    match p4t with
    | Expr.TBool => (Ctypes.type_bool, env)
    | Expr.TBit (w) => (bit_vec,env)
    | Expr.TInt (w) => (bit_vec, env)
    | Expr.TVar name => (Ctypes.Tvoid, env) (*TODO: implement, I'm really lost on this*)
    | Expr.TError => (Ctypes.Tvoid, env) (*TODO: implement what exactly is an error type? Should it be depending on the target?*)
    | Expr.TMatchKind => (int_unsigned, env) (*I guess this should just be an enum, aka an int.*)

    | Expr.TTuple (ts) => 
        match lookup_composite tags_t env p4t with
        | inl comp => (Ctypes.Tstruct (Ctypes.name_composite_def comp) noattr, env)
        | _ => 
        let (env_top_id, top_id) := CCompEnv.new_ident tags_t env in
        let (members ,env_fields_declared):= 
        List.fold_left 
        (fun (cumulator: Ctypes.members*ClightEnv tags_t)  (field: Expr.t) 
        => let (members_prev, env_prev) := cumulator in 
           let (new_t, new_env):= CTranslateType field env_prev in
           let (new_env, new_id):= CCompEnv.new_ident tags_t new_env in
           (members_prev ++ [(new_id, new_t)], new_env))
        ts ([],env_top_id) in
        let comp_def := Ctypes.Composite top_id Ctypes.Struct members Ctypes.noattr in
        let env_comp_added := CCompEnv.add_composite_typ tags_t env_fields_declared p4t comp_def in
        (Ctypes.Tstruct top_id noattr, env_comp_added)
        end

    | Expr.TStruct (fields) => 
        match lookup_composite tags_t env p4t with
        | inl comp => (Ctypes.Tstruct (Ctypes.name_composite_def comp) noattr, env)
        | _ => 
        let (env_top_id, top_id) := CCompEnv.new_ident tags_t env in
        let (members ,env_fields_declared):= 
        F.fold 
        (fun (k: string) (field: Expr.t) (cumulator: Ctypes.members*ClightEnv tags_t) 
        => let (members_prev, env_prev) := cumulator in 
           let (new_t, new_env):= CTranslateType field env_prev in
           let new_t := 
           match new_t with 
           | (Tstruct st noattr) => if(st == RunTime._BitVec) then Tpointer new_t noattr else new_t
           | _ => new_t end in 
           let (new_env, new_id):= CCompEnv.new_ident tags_t new_env in
           (members_prev ++ [(new_id, new_t)], new_env))
        fields ([],env_top_id) in
        let comp_def := Ctypes.Composite top_id Ctypes.Struct members Ctypes.noattr in
        let env_comp_added := CCompEnv.add_composite_typ tags_t env_fields_declared p4t comp_def in
        (Ctypes.Tstruct top_id noattr, env_comp_added)
        end

    | Expr.THeader (fields) => 
    (* struct plus a validity boolean value *)
        match lookup_composite tags_t env p4t with
        | inl comp => (Ctypes.Tstruct (Ctypes.name_composite_def comp) noattr, env)
        | _ => 
        let (env_top_id, top_id) := CCompEnv.new_ident tags_t env in
        let (env_valid, valid_id) := new_ident tags_t env_top_id in 
        let (members ,env_fields_declared):= 
        F.fold 
        (fun (k: string) (field: Expr.t) (cumulator: Ctypes.members*ClightEnv tags_t ) 
        => let (members_prev, env_prev) := cumulator in 
           let (new_t, new_env):= CTranslateType field env_prev in
           let new_t := 
           match new_t with 
           | (Tstruct st noattr) => if(st == RunTime._BitVec) then Tpointer new_t noattr else new_t
           | _ => new_t end in 
           let (new_env, new_id):= CCompEnv.new_ident tags_t new_env in
           (members_prev++[(new_id, new_t)], new_env))
        fields ([(valid_id, type_bool)],env_valid) in
        let comp_def := Ctypes.Composite top_id Ctypes.Struct members Ctypes.noattr in
        let env_comp_added := CCompEnv.add_composite_typ tags_t env_fields_declared p4t comp_def in
        (Ctypes.Tstruct top_id noattr, env_comp_added)
        end

    | Expr.THeaderStack fields n=> 
      match lookup_composite tags_t env p4t with
      | inl comp => (Ctypes.Tstruct (Ctypes.name_composite_def comp) noattr, env)
      | _ =>
        let header := Expr.THeader fields in
        let (hdarray, env_hdarray) := 
        match lookup_composite tags_t env header with
        | inl comp => (Ctypes.Tarray (Ctypes.Tstruct (Ctypes.name_composite_def comp) noattr) (Zpos n) noattr, env)
        | _ => 
        let (env_top_id, top_id) := CCompEnv.new_ident tags_t env in
        let (env_valid, valid_id) := new_ident tags_t env_top_id in 
        let (members ,env_fields_declared):= 
        F.fold 
        (fun (k: string) (field: Expr.t) (cumulator: Ctypes.members*ClightEnv tags_t ) 
        => let (members_prev, env_prev) := cumulator in 
          let (new_t, new_env):= CTranslateType field env_prev in
          let new_t := 
           match new_t with 
           | (Tstruct st noattr) => if(st == RunTime._BitVec) then Tpointer new_t noattr else new_t
           | _ => new_t end in 
          let (new_env, new_id):= CCompEnv.new_ident tags_t new_env in
          (members_prev++[(new_id, new_t)], new_env))
        fields ([(valid_id, type_bool)],env_valid) in
        let comp_def := Ctypes.Composite top_id Ctypes.Struct members Ctypes.noattr in
        let env_comp_added := CCompEnv.add_composite_typ tags_t env_fields_declared header comp_def in
        (Tarray (Ctypes.Tstruct top_id noattr) (Zpos n) noattr, env_comp_added)
        end in
        let (env_ptr_id, ptr_id) := CCompEnv.new_ident tags_t env_hdarray in
        let (env_size_id, size_id) := CCompEnv.new_ident tags_t env_ptr_id in
        let (env_arr_id, arr_id) := CCompEnv.new_ident tags_t env_size_id in
        let (env_top_id, top_id) := CCompEnv.new_ident tags_t env_arr_id in
        let comp_def := Ctypes.Composite top_id Ctypes.Struct [(ptr_id, int_signed);(size_id, int_signed);(arr_id, hdarray)] noattr in
        let env_comp_added := CCompEnv.add_composite_typ tags_t env_top_id p4t comp_def in
        ((Ctypes.Tstruct top_id noattr), env_comp_added)      
      end
  end.

  Definition CTranslateConstructorType (ct: Expr.ct) (env: ClightEnv tags_t) : Ctypes.type * ClightEnv tags_t :=
  match ct with 
  | Expr.CTType type => CTranslateType type env
  | Expr.CTControl cparams _ parameters => (Ctypes.Tvoid, env) (*TODO: implement*)
  | Expr.CTParser cparams  _ parameters => (Ctypes.Tvoid, env) (*TODO: implement*)
  | Expr.CTPackage cparams => (Ctypes.Tvoid, env) (*TODO: implement*)

  | Expr.CTExtern extern_name => 
    match extern_name with
    | "packet_in" => (packet_in,env)
    | "packet_out" => (packet_out, env)
    | _ => (Ctypes.Tvoid, env) (*TODO: implement*) 
    end
  end.
  
  Definition findStackAttributes (stack_var: Clight.expr) (stack_t : Ctypes.type) (env: ClightEnv tags_t)
  :=
    match stack_t with
    | Ctypes.Tstruct compid noattr =>
      let* comp := lookup_composite_id tags_t env compid in
      match comp with 
      | Ctypes.Composite _ _ ((next_id, ti) :: (size_id, ts) :: (arr_id, ta)::[]) _ => 
        let '(size_var, next_var, arr_var) := (Efield stack_var size_id ts, Efield stack_var next_id ti, Efield stack_var arr_id ta) in
        match ta with
        | Tarray val_typ _ _ =>
          match val_typ with
          | Ctypes.Tstruct val_t_id noattr => 
            let* val_comp := lookup_composite_id tags_t env val_t_id in
            match val_comp with
            | Ctypes.Composite _ _ ((val_typ_valid_index,type_bool)::_) _ =>
            error_ret (next_var,ti,size_var,ts,arr_var,ta, val_typ, val_typ_valid_index)
            |_ => err "not a stack of struct or header"
            end
          | _ => err "not a stack of struct or header"
          end
        | _ => err "array not at the expected place"
        end  
      |_ => err "the composite looked up is not a composite"
      end
    | _ => err "stack is not a struct"
    end.
  
  Definition ArrayAccess (arr : Clight.expr) (index : Clight.expr) (result_t: Ctypes.type) : Clight.expr
  := 
    Ederef 
    (Ebinop Oadd arr index (Tpointer result_t noattr))
    result_t.

  Fixpoint CTranslateExpr (e: Expr.e tags_t) (env: ClightEnv tags_t )
    : @error_monad string (Clight.expr * ClightEnv tags_t ) :=
    match e with
    | Expr.EBool true i =>   error_ret (Econst_int (Integers.Int.one) (type_bool), env)
    | Expr.EBool false i =>  error_ret (Econst_int (Integers.Int.zero) (type_bool), env)

    | Expr.EVar ty x i => (*first find if x has been declared. If not, declare it *)
                        let (cty, env_ty) := CTranslateType ty env in
                        match find_ident_temp_arg tags_t env_ty x with 
                        (*first look for if this is an argument and has its own temp for copy in/out *)
                        | inl (_,tempid) => error_ret (Etempvar tempid cty, env_ty)
                        | _ =>
                        match find_ident tags_t env_ty x with
                        | inl id => error_ret (Evar id cty, env_ty)
                        | _ => let env' := add_var tags_t env_ty x cty in
                                  let* id' := find_ident tags_t env' x in
                                  error_ret (Evar id' cty, env')
                        end
                        end

    | Expr.EExprMember ty y x i =>
                        let(cty, env_ty):= CTranslateType ty env in
                        let* (x', env') := CTranslateExpr x env_ty in
                        match ty with
                        | Expr.TStruct(f) =>
                          match F.get_index y f , F.get y f with 
                          | Some n, Some t_member =>
                            let (ctm, env_ctm) := CTranslateType t_member env' in
                            let em :=
                              match ctm with 
                              | (Tstruct st _) => if(st == RunTime._BitVec) 
                                                      then Ederef (Clight.Efield x' (Pos.of_nat n) (Tpointer ctm noattr)) (ctm)
                                                      else (Clight.Efield x' (Pos.of_nat n) ctm)
                              | _ => (Clight.Efield x' (Pos.of_nat n) ctm) end in 
                            error_ret (em, env_ctm)
                          | _, _ => err "member is not in struct"
                          end
                            
                        | Expr.THeader(f) => 
                        (* +1 for the valid bit *)
                          match F.get_index y f , F.get y f with 
                          | Some n, Some t_member =>
                            let (ctm, env_ctm) := CTranslateType t_member env' in
                            let em :=
                              match ctm with 
                              | (Tstruct st _) => if(st == RunTime._BitVec) 
                                                      then Ederef (Clight.Efield x' (Pos.of_nat (n+1)) (Tpointer ctm noattr)) (ctm)
                                                      else (Clight.Efield x' (Pos.of_nat (n+1)) ctm)
                              | _ => (Clight.Efield x' (Pos.of_nat (n+1)) ctm) end in 
                            error_ret (em, env_ctm)
                          | _, _ => err "member is not in struct"
                          end
                        | _ => err "member of an invalid type"
                        end

    | Expr.EHeaderStackAccess ts stack index i => 
      let (stack_t,env) := CTranslateType (Expr.THeader ts) env in 
      let* (stack, env) :=  CTranslateExpr stack env in
      let* (next_var,ti,size_var,ts,arr_var,ta, val_typ, val_typ_valid_index) 
        := findStackAttributes stack stack_t env in
      error_ret (ArrayAccess arr_var (Econst_int (Integers.Int.repr index) int_signed ) val_typ, env)

    | Expr.EError x i => err "EError , todo : implement" (*TODO: implement*)
    | Expr.EMatchKind mk i => err "EMatchKind, todo : implement" (*TODO : implement*)
    | _ => err "illegal expression, statementized failed" (*Not Allowed*)
    end.

  Definition CTranslateExprList (el : list (Expr.e tags_t)) (env: ClightEnv tags_t ): @error_monad string ((list Clight.expr) * ClightEnv tags_t ) :=
    let Cumulator: Type := @error_monad string (list Clight.expr * ClightEnv tags_t ) in 
    let transformation (A: Cumulator) (B: Expr.e tags_t) : Cumulator := 
      let* (el', env') := A in 
      let* (B', env'') := CTranslateExpr B env' in
      error_ret (el' ++ [B'], env'') in
    List.fold_left  (transformation) el (error_ret ([],env)).
  
  Definition CTranslateDirExprList (el: Expr.args tags_t) (env: ClightEnv tags_t ) : @error_monad string ((list Clight.expr) * ClightEnv tags_t ) := 
    let Cumulator : Type := @error_monad string (list Clight.expr * ClightEnv tags_t ) in 
    let transformation
          (A: Cumulator)
          (B: string * (paramarg (Expr.e tags_t) (Expr.e tags_t))) : Cumulator := 
      let* (el', env') := A in
      match B with 
      | (_, PAIn e)
      | (_, PADirLess e) =>
        let* (e', env'') := CTranslateExpr e env' in
        error_ret (el' ++ [e'], env'')
      | (_, PAOut e)
      | (_, PAInOut e) =>
        let t := t_of_e e in
        let (ct, env_ct):= CTranslateType t env' in 
        let*  (e', env'') := CTranslateExpr e env_ct in
        let e' := Eaddrof e' (Tpointer ct noattr) in 
        error_ret (el' ++ [e'], env'')
      end
    in 
    List.fold_left  (transformation) el (error_ret ([],env)).
  
  Definition typelist_slice := 
    Ctypes.Tcons TpointerBitVec 
    (Ctypes.Tcons TpointerBitVec 
    (Ctypes.Tcons TpointerBitVec
    (Ctypes.Tcons TpointerBitVec Ctypes.Tnil))).

  Definition slice_function := 
    Evar $"eval_slice" (Tfunction typelist_slice tvoid cc_default).
  
  Definition typelist_uop := 
    Ctypes.Tcons TpointerBitVec 
    (Ctypes.Tcons TpointerBitVec Ctypes.Tnil).
  
  Definition uop_function (op: ident) := 
    Evar op (Tfunction typelist_uop tvoid cc_default).
    
  Definition typelist_bop_bitvec := 
    let TpointerBitVec := Ctypes.Tpointer bit_vec noattr in 
    Ctypes.Tcons TpointerBitVec 
    (Ctypes.Tcons TpointerBitVec
    (Ctypes.Tcons TpointerBitVec
    Ctypes.Tnil)).

  Definition typelist_bop_bool := 
    Ctypes.Tcons TpointerBitVec 
    (Ctypes.Tcons TpointerBitVec
    (Ctypes.Tcons TpointerBool
    Ctypes.Tnil)).

  Definition bop_function (op: ident) := 
    if(op == _interp_beq) then
      Evar op (Tfunction typelist_bop_bool tvoid cc_default) 
    (* else if(op == _interp_not_eq) then
      Evar op (Tfunction typelist_bop_bool tvoid cc_default)  *)
    else if(op == _interp_bge) then
      Evar op (Tfunction typelist_bop_bool tvoid cc_default) 
    else if(op == _interp_bgt) then
      Evar op (Tfunction typelist_bop_bool tvoid cc_default) 
    else if(op == _interp_ble) then
      Evar op (Tfunction typelist_bop_bool tvoid cc_default) 
    else if(op == _interp_blt) then
      Evar op (Tfunction typelist_bop_bool tvoid cc_default) 
    else
      Evar op (Tfunction typelist_bop_bitvec tvoid cc_default) 
    .

  Definition typelist_bitvec_init :=
    Ctypes.Tcons TpointerBitVec 
    (Ctypes.Tcons type_bool
    (Ctypes.Tcons int_signed
    (Ctypes.Tcons Cstring
    Ctypes.Tnil))).

  Definition bitvec_init_function := 
    Evar _init_bitvec (Tfunction typelist_bitvec_init tvoid cc_default). 

  Definition ValidBitIndex (arg: Expr.e tags_t) (env: ClightEnv tags_t ) : @error_monad string AST.ident
  :=
    let* comp:= lookup_composite tags_t env (t_of_e arg) in
    match comp with
    | Ctypes.Composite _ Ctypes.Struct m _ =>
      match m with
      | [] => err "struct is empty"
      | (id,t) :: _ => error_ret id
      end
    | _ => err "composite looked up is not a composite"
    end.
  
  Definition HeaderStackIndex := ValidBitIndex.
  
  Definition HeaderStackSize (arg: Expr.e tags_t) (env: ClightEnv tags_t ) : @error_monad string AST.ident
  :=
    let* comp := lookup_composite tags_t env (t_of_e arg) in
    match comp with
    | Ctypes.Composite _ Ctypes.Struct m _=>
      match m with
        | (_,_) :: (id,t) :: _ => error_ret id
        | _ => err "struct too small"
      end
    | _ => err "composite looked up is not aa composite"
    end.

  Definition CTranslateUop 
    (dst_t: Expr.t)
    (op: Expr.uop)
    (arg: Expr.e tags_t)
    (dst: string)
    (env: ClightEnv tags_t ): @error_monad string (Clight.statement * ClightEnv tags_t ) 
  := 
    let* dst' :=  find_ident tags_t env dst in 
    let (dst_t', env') := CTranslateType dst_t env in 
    let dst' := Evar dst' dst_t' in
    let* (arg', env_arg) := CTranslateExpr arg env' in
    let arg_ref := Eaddrof arg' (Tpointer (Clight.typeof arg') noattr) in
    let dst_ref := Eaddrof dst' (Tpointer dst_t' noattr) in  
    match op with
    | Expr.Not => 
      let not_expr := Eunop Onotbool arg' Ctypes.type_bool in 
      error_ret (Sassign dst' not_expr, env_arg)

    | Expr.BitNot => 
      (*need implementation in runtime*)
      error_ret (Scall None (uop_function _interp_bitwise_and) [arg_ref; dst_ref], env_arg)

    | Expr.UMinus => 
      error_ret (Scall None (uop_function _eval_uminus)  [arg_ref; dst_ref], env_arg)

    | Expr.IsValid =>
      let* index := ValidBitIndex arg env_arg in
      let member :=  Efield arg' index type_bool in
      error_ret (Sassign dst' member, env_arg)

    | Expr.NextIndex =>
      let* index := HeaderStackIndex arg env_arg in
      let member := Efield arg' index int_signed in
      let increment := Ebinop Oadd member (Econst_int Integers.Int.one int_signed) int_signed in
      let assign := Sassign member increment in 
      let to_dst := Sassign dst' arg' in
      error_ret (Ssequence assign to_dst, env_arg) 

    | Expr.Size => 
      let* index := HeaderStackSize arg env_arg in
      let member := Efield arg' index int_signed in
      let to_dst := Sassign dst' member in
      error_ret (to_dst, env_arg) 

    | _ => err "Unsupported uop"  
    end.

  Definition CTranslateBop 
    (dst_t: Expr.t)
    (op: Expr.bop)
    (le: Expr.e tags_t)
    (re: Expr.e tags_t)
    (dst: string)
    (env: ClightEnv tags_t ) : @error_monad string (Clight.statement * ClightEnv tags_t )
  := 
    let* dst' := find_ident tags_t env dst in
    let (dst_t', env') := CTranslateType dst_t env in 
    let dst' := Evar dst' dst_t' in
    let* (le', env_le) := CTranslateExpr le env' in 
    let* (re', env_re) := CTranslateExpr re env_le in
    let le_ref := Eaddrof le' (Tpointer (Clight.typeof le') noattr) in
    let re_ref := Eaddrof re' (Tpointer (Clight.typeof re') noattr) in
    let dst_ref := Eaddrof dst' (Tpointer dst_t' noattr) in  
    let signed := 
      match dst_t with
      | Expr.TInt _ => true
      | _ => false
      end in
    match op with
    | Expr.Plus => error_ret (Scall None (bop_function _interp_bplus) [dst_ref; le'; re'], env_re)
    | Expr.PlusSat => error_ret (Scall None (bop_function _interp_bplus_sat) [dst_ref; le'; re'], env_re)
    | Expr.Minus => error_ret (Scall None (bop_function _interp_bminus) [dst_ref; le'; re'], env_re)
    | Expr.MinusSat => error_ret (Scall None (bop_function _interp_bminus_sat) [dst_ref; le'; re'], env_re)
    | Expr.Times => error_ret (Scall None (bop_function  _interp_bmult) [dst_ref; le'; re'], env_re)
    | Expr.Shl => error_ret (Scall None (bop_function _interp_bshl) [dst_ref; le'; re'], env_re)
    | Expr.Shr => error_ret (Scall None (bop_function _interp_bshr) [dst_ref; le'; re'], env_re)
    | Expr.Le => error_ret (Scall None (bop_function  _interp_ble) [dst_ref; le'; re'], env_re)
    | Expr.Ge => error_ret (Scall None (bop_function _interp_bge) [dst_ref; le'; re'], env_re)
    | Expr.Lt => error_ret (Scall None (bop_function _interp_blt) [dst_ref; le'; re'], env_re)
    | Expr.Gt => error_ret (Scall None (bop_function _interp_bgt) [dst_ref; le'; re'], env_re)

    | Expr.Eq => 
      match Clight.typeof le' with
      | Tint IBool Signed noattr =>
        let eq_expr :=  Ebinop Oeq le' re' type_bool in
        error_ret (Sassign dst' eq_expr, env_re)
      | _ =>
        error_ret (Scall None (bop_function _interp_beq) [dst_ref; le'; re'], env_re)
      end
    
    | Expr.NotEq => 
      match Clight.typeof le' with
      | Tint IBool Signed noattr =>
        let eq_expr :=  Ebinop Oeq le' re' type_bool in
        error_ret (Sassign dst' eq_expr, env_re)
      | _ =>  (*TODO: want a not eq here*)
        error_ret (Scall None (bop_function _interp_beq) [dst_ref; le'; re'], env_re)
      end
    
    | Expr.BitAnd => error_ret (Scall None (bop_function _interp_bitwise_and) [dst_ref; le'; re'], env_re)
    | Expr.BitXor => error_ret (Scall None (bop_function _interp_bitwise_xor) [dst_ref; le'; re'], env_re)
    | Expr.BitOr => error_ret (Scall None (bop_function _interp_bitwise_or) [dst_ref; le'; re'], env_re)

    | Expr.PlusPlus => 
    (*TODO: Need implementation in runtime*)
      error_ret (Scall None (bop_function _interp_bplus) [dst_ref; le'; re'], env_re)

    | Expr.And => 
      let and_expr :=  Ebinop Oand le' re' type_bool in
      error_ret (Sassign dst' and_expr, env_re)
    
    | Expr.Or => 
      let or_expr :=  Ebinop Oor le' re' type_bool in
      error_ret (Sassign dst' or_expr, env_re)
    end
    .
  

  Definition CTranslateFieldType (fields: F.fs string (Expr.e tags_t)) 
    := F.map (t_of_e) fields.
    
  Definition CTranslateListType (exps : list (Expr.e tags_t)):=
    List.map (t_of_e) exps.

  Fixpoint CTranslateFieldAssgn (m : members) (exps : F.fs string (Expr.e tags_t)) (dst : Clight.expr) (env: ClightEnv tags_t):= 
    match m, exps with 
    |(id, typ) :: mtl, (fname, exp) :: etl => 
      let* (exp, env') := CTranslateExpr exp env in 
      let* (nextAssgn, env') := CTranslateFieldAssgn mtl etl dst env' in
      let curAssgn := 
          match typ with 
          | Tpointer t _  => Sassign (Ederef (Efield dst id typ) (t)) exp 
          | _ => Sassign (Efield dst id typ) exp
          end in 
      error_ret (Ssequence curAssgn nextAssgn , env')
    | [],[] => error_ret (Sskip,env)
    | _ , _ => err "field different length"
    end.
  
  Fixpoint CTranslateListAssgn (m : members) (exps : list (Expr.e tags_t)) (dst : Clight.expr) (env: ClightEnv tags_t):= 
    match m, exps with 
    |(id, typ) :: mtl, exp :: etl => 
      let* (exp, env') := CTranslateExpr exp env in
      let* (nextAssgn, env') := CTranslateListAssgn mtl etl dst env' in 
      error_ret (Ssequence (Sassign (Efield dst id typ) exp) nextAssgn , env')
    | [],[] => error_ret (Sskip,env)
    | _ , _ => err "list different length"
    end.

  Definition CTranslateTupleAssgn (exps: list (Expr.e tags_t)) (composite: composite_definition) (dst : Clight.expr) (env: ClightEnv tags_t):=
    match composite with 
      | Composite id su m a =>
        CTranslateListAssgn m exps dst env
    end.  

  Definition CTranslateStructAssgn (fields: F.fs string (Expr.e tags_t))
             (composite: composite_definition) (dst : Clight.expr) (env: ClightEnv tags_t):=
    match composite with 
      | Composite id su m a =>
        CTranslateFieldAssgn m fields dst env
    end.

  Definition CTranslateHeaderAssgn (exps: F.fs string (Expr.e tags_t)) (composite: composite_definition) (dst : Clight.expr) (env: ClightEnv tags_t) (valid: Clight.expr):=
    match composite with 
      | Composite id su ((valid_id, valid_typ) :: mtl) a =>
        let assignValid := Sassign (Efield dst valid_id valid_typ) valid in
        let* (assigns, env') := CTranslateFieldAssgn mtl exps dst env in
        error_ret (Ssequence assignValid assigns , env')  
      |_ => err "Not a composite"
    end.

  Definition PushLoop 
    (n : positive) (env: ClightEnv tags_t) 
    (arr_var : Clight.expr)
    (size : Clight.expr) 
    (next_var : Clight.expr)
    (i : AST.ident) (val_typ : Ctypes.type) (val_typ_valid_index : AST.ident)
  := 
    let ivar := Etempvar i int_signed in
    let int_one := Econst_int Integers.Int.one int_signed in
    let int_zero := Econst_int Integers.Int.zero int_signed in
    let int_n := Econst_int (Integers.Int.repr (Zpos n)) int_signed in
    let false := Econst_int Integers.Int.zero type_bool in
    let for_loop := 
    Sfor 
    (Sset i (Ebinop Osub size int_one int_signed)) 
    (Ebinop Oge ivar int_zero type_bool) 
    (Sset i (Ebinop Osub ivar int_one int_signed)) 
    (
      Sifthenelse 
      (Ebinop Oge ivar int_n type_bool)
      (Sassign (ArrayAccess arr_var ivar val_typ) (ArrayAccess arr_var (Ebinop Osub ivar int_n int_signed) val_typ))
      (Sassign (Efield (ArrayAccess arr_var ivar val_typ) val_typ_valid_index type_bool) false)
    )
    in 
    let increment := 
    (Ssequence
    (Sassign next_var (Ebinop Oadd next_var int_n int_signed))
    (
      Sifthenelse 
      (Ebinop Ogt next_var size type_bool)
      (Sassign next_var size)
      (Sskip)))
    in
    Ssequence for_loop increment
    .

  Definition CTranslatePush (stack : AST.ident) (n : positive) (env: ClightEnv tags_t) : @error_monad string (Clight.statement * ClightEnv tags_t):= 
    let env := add_temp tags_t env "i" int_signed in
    let* i := find_ident tags_t env "i" in
    let* stack_t := lookup_temp_type tags_t env stack in
    let stack_var := Evar stack (stack_t) in
    let* (next_var,ti,size_var,ts,arr_var,ta, val_typ, val_typ_valid_index) 
      := findStackAttributes stack_var stack_t env in
    error_ret (
      (PushLoop n env arr_var size_var 
      next_var i val_typ val_typ_valid_index), 
      env) 
    .

  Definition PopLoop 
    (n : positive) (env: ClightEnv tags_t) 
    (arr_var : Clight.expr)
    (size : Clight.expr) 
    (next_var : Clight.expr)
    (i : AST.ident) (val_typ : Ctypes.type) (val_typ_valid_index : AST.ident)
  := 
    let ivar := Etempvar i int_signed in
    let int_one := Econst_int Integers.Int.one int_signed in
    let int_zero := Econst_int Integers.Int.zero int_signed in
    let int_n := Econst_int (Integers.Int.repr (Zpos n)) int_signed in
    let false := Econst_int Integers.Int.zero type_bool in
    let for_loop := 
    Sfor 
    (Sset i int_zero) 
    (Ebinop Olt ivar size type_bool) 
    (Sset i (Ebinop Oadd ivar int_one int_signed)) 
    (
      Sifthenelse 
      (Ebinop Olt (Ebinop Oadd ivar int_n int_signed) size type_bool)
      (Sassign (ArrayAccess arr_var ivar val_typ) (ArrayAccess arr_var (Ebinop Oadd ivar int_n int_signed) val_typ))
      (Sassign (Efield (ArrayAccess arr_var ivar val_typ) val_typ_valid_index type_bool) false)
    )
    in 
    let decrement := 
    Sifthenelse 
    (Ebinop Oge next_var int_n type_bool)
    (Sassign next_var (Ebinop Osub size int_n int_signed))
    (Sassign next_var int_zero)
    in
    Ssequence for_loop decrement
    .

  Definition CTranslatePop (stack : AST.ident) (n : positive) (env: ClightEnv tags_t) : @error_monad string (Clight.statement * ClightEnv tags_t):= 
    let env := add_temp tags_t env "i" int_signed in
    let* i := find_ident tags_t env "i" in
    let* stack_t := lookup_temp_type tags_t env stack in
    let stack_var := Evar stack (stack_t) in
    let* (next_var,ti,size_var,ts,arr_var,ta, val_typ, val_typ_valid_index) :=
      findStackAttributes stack_var stack_t env in
    error_ret (
      (PopLoop n env arr_var size_var 
      next_var i val_typ val_typ_valid_index), 
      env) 
    .

  Fixpoint HeaderStackAssignLoop 
    (env: ClightEnv tags_t) 
    (arr_var: Clight.expr) 
    (i_var : Clight.expr) 
    (fields : F.fs string Expr.t) 
    (headers: list (Expr.e tags_t))
    (header_typ : Ctypes.type)
    : @error_monad string (Clight.statement * ClightEnv tags_t)
  := 
    let true := Econst_int Integers.Int.one type_bool in
    let int_one := Econst_int Integers.Int.one int_signed in
    match headers with
    | [] => error_ret (Sskip, env)
    | header :: tl => 
      let* (header,env) := CTranslateExpr header env in
      let assignHeader := Sassign (ArrayAccess arr_var i_var header_typ) header in
      let increment := Sassign (i_var) (Ebinop Oadd i_var int_one int_signed) in
      let* (assigntail, env') := HeaderStackAssignLoop env arr_var i_var fields tl header_typ in
      error_ret ((Ssequence assignHeader (Ssequence increment assigntail)), env')
    end.

  Fixpoint CTranslateStatement (s: Stmt.s tags_t) (env: ClightEnv tags_t ) : @error_monad string (Clight.statement * ClightEnv tags_t ) :=
    match s with
    | Stmt.SSkip i => error_ret (Sskip, env)
    | Stmt.SSeq s1 s2 i => 
      let* (s1', env1) := CTranslateStatement s1 env in
      let* (s2', env2) := CTranslateStatement s2 env1 in
      error_ret (Ssequence s1' s2', env2)

    | Stmt.SBlock s => CTranslateStatement s env
    | Stmt.SVardecl x (Left t) i => 
      let (cty, env_cty):= CTranslateType t env in
      error_ret (Sskip, CCompEnv.add_var tags_t env_cty x cty)
    | Stmt.SVardecl x (Right e) i => err "FIXME" (* TODO *)
    | Stmt.SConditional e s1 s2 i => 
      let* (e', env1) := CTranslateExpr e env in
      let* (s1', env2) := CTranslateStatement s1 env1 in
      let* (s2', env3) := CTranslateStatement s2 env2 in                 
      error_ret (Sifthenelse e' s1' s2', env3)

    | Stmt.SFunCall f _ (Arrow args None) i
    | Stmt.SActCall f args i => 
      let* (f', id) := CCompEnv.lookup_function tags_t env f in
      let* (elist, env') := CTranslateDirExprList args env in 
      error_ret (Scall None (Evar id (Clight.type_of_function f')) elist, env')                              

    | Stmt.SFunCall f _ (Arrow args (Some e)) i =>
      let t := t_of_e e in
      let (ct, env_ct) := CTranslateType t env in
      let* (f', id) := CCompEnv.lookup_function tags_t env_ct f in
      let* (elist, env') := CTranslateDirExprList args env_ct in
      let (env', tempid) := CCompEnv.add_temp_nameless tags_t env' ct in
      let* (lvalue, env') := CTranslateExpr e env' in 
      error_ret (
        (Ssequence 
        (Scall (Some tempid) (Evar id (Clight.type_of_function f')) elist)
        (Sassign lvalue (Etempvar tempid ct) ))
        , env')
    
    | Stmt.SExternMethodCall e f _ (Arrow args x) i => error_ret (Sskip, env) (*TODO: implement, need to be target specific.*)

    | Stmt.SReturn (Some e) i => 
      let* (e', env') := CTranslateExpr e env in
      error_ret ((Sreturn (Some e')), env')
    | Stmt.SReturn None i => error_ret (Sreturn None, env)
    | Stmt.SExit i => error_ret (Sskip, env) (*TODO: implement, what is this?*)
    | Stmt.SApply x ext args i => 
      let* (f', id) := CCompEnv.lookup_function tags_t env x in
      let* (elist, env') := CTranslateDirExprList args env in 
      error_ret (Scall None (Evar id (Clight.type_of_function f')) elist, env')  (*TODO: figure out why extern args here?*)          
    | Stmt.SInvoke tbl i => error_ret (Sskip, env) (*TODO: implement*)
    | Stmt.SAssign e1 e2 i =>
      let t := t_of_e e1 in
      match e1 with
      | Expr.EVar dst_t dst i => 
        match e2 with
        | Expr.EBit width val i => 
          let* dst' := find_ident tags_t env dst in
          let (env', val_id) := find_BitVec_String tags_t env val in 
          let w := Econst_int (Integers.Int.repr (Z.of_N width)) (int_signed) in
          let signed := Econst_int (Integers.Int.zero) (type_bool) in 
          let val' := Evar val_id Cstring in
          let dst' := Eaddrof (Evar dst' bit_vec) TpointerBitVec in
          error_ret (Scall None bitvec_init_function [dst'; signed; w; val'], env')
        
        | Expr.EInt width val i => 
          let* dst' := find_ident tags_t env dst in
          let (env', val_id) := find_BitVec_String tags_t env val in 
          let w := Econst_int (Integers.Int.repr (Zpos width)) (int_signed) in
          let signed := Econst_int (Integers.Int.one) (type_bool) in 
          let val' := Evar val_id Cstring in
          let dst' := Eaddrof (Evar dst' bit_vec) TpointerBitVec in
          error_ret (Scall None bitvec_init_function [dst'; signed; w; val'], env')

        | Expr.ESlice n hi lo i =>
          let τ := t_of_e n in
          let* (n', env') := CTranslateExpr n env in
          let hi' := Econst_int (Integers.Int.repr (Zpos hi)) (int_unsigned) in
          let lo' := Econst_int (Integers.Int.repr (Zpos lo)) (int_unsigned) in
          let* dst' := find_ident tags_t env dst in
          let (tau', env') := CTranslateType τ env' in 
          let dst' := Evar dst' tau' in
          error_ret (Scall None slice_function [n'; hi'; lo'; dst'], env')

        | Expr.ECast τ e i => err "cast unimplemented" (*TODO: implement in the runtime*)

        | Expr.EUop dst_t op x i => CTranslateUop dst_t op x dst env

        | Expr.EBop dst_t op x y i => CTranslateBop dst_t op x y dst env
                        
        | Expr.ETuple es i =>  (*first create a temp of this tuple. then assign all the values to it. then return this temp  *) 
          let tuple := Expr.TTuple (CTranslateListType es) in
          let (typ, env) := CTranslateType tuple env in
          let* composite := lookup_composite tags_t env tuple in
          let* dst := find_ident tags_t env dst in
          CTranslateTupleAssgn es composite (Evar dst typ) env

        | Expr.EStruct fields i => (*first create a temp of this struct. then assign all the values to it. then return this temp *)
          let struct := Expr.TStruct (CTranslateFieldType fields) in
          let (typ, env) := CTranslateType struct env in
          let* composite := lookup_composite tags_t env struct in
          let* dst := find_ident tags_t env dst in
          CTranslateStructAssgn fields composite (Evar dst typ) env

        | Expr.EHeader fields b i => (*first create a temp of this header. then assign all the values to it. then return this temp*)
          let hdr := Expr.THeader (CTranslateFieldType fields) in
          let (typ, env) := CTranslateType hdr env in
          let* (valid, env) := CTranslateExpr b env in
          let* composite := lookup_composite tags_t env hdr in
          let* dst := find_ident tags_t env dst in
          CTranslateHeaderAssgn fields composite (Evar dst typ) env valid

        | Expr.EHeaderStack fields headers next_index i =>
          let size := Pos.of_nat (length headers) in
          let top_typ := Expr.THeaderStack fields size in
          let (top_typ, env) := CTranslateType top_typ env in
          let* stack := find_ident tags_t env dst in
          let stack_var := Evar stack top_typ in
          let* (next_var,ti,size_var,ts,arr_var,ta, val_typ, val_typ_valid_index) :=
             findStackAttributes stack_var top_typ env in
          let int_size := Econst_int (Integers.Int.repr (Zpos size)) int_signed in
          let int_next := Econst_int (Integers.Int.repr next_index) int_signed in
          let assignSize := Sassign size_var int_size in
          let assignNext := Sassign next_var int_next in
          let env := add_temp tags_t env "i" int_signed in
          let* i := find_ident tags_t env "i" in 
          let i_var := Etempvar i int_signed in
          HeaderStackAssignLoop env arr_var i_var fields headers val_typ

        | _ => 
          let* (e1', env1) := CTranslateExpr e1 env in
          let* (e2', env2) := CTranslateExpr e2 env1 in
          error_ret (Sassign e1' e2', env2)
        end
      | _ =>
      let* (e1', env1) := CTranslateExpr e1 env in
      let* (e2', env2) := CTranslateExpr e2 env1 in
      error_ret (Sassign e1' e2', env2)
      end

    | Stmt.SHeaderStackOp stack Stmt.HSPush n i =>
      let* stack_id := 
        match find_ident_temp_arg tags_t env stack with
        | inl (_, x) => error_ret x
        | _ => find_ident tags_t env stack 
        end
      in
      CTranslatePush stack_id n env

    | Stmt.SHeaderStackOp stack Stmt.HSPop n i => 
      let* stack_id := 
        match find_ident_temp_arg tags_t env stack with
        | inl (_, x) => error_ret x
        | _ => find_ident tags_t env stack 
        end
      in 
      CTranslatePop stack_id n env
    
    (*  *)

    | Stmt.SSetValidity arg val i =>
      let* (arg', env) := CTranslateExpr arg env in 
      let* index := ValidBitIndex arg env in
      let member :=  Efield arg' index type_bool in
      let val := 
        match val with
        | true => Econst_int Integers.Int.one type_bool
        | false => Econst_int Integers.Int.zero type_bool
        end in
      let assign := Sassign member val in
      error_ret (assign , env)  

    end.


  Definition CTranslateParams (params : Expr.params) (env : ClightEnv tags_t ) 
    : list (AST.ident * Ctypes.type) * ClightEnv tags_t  
  :=
    List.fold_left 
      (fun (cumulator: (list (AST.ident * Ctypes.type))*ClightEnv tags_t ) (p: string * paramarg Expr.t Expr.t)
      =>let (l, env') := cumulator in
        let (env', new_id) := new_ident tags_t env' in
        let (ct,env_ct) := match p with 
          | (_, PAIn x) 
          | (_, PADirLess x)
          | (_, PAOut x)
          | (_, PAInOut x) => (CTranslateType x env')
        end in
        let ct_param := match p with 
        | (_, PADirLess _)
        | (_, PAIn _) => ct
        | (_, PAOut x)
        | (_, PAInOut x) => Ctypes.Tpointer ct noattr
        end in
        let s := fst p in
        let env_temp_added := add_temp_arg tags_t env_ct s ct new_id in  (*the temps here are for copy in copy out purpose*)
        (l ++ [(new_id, ct_param)], env_temp_added)) 
    (params) ([],env) . 

  Definition CTranslateConstructorParams (cparams : Expr.constructor_params) (env : ClightEnv tags_t)
    : list (AST.ident * Ctypes.type) * ClightEnv tags_t 
  := 
    List.fold_left 
      (fun (cumulator: (list (AST.ident * Ctypes.type)) * ClightEnv tags_t ) (p: string * Expr.ct)
      =>let (l, env') := cumulator in
        let (env', new_id) := new_ident tags_t env' in
        let (pname, typ) := p in
        let (ct,env_ct) :=  (CTranslateConstructorType typ env') in
        (*don't do copy in copy out*)
        (l ++ [(new_id, ct)], env_ct)) 
    (cparams) ([],env) .
  
  Definition CTranslateExternParams (eparams : F.fs string string) (env : ClightEnv tags_t)
    : list (AST.ident * Ctypes.type) * ClightEnv tags_t 
  := 
    List.fold_left 
      (fun (cumulator: (list (AST.ident * Ctypes.type)) * ClightEnv tags_t ) (p: string * string)
      =>let (l, env') := cumulator in
        let (env', new_id) := new_ident tags_t env' in
        let (pname , ptyp) := p in
        let env' := bind tags_t env' pname new_id in 
        let ct :=  Ctypes.Tstruct $ptyp noattr in
        (* don't do copy in copy out*)
        (l ++ [(new_id, ct)], env')) 
    (eparams) ([],env) .
  
  Definition CCopyIn (fn_params: Expr.params) (env: ClightEnv tags_t )
    : @error_monad string (Clight.statement * ClightEnv tags_t)
  := 
    List.fold_left 
      (fun (cumulator: @error_monad string (Clight.statement * ClightEnv tags_t)) (fn_param: string * (paramarg Expr.t Expr.t))
      =>let (name, t) := fn_param in 
        let* (prev_stmt, prev_env) := cumulator in
        let* (oldid, tempid) := find_ident_temp_arg tags_t env name in
        match t with
          | PAIn t
          | PADirLess t => 
            let (ct, env_ct) := CTranslateType t prev_env in
            let new_stmt := Sassign (Evar tempid ct) (Evar oldid ct) in
            error_ret (Ssequence prev_stmt new_stmt, env_ct)
          | PAOut t
          | PAInOut t => 
            let (ct, env_ct) := CTranslateType t prev_env in
            let new_stmt := Sassign (Evar tempid ct) (Ederef (Evar oldid (Ctypes.Tpointer ct noattr)) ct) in
            error_ret (Ssequence prev_stmt new_stmt, env_ct)
        end
      ) fn_params (error_ret (Sskip, env)).

  Definition CCopyOut (fn_params: Expr.params) (env: ClightEnv tags_t )
    : @error_monad string (Clight.statement * ClightEnv tags_t) 
  := 
    List.fold_left 
      (fun (cumulator: @error_monad string (Clight.statement * ClightEnv tags_t)) (fn_param: string * (paramarg Expr.t Expr.t))
      =>let (name, t) := fn_param in 
        let* (prev_stmt, prev_env) := cumulator in
        let* (oldid, tempid) := find_ident_temp_arg tags_t env name in 
        match t with
        | PADirLess t
        | PAIn t => 
          let (ct, env_ct) := CTranslateType t prev_env in
          let new_stmt := Sassign (Evar oldid ct) (Evar tempid ct) in
          error_ret (Ssequence prev_stmt new_stmt, env_ct)
        | PAOut t
        | PAInOut t => 
          let (ct, env_ct) := CTranslateType t prev_env in
          let new_stmt := Sassign (Ederef (Evar oldid (Ctypes.Tpointer ct noattr)) ct) (Evar tempid ct) in
          error_ret (Ssequence prev_stmt new_stmt, env_ct)
        end
      ) fn_params (error_ret (Sskip, env)).

  (*return the list of args for the params*)
  Definition CFindTempArgs (fn_params: Expr.params) (env: ClightEnv tags_t )
    : @error_monad string (list Clight.expr) 
  := 
    List.fold_left 
      (fun (cumulator: @error_monad string (list Clight.expr)) (fn_param: string * (paramarg Expr.t Expr.t))
        =>let (name, t) := fn_param in
          let* (oldid, tempid) := find_ident_temp_arg tags_t env name in
          let* cumulator := cumulator in
          match t with 
          | PADirLess t
          | PAIn t
          | PAOut t
          | PAInOut t =>
            let (ct, _) := CTranslateType t env in
            error_ret (cumulator ++ [Evar tempid ct])
          end
      ) fn_params (error_ret []).

  (*return the list of args for the params but adding directions.
  change the temp to ref temp if it is a out parameter.
  *)
  Definition CFindTempArgsForCallingSubFunctions (fn_params: Expr.params) (env: ClightEnv tags_t )
    : @error_monad string (list Clight.expr) 
  := 
    List.fold_left 
      (fun (cumulator: @error_monad string (list Clight.expr)) (fn_param: string * (paramarg Expr.t Expr.t))
      =>let (name, t) := fn_param in
        let* (oldid, tempid) := find_ident_temp_arg tags_t env name in
        let* cumulator := cumulator in 
        let (ct, _) := 
          match t with 
          | PADirLess t
          | PAIn t
          | PAOut t
          | PAInOut t => CTranslateType t env 
          end in 
        let var := 
          match t with
          | PADirLess t
          | PAIn t => Evar tempid ct
          | PAOut t
          | PAInOut t => Eaddrof (Evar tempid ct) (Tpointer ct noattr)
          end in
        error_ret (cumulator ++ [var])
      ) fn_params (error_ret []).


  Definition CTranslateArrow (signature : Expr.arrowT) (env : ClightEnv tags_t )
    : (list (AST.ident * Ctypes.type)) * Ctypes.type * ClightEnv tags_t  
  := 
    let  '(Arrow pas ret) := signature in
    let (fn_params, env_params_created) := CTranslateParams pas env in 
    match ret with 
    | None => (fn_params, Ctypes.Tvoid, env_params_created)
    | Some return_t => 
      let (ct, env_ct):= CTranslateType return_t env_params_created in 
      (fn_params, ct , env_ct)
    end.
      
  Definition PaFromArrow (arrow: Expr.arrowT) : (Expr.params):=
    let '(Arrow pas ret) := arrow in
    pas.

  Definition CTranslatePatternVal (p : Parser.pat) (env: ClightEnv tags_t)
    : @error_monad string (Clight.statement * ident * ClightEnv tags_t) := 
    match p with 
    | Parser.PATBit width val =>
        let (env, fresh_id) := new_ident tags_t env in 
        let fresh_name := String.append "_p_e_t_r_4_" (BinaryString.of_pos fresh_id) in
        let env := add_var tags_t env fresh_name bit_vec in 
        let* dst := find_ident tags_t env fresh_name in
        let (env', val_id) := find_BitVec_String tags_t env val in 
        let w := Econst_int (Integers.Int.repr (Z.of_N width)) (int_signed) in
        let signed := Econst_int (Integers.Int.zero) (type_bool) in 
        let val' := Evar val_id Cstring in
        let dst' := Eaddrof (Evar dst bit_vec) TpointerBitVec in
        error_ret ((Scall None bitvec_init_function [dst'; signed; w; val']), dst, env')
        
    | Parser.PATInt width val => 
        let (env, fresh_id) := new_ident tags_t env in 
        let fresh_name := String.append "_p_e_t_r_4_" (BinaryString.of_pos fresh_id) in
        let env := add_var tags_t env fresh_name bit_vec in 
        let* dst := find_ident tags_t env fresh_name in
        let (env', val_id) := find_BitVec_String tags_t env val in 
        let w := Econst_int (Integers.Int.repr (Zpos width)) (int_signed) in
        let signed := Econst_int (Integers.Int.one) (type_bool) in 
        let val' := Evar val_id Cstring in
        let dst' := Eaddrof (Evar dst bit_vec) TpointerBitVec in
        error_ret ((Scall None bitvec_init_function [dst'; signed; w; val']), dst, env')

    | _ => err "not a pattern value"
    end.

  Definition CTranslatePatternMatch (input: Clight.expr) (p: Parser.pat) (env: ClightEnv tags_t)
    : @error_monad string (Clight.statement * ident * ClightEnv tags_t) :=
    let (env, fresh_id) := new_ident tags_t env in 
    let fresh_name := String.append "_p_e_t_r_4_" (BinaryString.of_pos fresh_id) in
    let env := add_var tags_t env fresh_name type_bool in 
    let* dst := find_ident tags_t env fresh_name in
    let dst' := Eaddrof (Evar dst type_bool) TpointerBool in
    match p with
    | Parser.PATWild => 
      let assign := Sassign dst' (Econst_int (Integers.Int.one) (type_bool)) in 
      error_ret (assign, dst, env)
      
    | Parser.PATMask  p1 p2 => 
      let* (init1, var_left, env) := CTranslatePatternVal p1 env in
      let* (init2, var_right, env) := CTranslatePatternVal p2 env in
      let (env, fresh_id) := new_ident tags_t env in 
      let fresh_name := String.append "_p_e_t_r_4_" (BinaryString.of_pos fresh_id) in
      let env := add_var tags_t env fresh_name bit_vec in 
      let* inputand := find_ident tags_t env fresh_name in
      let (env, fresh_id) := new_ident tags_t env in 
      let fresh_name := String.append "_p_e_t_r_4_" (BinaryString.of_pos fresh_id) in
      let env := add_var tags_t env fresh_name bit_vec in 
      let* valueand := find_ident tags_t env fresh_name in
      let inand' := Eaddrof (Evar inputand bit_vec) TpointerBitVec in
      let valand' := Eaddrof (Evar valueand bit_vec) TpointerBitVec in
      let assign_in := Scall None (bop_function _interp_bitwise_and) [inand'; input; (Evar var_right bit_vec)] in
      let assign_val := Scall None (bop_function _interp_bitwise_and) [valand'; (Evar var_left bit_vec); (Evar var_right bit_vec)] in
      let assign := Scall None (bop_function _interp_beq) [dst'; (Evar inputand bit_vec); (Evar valueand bit_vec)] in
      let stmts := 
        (Ssequence init1
        (Ssequence init2
        (Ssequence assign_in
        (Ssequence assign_val
        assign
        ))))  in
      error_ret (stmts, dst, env)

    | Parser.PATRange p1 p2 => 
      let* (init1, var_left, env) := CTranslatePatternVal p1 env in
      let* (init2, var_right, env) := CTranslatePatternVal p2 env in
      let (env, fresh_id) := new_ident tags_t env in 
      let fresh_name := String.append "_p_e_t_r_4_" (BinaryString.of_pos fresh_id) in
      let env := add_var tags_t env fresh_name type_bool in 
      let* lefttrue := find_ident tags_t env fresh_name in
      let (env, fresh_id) := new_ident tags_t env in 
      let fresh_name := String.append "_p_e_t_r_4_" (BinaryString.of_pos fresh_id) in
      let env := add_var tags_t env fresh_name type_bool in 
      let* righttrue := find_ident tags_t env fresh_name in
      let lefttrue' := Eaddrof (Evar lefttrue type_bool) TpointerBool in
      let righttrue' := Eaddrof (Evar righttrue type_bool) TpointerBool in
      let assign_left := Scall None (bop_function _interp_bge) [lefttrue'; input; (Evar var_left bit_vec)] in
      let assign_right := Scall None (bop_function _interp_ble) [righttrue'; input; (Evar var_right bit_vec)] in
      let and_expr :=  Ebinop Oand (Evar lefttrue type_bool) (Evar righttrue type_bool) type_bool in
      let assign := Sassign dst' and_expr in 
      let stmts := 
        (Ssequence init1
        (Ssequence init2
        (Ssequence assign_left
        (Ssequence assign_right
        assign
        ))))  in
      error_ret (stmts, dst, env)

    | Parser.PATInt width val
    | Parser.PATBit width val => 
      let*  (init, var, env) := CTranslatePatternVal p env in
      let assign := 
        Scall None (bop_function _interp_beq) [dst'; input; (Evar var bit_vec)] in
      let stmts := Ssequence init assign in
      error_ret (stmts, dst, env)

    | Parser.PATTuple ps => 
      err "not a simple pattern match"
    end.


  Definition CTranslateParserExpressionVal
    (pe: Parser.e tags_t) 
    (env: ClightEnv tags_t)
    (rec_call_args : list (Clight.expr))
    : @error_monad string (Clight.statement * ClightEnv tags_t) :=
    match pe with 
    | Parser.PGoto st i => 
      match st with
      | Parser.STStart =>
        let* (start_f, start_id) := (lookup_function tags_t env "start") in
        error_ret (Scall None (Evar start_id (Clight.type_of_function start_f)) rec_call_args, env)

      | Parser.STAccept =>
        error_ret ( Sreturn None, env)
         
      | Parser.STReject => err "not sure how to implement error state" (*TODO: implement*)
      
      | Parser.STName x => 
        let*  (x_f, x_id) := lookup_function tags_t env x in
        error_ret (Scall None (Evar x_id (Clight.type_of_function x_f)) rec_call_args, env)
      end

    | Parser.PSelect exp def cases i => 
      err "nested select expression, currently unsupported"
    end.
    

  Definition CTranslateParserExpression 
    (pe: Parser.e tags_t) 
    (env: ClightEnv tags_t)
    (rec_call_args : list (Clight.expr))
    : @error_monad string (Clight.statement * ClightEnv tags_t) :=
    match pe with 
    | Parser.PSelect exp def cases i => 
      let* (input, env) := CTranslateExpr exp env in
      let* (default_stmt, env) := CTranslateParserExpressionVal def env rec_call_args in
      let fold_function 
          (elt: Parser.pat * Parser.e tags_t) 
          (cumulator: @error_monad string (Clight.statement * ClightEnv tags_t)) :=
          let '(p, action) := elt in
          let* (fail_stmt, env') := cumulator in
          let* (match_statement, this_match, env') := CTranslatePatternMatch input p env' in
          let* (success_statement, env') := CTranslateParserExpressionVal action env' rec_call_args in 
          let new_stmt := Ssequence match_statement (Sifthenelse (Evar this_match type_bool) success_statement fail_stmt) in
          error_ret (new_stmt, env')
      in
      List.fold_right fold_function (error_ret (default_stmt, env)) cases
    
    | _ => CTranslateParserExpressionVal pe env rec_call_args
    end.

  Definition CTranslateParserState (st : Parser.state_block tags_t) (env: ClightEnv tags_t ) (params: list (AST.ident * Ctypes.type))
    : @error_monad string (Clight.function * ClightEnv tags_t ) :=
    let '(Parser.State stmt pe) := st in
    let rec_call_args := List.map (fun (x: AST.ident * Ctypes.type) => Etempvar (fst x) (snd x)) params in
    let* (stmt', env') := CTranslateStatement stmt env in
    let* (estmt, env') := CTranslateParserExpression pe env' rec_call_args in
    error_ret (Clight.mkfunction
          Ctypes.Tvoid
          (AST.mkcallconv None true true)
          params
          (CCompEnv.get_vars tags_t env')
          (CCompEnv.get_temps tags_t env')
          (Ssequence stmt' estmt)
          , (set_temp_vars tags_t env env')).

  Definition CTranslateTopParser (parsr: TopDecl.d tags_t) (env: ClightEnv tags_t ) 
    (init: Clight.statement) (instance_name: string) 
    : @error_monad string (ClightEnv tags_t )
  :=
    match parsr with
    | TopDecl.TPParser p _ eps params st states i =>
      let (fn_eparams, env_eparams) := CTranslateExternParams eps env in 
      let (fn_params, env_params):= CTranslateParams params env_eparams in 
      let* (copyin, env_copyin) := CCopyIn params env_params in
      let* (copyout, env_copyout) := CCopyOut params env_copyin in   (*copy in and copy out may need to copy cparams and eparams as well*)
      let state_names := F.keys states in 
      let fn_params := fn_eparams ++ fn_params in 
      (*all functions inside one top parser declaration should have the same parameter*)
      let fn_sig := 
        (Clight.mkfunction 
        Ctypes.Tvoid 
        (AST.mkcallconv None true true) 
        fn_params
        []
        []
        Sskip ) in
      let env_start_fn_sig_declared := CCompEnv.add_function tags_t env_copyout "start" fn_sig in
      let env_fn_sig_declared := 
        List.fold_left 
          (fun (cumulator : ClightEnv tags_t ) (state_name: string) =>
            CCompEnv.add_function tags_t cumulator state_name fn_sig
          ) state_names  env_start_fn_sig_declared in
      
      let* env_fn_declared := 
        List.fold_left
        (fun (cumulator: @error_monad string (ClightEnv tags_t )) (state_name: string) => 
          let* env' := cumulator in
          match Env.find state_name states with 
            | None => err "state name not in states"
            | Some sb =>
            let* (f, env_f_translated) := CTranslateParserState sb env' fn_params in
            error_ret (CCompEnv.update_function tags_t env_f_translated state_name f)
          end
        ) state_names (error_ret (set_temp_vars tags_t env env_fn_sig_declared)) in
      
      (*finished declaring all the state blocks except start state*)
      let* (f_start, env_start_translated) := CTranslateParserState st (set_temp_vars tags_t env env_fn_declared) fn_params in 
      let env_start_declared := CCompEnv.update_function tags_t env_start_translated "start" f_start in
      let env_start_declared := set_temp_vars tags_t env_copyout env_start_declared in
      let* (start_f, start_id) := (lookup_function tags_t env_start_declared "start") in
      let* call_args := CFindTempArgsForCallingSubFunctions params env_start_declared in
      let e_call_args := List.map (fun (x: AST.ident * Ctypes.type) => Etempvar (fst x) (snd x)) fn_eparams in
      let call_args := e_call_args ++ call_args in
      let fn_body := 
        Ssequence init
        (Ssequence copyin 
        (Ssequence 
        (Scall None (Evar start_id (Clight.type_of_function start_f)) call_args)
        copyout)) in 
      let top_function := 
        (Clight.mkfunction
        Ctypes.Tvoid
        (AST.mkcallconv None true true)
        fn_params
        (get_vars tags_t env_start_declared)
        (get_temps tags_t env_start_declared)
        fn_body)
      in
      let env_topfn_added := CCompEnv.add_function tags_t env_start_declared instance_name top_function in
      error_ret ( set_temp_vars tags_t env env_topfn_added)
    | _ => err "not parser"
    end.


  Definition CTranslateAction 
  (signature: Expr.params) (body: Stmt.s tags_t) 
  (env: ClightEnv tags_t ) (top_fn_params: list (AST.ident * Ctypes.type))
  (top_signature: Expr.params)
  : @error_monad string (Clight.function* ClightEnv tags_t ):= 
  let (fn_params, env_params_created) := CTranslateParams signature env in
  let fn_params := top_fn_params ++ fn_params in 
  let full_signature := top_signature ++ signature in
  let* (copyin, env_copyin) := CCopyIn full_signature env_params_created in
  let* (copyout, env_copyout) := CCopyOut full_signature env_copyin in
  let* (c_body, env_body_translated) := CTranslateStatement body env_copyout in
  let body:= Ssequence copyin (Ssequence c_body copyout) in
  error_ret (
    (Clight.mkfunction 
      Ctypes.Tvoid
      (AST.mkcallconv None true true)
      fn_params 
      (get_vars tags_t env_body_translated)
      (get_temps tags_t env_body_translated)
      body), (set_temp_vars tags_t env env_body_translated))
  .

  Fixpoint CTranslateControlLocalDeclaration 
  (ct : Control.d tags_t) (env: ClightEnv tags_t ) 
  (top_fn_params: list (AST.ident * Ctypes.type))
  (top_signature: Expr.params)
  : @error_monad string (ClightEnv tags_t )
  := match ct with
  | Control.CDSeq d1 d2 i=> 
    let* env1 := (CTranslateControlLocalDeclaration d1 env top_fn_params top_signature) in
    CTranslateControlLocalDeclaration d2 env1 top_fn_params top_signature
    
  | Control.CDAction a params body i => 
    let* (f, env_action_translated) := CTranslateAction params body env top_fn_params top_signature in
    error_ret (CCompEnv.add_function tags_t env_action_translated a f)

  | Control.CDTable t (Control.Table ems acts) i => error_ret env (*TODO: implement table*)
  end.
  
  Definition CTranslateTopControl (ctrl: TopDecl.d tags_t) (env: ClightEnv tags_t) 
    (init: Clight.statement) (instance_name: string)
    : @error_monad string (ClightEnv tags_t )
  := 
    match ctrl with
    | TopDecl.TPControl c _ eps params body blk i => 
      let (fn_eparams, env_top_fn_eparam) := CTranslateExternParams eps env in
      let (fn_params, env_top_fn_param) := CTranslateParams params env_top_fn_eparam in
      let* (copyin, env_copyin) := CCopyIn params env_top_fn_param in 
      let* (copyout, env_copyout) := CCopyOut params env_copyin in 
      let fn_params := fn_eparams ++ fn_params in 
      let* env_local_decled := CTranslateControlLocalDeclaration body env_copyout fn_params params in
      let* (apply_blk, env_apply_block_translated) := CTranslateStatement blk env_local_decled in
      let body:= Ssequence init (Ssequence copyin (Ssequence apply_blk copyout)) in
      let top_fn := 
        Clight.mkfunction 
          Ctypes.Tvoid 
          (AST.mkcallconv None true true)
          fn_params 
          (get_vars tags_t env_apply_block_translated)
          (get_temps tags_t env_apply_block_translated)
          body in
      let env_top_fn_declared := 
        CCompEnv.add_function tags_t env_local_decled instance_name top_fn in
      error_ret (set_temp_vars tags_t env env_top_fn_declared) 

    | _ => err "not a top control"
    end.


  
  Definition CTranslateFunction (funcdecl : TopDecl.d tags_t) (env: ClightEnv tags_t )
    : @error_monad string (ClightEnv tags_t )
  := 
    match funcdecl with
    | TopDecl.TPFunction name _ signature body _ => 
      let '(fn_params, fn_return, env_params_created) := CTranslateArrow signature env in 
      let paramargs := PaFromArrow signature in
      let* (copyin, env_copyin) := CCopyIn paramargs env_params_created in
      let* (copyout, env_copyout) := CCopyOut paramargs env_copyin in
      let* (c_body, env_body_translated) := CTranslateStatement body env_copyout in
      let body:= Ssequence copyin (Ssequence c_body copyout) in
      let top_function := 
        (Clight.mkfunction 
          fn_return
          (AST.mkcallconv None true true)
          fn_params 
          (get_vars tags_t env_body_translated)
          (get_temps tags_t env_body_translated)
          body) in
      error_ret (set_temp_vars tags_t env (CCompEnv.add_function tags_t env_params_created name top_function))

    | _ => err "not a function"
    end.
  
  Definition InjectConstructorArg (arg_name: string) 
    (arg: Expr.constructor_arg tags_t) 
    (cumulator: @error_monad string (ClightEnv tags_t * Clight.statement))
    : @error_monad string (ClightEnv tags_t * Clight.statement) := 
    let* (env, st) := cumulator in 
    match arg with 
    | Expr.CAExpr e => 
      let* (init, env) := 
      match e with 
      | Expr.EBool b i =>
        let env := add_var tags_t env arg_name type_bool in 
        let* val_id := find_ident tags_t env arg_name in
        let initialize := 
          if b then 
            Sassign (Evar val_id type_bool) (Econst_int (Integers.Int.zero) (type_bool)) 
          else 
            Sassign (Evar val_id type_bool) (Econst_int (Integers.Int.one) (type_bool)) 
        in
        error_ret (initialize, env)
      | Expr.EBit width val i => 
        let env := add_var tags_t env arg_name bit_vec in 
        let* dst := find_ident tags_t env arg_name in
        let (env', val_id) := find_BitVec_String tags_t env val in 
        let w := Econst_int (Integers.Int.repr (Z.of_N width)) (int_signed) in
        let signed := Econst_int (Integers.Int.zero) (type_bool) in 
        let val' := Evar val_id Cstring in
        let dst' := Eaddrof (Evar dst bit_vec) TpointerBitVec in
        error_ret (Scall None bitvec_init_function [dst'; signed; w; val'], env')
      | Expr.EInt width val i => 
        let env := add_var tags_t env arg_name bit_vec in 
        let* dst := find_ident tags_t env arg_name in
        let (env', val_id) := find_BitVec_String tags_t env val in 
        let w := Econst_int (Integers.Int.repr (Zpos width)) (int_signed) in
        let signed := Econst_int (Integers.Int.one) (type_bool) in 
        let val' := Evar val_id Cstring in
        let dst' := Eaddrof (Evar dst bit_vec) TpointerBitVec in
        error_ret (Scall None bitvec_init_function [dst'; signed; w; val'], env')
      | _ => err "not folded constant"
        end in 
        error_ret (env, Ssequence st init)
    | Expr.CAName x =>
      let* instance_id := CCompEnv.find_ident tags_t env x in 
      error_ret (CCompEnv.bind tags_t env arg_name instance_id, st)
    end.

  Definition InjectConstructorArgs (env: ClightEnv tags_t) (cargs: Expr.constructor_args tags_t)
    : @error_monad string (ClightEnv tags_t * Clight.statement) :=
    F.fold InjectConstructorArg cargs (error_ret (env, Sskip)).

  Fixpoint CTranslateTopDeclaration (d: TopDecl.d tags_t) (env: ClightEnv tags_t ) : @error_monad string (ClightEnv tags_t )
  := 
  match d with
  | TopDecl.TPSeq d1 d2 i => 
    let* env1 := CTranslateTopDeclaration d1 env in
    CTranslateTopDeclaration d2 env1 

  | TopDecl.TPInstantiate c x _ args i => 
    (* let* (init', env') := CTranslateStatement args_init env in *)
    (* Some (set_main_init tags_t (set_instantiate_cargs tags_t env args) Sskip) *)
    (*TODO: Translate each instantiate into a function*)
    (*TODO: Maybe we also want an abstract interpretation in the statementize pass?*)
    let env := add_tpdecl tags_t env x d in
    let env := if (x == "main") then set_instantiate_cargs tags_t env args else env in
    match lookup_topdecl tags_t env c with 
    | inl tpdecl => 
      match tpdecl with
      | TopDecl.TPParser _ _ _ _ _ _ _  => 
        let* (env, init) := InjectConstructorArgs env args in
         CTranslateTopParser tpdecl env init x

      | TopDecl.TPControl _ _ _ _ _ _ _ =>
        let* (env, init) := InjectConstructorArgs env args in 
        CTranslateTopControl tpdecl env init x 

      | _ => error_ret env
      end
    | _ => error_ret env
    end
  | TopDecl.TPFunction _ _ _ _ _ => CTranslateFunction d env
  | TopDecl.TPExtern e _ cparams methods i => err "don't know how to handle extern" (*TODO: implement*)
  | TopDecl.TPControl name _ _ _ _ _ _ => error_ret (add_tpdecl tags_t env name d)
  (* CTranslateTopControl d env *)
  | TopDecl.TPParser name _ _ _ _ _ _ => error_ret (add_tpdecl tags_t env name d)
   (* CTranslateTopParser d env *)
  | TopDecl.TPPackage name _ _ _ =>  error_ret (add_tpdecl tags_t env name d) (*TODO: implement*)
  end.

  Definition Compile (prog: TopDecl.d tags_t) : Errors.res (Clight.program) := 
    let init_env := CCompEnv.newClightEnv tags_t in
    let main_id := $"main" in 
    match CTranslateTopDeclaration prog init_env with
    | inr m => Errors.Error (Errors.msg m)
    | inl env_all_declared => 
      match CCompEnv.get_functions tags_t env_all_declared with
      | inr _ => Errors.Error (Errors.msg "can't find all the declared functions")
      | inl f_decls => 
      let f_decls := List.map 
        (fun (x: AST.ident * Clight.function) 
        => let (id, f) := x in 
        (id, AST.Gfun(Ctypes.Internal f))) f_decls in
      let typ_decls := CCompEnv.get_composites tags_t env_all_declared in
      
      let main_decl :=
      AST.Gfun (Ctypes.Internal (main_fn tags_t env_all_declared (get_instantiate_cargs tags_t env_all_declared)))
      in 
      let gvars := get_globvars tags_t env_all_declared in 
      let gvars := List.map 
        (fun (x: AST.ident * globvar Ctypes.type)
        => let (id, v) := x in 
        (id, AST.Gvar(v))) gvars in
      let res_prog : Errors.res (program function) := make_program 
        (
          (* RunTime.composites++  *)
          typ_decls)
        (gvars ++ ((main_id, main_decl):: f_decls))
        [] main_id
      in
      res_prog
      end
    end.

  Definition Compile_print (prog: TopDecl.d tags_t): unit := 
    match Compile prog with
    | Errors.Error e => tt
    | Errors.OK prog => print_Clight prog
    end.  
End CCompSel.

Definition helloworld_program_sel := Statementize.TranslateProgram helloworld_program.
Definition test := 
  match helloworld_program_sel with 
  | inl helloworld_program_sel => CCompSel.Compile_print nat helloworld_program_sel
  | inr _ => tt
  end.
