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
Require Import Poulet4.P4sel.P4sel.
Require Import Poulet4.Monads.Monad.
Require Import Poulet4.Monads.Option.
Require Poulet4.P4sel.RemoveSideEffect.
Require Import Poulet4.Ccomp.CCompEnv.
Require Import Poulet4.Ccomp.Helloworld.
Require Import Poulet4.Ccomp.CV1Model.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope clight_scope.
Import Clightdefs.ClightNotations.
Require Import Poulet4.Ccomp.Petr4Runtime.
Module P := P4cub.
Module F := P.F.
Module E := P.Expr.
Module ST := P.Stmt.
Module PA := P.Parser.
Module CT := P.Control.ControlDecl.
Module TD := P.TopDecl.
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
  
  Fixpoint CTranslateType (p4t : P4cub.Expr.t) (env: ClightEnv tags_t) : Ctypes.type * ClightEnv tags_t:=
    match p4t with
    | P4cub.Expr.TBool => (Ctypes.type_bool, env)
    | P4cub.Expr.TBit (w) => (bit_vec,env)
    | P4cub.Expr.TInt (w) => (bit_vec, env)
    | P4cub.Expr.TVar name => (Ctypes.Tvoid, env) (*TODO: implement, I'm really lost on this*)
    | P4cub.Expr.TError => (Ctypes.Tvoid, env) (*TODO: implement what exactly is an error type? Should it be depending on the target?*)
    | P4cub.Expr.TMatchKind => (int_unsigned, env) (*I guess this should just be an enum, aka an int.*)

    | P4cub.Expr.TTuple (ts) => 
        match lookup_composite tags_t env p4t with
        | Some comp => (Ctypes.Tstruct (Ctypes.name_composite_def comp) noattr, env)
        | None => 
        let (env_top_id, top_id) := CCompEnv.new_ident tags_t env in
        let (members ,env_fields_declared):= 
        List.fold_left 
        (fun (cumulator: Ctypes.members*ClightEnv tags_t)  (field: E.t) 
        => let (members_prev, env_prev) := cumulator in 
           let (new_t, new_env):= CTranslateType field env_prev in
           let (new_env, new_id):= CCompEnv.new_ident tags_t new_env in
           (members_prev ++ [(new_id, new_t)], new_env))
        ts ([],env_top_id) in
        let comp_def := Ctypes.Composite top_id Ctypes.Struct members Ctypes.noattr in
        let env_comp_added := CCompEnv.add_composite_typ tags_t env_fields_declared p4t comp_def in
        (Ctypes.Tstruct top_id noattr, env_comp_added)
        end

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

    | P4cub.Expr.THeader (fields) => 
    (* struct plus a validity boolean value *)
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

    | P4cub.Expr.THeaderStack fields n=> 
      match lookup_composite tags_t env p4t with
      | Some comp => (Ctypes.Tstruct (Ctypes.name_composite_def comp) noattr, env)
      | None =>
        let header := P4cub.Expr.THeader fields in
        let (hdarray, env_hdarray) := 
        match lookup_composite tags_t env header with
        | Some comp => (Ctypes.Tarray (Ctypes.Tstruct (Ctypes.name_composite_def comp) noattr) (Zpos n) noattr, env)
        | None => 
        let (env_top_id, top_id) := CCompEnv.new_ident tags_t env in
        let (env_valid, valid_id) := new_ident tags_t env_top_id in 
        let (members ,env_fields_declared):= 
        F.fold 
        (fun (k: string) (field: E.t) (cumulator: Ctypes.members*ClightEnv tags_t ) 
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

  Definition CTranslateConstructorType (ct: P4cub.Expr.ct) (env: ClightEnv tags_t) : Ctypes.type * ClightEnv tags_t :=
  match ct with 
  | P4cub.Expr.CTType type => CTranslateType type env
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
            Some (next_var,ti,size_var,ts,arr_var,ta, val_typ, val_typ_valid_index)
            |_ => None
            end
          | _ => None
          end
        | _ => None
        end  
      |_ => None
      end
    | _ => None
    end.
  
  Definition ArrayAccess (arr : Clight.expr) (index : Clight.expr) (result_t: Ctypes.type) : Clight.expr
  := 
    Ederef 
    (Ebinop Oadd arr index (Tpointer result_t noattr))
    result_t.

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
                                  let* id' := find_ident tags_t env' x in
                                  Some (Evar id' cty, env')
                        end
                        end

    | E.EExprMember y ty x i => 
                        let(cty, env_ty):= CTranslateType ty env in
                        let* (x', env') := CTranslateExpr x env_ty in
                        match ty with
                        | E.TStruct(f) =>
                          let* n := F.get_index y f in
                          let* t_member :=  F.get y f in
                          let (ctm, env_ctm) := CTranslateType t_member env' in
                          let em :=
                            match ctm with 
                            | (Tstruct st _) => if(st == RunTime._BitVec) 
                                                    then Ederef (Clight.Efield x' (Pos.of_nat n) (Tpointer ctm noattr)) (ctm)
                                                    else (Clight.Efield x' (Pos.of_nat n) ctm)
                            | _ => (Clight.Efield x' (Pos.of_nat n) ctm) end in 
                          Some (em, env_ctm)
                          
                        | E.THeader(f) => 
                        (* +1 for the valid bit *)
                          let* n := F.get_index y f in
                          let* t_member := F.get y f in
                          let (ctm, env_ctm) := CTranslateType t_member env' in
                          let em :=
                            match ctm with 
                            | (Tstruct st _) => if(st == RunTime._BitVec) 
                                                    then Ederef (Clight.Efield x' (Pos.of_nat (n+1)) (Tpointer ctm noattr)) (ctm)
                                                    else (Clight.Efield x' (Pos.of_nat (n+1)) ctm)
                            | _ => (Clight.Efield x' (Pos.of_nat (n+1)) ctm) end in 
                          Some (em, env_ctm)
                        | _ => None
                        end

    | E.EHeaderStackAccess stack index i => 
      let (stack_t,env) := CTranslateType (E.cub_type_of tags_t stack) env in 
      let* (stack, env) :=  CTranslateExpr stack env in
      let* (next_var,ti,size_var,ts,arr_var,ta, val_typ, val_typ_valid_index) 
        := findStackAttributes stack stack_t env in
      Some (ArrayAccess arr_var (Econst_int (Integers.Int.repr index) int_signed ) val_typ, env)

    | E.EError x i => None (*TODO: implement*)
    | E.EMatchKind mk i => None (*TODO : implement*)
    | _ => None (*Not Allowed*)
    end.

  Definition CTranslateExprList (el : list (E.e tags_t)) (env: ClightEnv tags_t ): option ((list Clight.expr) * ClightEnv tags_t ) :=
    let Cumulator: Type := option (list Clight.expr * ClightEnv tags_t ) in 
    let transformation (A: Cumulator) (B: E.e tags_t) : Cumulator := 
      let* (el', env') := A in 
      let* (B', env'') := CTranslateExpr B env' in
      Some(el' ++ [B'], env'') in
    List.fold_left  (transformation) el (Some ([],env)).
  
  Definition CTranslateDirExprList (el: E.args tags_t) (env: ClightEnv tags_t ) : option ((list Clight.expr) * ClightEnv tags_t ) := 
    let Cumulator : Type := option (list Clight.expr * ClightEnv tags_t ) in 
    let transformation (A: Cumulator) (B: string * (P.paramarg (E.t*(E.e tags_t)) (E.t*(E.e tags_t)))) : Cumulator := 
      let* (el', env') := A in
      match B with 
      | (_, P.PAIn(t, e))
      | (_, P.PADirLess(t,e)) => 
        let* (e', env'') := CTranslateExpr e env' in
        Some (el' ++ [e'], env'')
      | (_, P.PAOut(t, e)) 
      | (_, P.PAInOut(t, e)) =>
        let (ct, env_ct):= CTranslateType t env' in 
        let*  (e', env'') := CTranslateExpr e env_ct in
        let e' := Eaddrof e' (Tpointer ct noattr) in 
        Some (el' ++ [e'], env'')
      end
    in 
    List.fold_left  (transformation) el (Some ([],env)).
  
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

  Definition ValidBitIndex (arg: E.e tags_t) (env: ClightEnv tags_t ) : option AST.ident
  :=
    let* comp:= lookup_composite tags_t env (E.cub_type_of tags_t arg) in
    match comp with
    | Ctypes.Composite _ Ctypes.Struct m _ =>
    match m with
    | [] => None
    | (id,t) :: _ => Some id
    end
    | _ => None
    end.
  
  Definition HeaderStackIndex := ValidBitIndex.
  
  Definition HeaderStackSize (arg: E.e tags_t) (env: ClightEnv tags_t ) : option AST.ident
  :=
    let* comp := lookup_composite tags_t env (E.cub_type_of tags_t arg) in
    match comp with
    | Ctypes.Composite _ Ctypes.Struct m _=>
      match m with
        | (_,_) :: (id,t) :: _ => Some id
        | _ => None
      end
    | _ => None
    end.

  Definition CTranslateUop 
    (dst_t: P4cub.Expr.t)
    (op: P4cub.Expr.uop)
    (arg: E.e tags_t)
    (dst: string)
    (env: ClightEnv tags_t ): option(Clight.statement * ClightEnv tags_t ) 
  := 
    let* dst' :=  find_ident tags_t env dst in 
    let (dst_t', env') := CTranslateType dst_t env in 
    let dst' := Evar dst' dst_t' in
    let* (arg', env_arg) := CTranslateExpr arg env' in
    let arg_ref := Eaddrof arg' (Tpointer (Clight.typeof arg') noattr) in
    let dst_ref := Eaddrof dst' (Tpointer dst_t' noattr) in  
    match op with
    | P4cub.Expr.Not => 
      let not_expr := Eunop Onotbool arg' Ctypes.type_bool in 
      Some (Sassign dst' not_expr, env_arg)

    | P4cub.Expr.BitNot => 
      (*need implementation in runtime*)
      Some (Scall None (uop_function _interp_bitwise_and) [arg_ref; dst_ref], env_arg)

    | P4cub.Expr.UMinus => 
      Some (Scall None (uop_function _eval_uminus)  [arg_ref; dst_ref], env_arg)

    | P4cub.Expr.IsValid =>
      let* index := ValidBitIndex arg env_arg in
      let member :=  Efield arg' index type_bool in
      Some (Sassign dst' member, env_arg)

    | P4cub.Expr.NextIndex =>
      let* index := HeaderStackIndex arg env_arg in
      let member := Efield arg' index int_signed in
      let increment := Ebinop Oadd member (Econst_int Integers.Int.one int_signed) int_signed in
      let assign := Sassign member increment in 
      let to_dst := Sassign dst' arg' in
      Some (Ssequence assign to_dst, env_arg) 

    | P4cub.Expr.Size => 
      let* index := HeaderStackSize arg env_arg in
      let member := Efield arg' index int_signed in
      let to_dst := Sassign dst' member in
      Some (to_dst, env_arg) 

    | _ => None  
    end.

  Definition CTranslateBop 
    (dst_t: P4cub.Expr.t)
    (op: P4cub.Expr.bop)
    (le: E.e tags_t)
    (re: E.e tags_t)
    (dst: string)
    (env: ClightEnv tags_t ) : option (Clight.statement * ClightEnv tags_t )
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
      | P4cub.Expr.TInt _ => true
      | _ => false
      end in
    match op with
    | P4cub.Expr.Plus => Some (Scall None (bop_function _interp_bplus) [dst_ref; le'; re'], env_re)
    | P4cub.Expr.PlusSat => Some (Scall None (bop_function _interp_bplus_sat) [dst_ref; le'; re'], env_re)
    | P4cub.Expr.Minus => Some (Scall None (bop_function _interp_bminus) [dst_ref; le'; re'], env_re)
    | P4cub.Expr.MinusSat => Some (Scall None (bop_function _interp_bminus_sat) [dst_ref; le'; re'], env_re)
    | P4cub.Expr.Times => Some (Scall None (bop_function  _interp_bmult) [dst_ref; le'; re'], env_re)
    | P4cub.Expr.Shl => Some (Scall None (bop_function _interp_bshl) [dst_ref; le'; re'], env_re)
    | P4cub.Expr.Shr => Some (Scall None (bop_function _interp_bshr) [dst_ref; le'; re'], env_re)
    | P4cub.Expr.Le => Some (Scall None (bop_function  _interp_ble) [dst_ref; le'; re'], env_re)
    | P4cub.Expr.Ge => Some (Scall None (bop_function _interp_bge) [dst_ref; le'; re'], env_re)
    | P4cub.Expr.Lt => Some (Scall None (bop_function _interp_blt) [dst_ref; le'; re'], env_re)
    | P4cub.Expr.Gt => Some (Scall None (bop_function _interp_bgt) [dst_ref; le'; re'], env_re)

    | P4cub.Expr.Eq => 
      match Clight.typeof le' with
      | Tint IBool Signed noattr =>
        let eq_expr :=  Ebinop Oeq le' re' type_bool in
        Some (Sassign dst' eq_expr, env_re)
      | _ =>
        Some (Scall None (bop_function _interp_beq) [dst_ref; le'; re'], env_re)
      end
    
    | P4cub.Expr.NotEq => 
      match Clight.typeof le' with
      | Tint IBool Signed noattr =>
        let eq_expr :=  Ebinop Oeq le' re' type_bool in
        Some (Sassign dst' eq_expr, env_re)
      | _ =>  (*TODO: want a not eq here*)
        Some (Scall None (bop_function _interp_beq) [dst_ref; le'; re'], env_re)
      end
    
    | P4cub.Expr.BitAnd => Some (Scall None (bop_function _interp_bitwise_and) [dst_ref; le'; re'], env_re)
    | P4cub.Expr.BitXor => Some (Scall None (bop_function _interp_bitwise_xor) [dst_ref; le'; re'], env_re)
    | P4cub.Expr.BitOr => Some (Scall None (bop_function _interp_bitwise_or) [dst_ref; le'; re'], env_re)

    | P4cub.Expr.PlusPlus => 
    (*TODO: Need implementation in runtime*)
      Some (Scall None (bop_function _interp_bplus) [dst_ref; le'; re'], env_re)

    | P4cub.Expr.And => 
      let and_expr :=  Ebinop Oand le' re' type_bool in
      Some (Sassign dst' and_expr, env_re)
    
    | P4cub.Expr.Or => 
      let or_expr :=  Ebinop Oor le' re' type_bool in
      Some (Sassign dst' or_expr, env_re)
    end
    .
  

  Definition CTranslateFieldType (fields: F.fs string (P4cub.Expr.t* (E.e tags_t))) 
  := 
    F.map (fst) fields
  .
  Definition CTranslateListType (exps : list (E.e tags_t)):=
    List.map (E.cub_type_of tags_t) exps.

  Fixpoint CTranslateFieldAssgn (m : members) (exps : F.fs string (E.e tags_t)) (dst : Clight.expr) (env: ClightEnv tags_t):= 
    match m, exps with 
    |(id, typ) :: mtl, (fname, exp) :: etl => 
      let* (exp, env') := CTranslateExpr exp env in 
      let* (nextAssgn, env') := CTranslateFieldAssgn mtl etl dst env' in
      let curAssgn := 
          match typ with 
          | Tpointer t _  => Sassign (Ederef (Efield dst id typ) (t)) exp 
          | _ => Sassign (Efield dst id typ) exp
          end in 
      Some (Ssequence curAssgn nextAssgn , env')
    | [],[] => Some (Sskip,env)
    | _ , _ => None
    end.
  
  Fixpoint CTranslateListAssgn (m : members) (exps : list (E.e tags_t)) (dst : Clight.expr) (env: ClightEnv tags_t):= 
    match m, exps with 
    |(id, typ) :: mtl, exp :: etl => 
      let* (exp, env') := CTranslateExpr exp env in
      let* (nextAssgn, env') := CTranslateListAssgn mtl etl dst env' in 
      Some (Ssequence (Sassign (Efield dst id typ) exp) nextAssgn , env')
    | [],[] => Some (Sskip,env)
    | _ , _ => None
    end.

  Definition CTranslateTupleAssgn (exps: list (E.e tags_t)) (composite: composite_definition) (dst : Clight.expr) (env: ClightEnv tags_t):=
    match composite with 
      | Composite id su m a =>
        CTranslateListAssgn m exps dst env
    end.  

  Definition CTranslateStructAssgn (fields: F.fs string (P4cub.Expr.t * (E.e tags_t))) (composite: composite_definition) (dst : Clight.expr) (env: ClightEnv tags_t):=
    let exps := F.map (snd) fields in  
    match composite with 
      | Composite id su m a =>
        CTranslateFieldAssgn m exps dst env
    end.

  Definition CTranslateHeaderAssgn (fields: F.fs string (P4cub.Expr.t * (E.e tags_t))) (composite: composite_definition) (dst : Clight.expr) (env: ClightEnv tags_t) (valid: Clight.expr):=
    let exps := F.map (snd) fields in  
    match composite with 
      | Composite id su ((valid_id, valid_typ) :: mtl) a =>
        let assignValid := Sassign (Efield dst valid_id valid_typ) valid in
        let* (assigns, env') := CTranslateFieldAssgn mtl exps dst env in
        Some (Ssequence assignValid assigns , env')  
      |_ => None 
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

  Definition CTranslatePush (stack : AST.ident) (n : positive) (env: ClightEnv tags_t) : option (Clight.statement * ClightEnv tags_t):= 
    let env := add_temp tags_t env "i" int_signed in
    let* i := find_ident tags_t env "i" in
    let* stack_t := lookup_temp_type tags_t env stack in
    let stack_var := Evar stack (stack_t) in
    let* (next_var,ti,size_var,ts,arr_var,ta, val_typ, val_typ_valid_index) 
      := findStackAttributes stack_var stack_t env in
    Some (
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

  Definition CTranslatePop (stack : AST.ident) (n : positive) (env: ClightEnv tags_t) : option (Clight.statement * ClightEnv tags_t):= 
    let env := add_temp tags_t env "i" int_signed in
    let* i := find_ident tags_t env "i" in
    let* stack_t := lookup_temp_type tags_t env stack in
    let stack_var := Evar stack (stack_t) in
    let* (next_var,ti,size_var,ts,arr_var,ta, val_typ, val_typ_valid_index) :=
      findStackAttributes stack_var stack_t env in
    Some (
      (PopLoop n env arr_var size_var 
      next_var i val_typ val_typ_valid_index), 
      env) 
    .

  Fixpoint HeaderStackAssignLoop 
    (env: ClightEnv tags_t) 
    (arr_var: Clight.expr) 
    (i_var : Clight.expr) 
    (fields : F.fs string P4cub.Expr.t) 
    (headers: list (E.e tags_t))
    (header_typ : Ctypes.type)
    : option (Clight.statement * ClightEnv tags_t)
  := 
    let true := Econst_int Integers.Int.one type_bool in
    let int_one := Econst_int Integers.Int.one int_signed in
    match headers with
    | [] => Some (Sskip, env)
    | header :: tl => 
      let* (header,env) := CTranslateExpr header env in
      let assignHeader := Sassign (ArrayAccess arr_var i_var header_typ) header in
      let increment := Sassign (i_var) (Ebinop Oadd i_var int_one int_signed) in
      let* (assigntail, env') := HeaderStackAssignLoop env arr_var i_var fields tl header_typ in
      Some ((Ssequence assignHeader (Ssequence increment assigntail)), env')
    end.

  Fixpoint CTranslateStatement (s: ST.s tags_t) (env: ClightEnv tags_t ) : option (Clight.statement * ClightEnv tags_t ) :=
    match s with
    | ST.SSkip i => Some (Sskip, env)
    | ST.SSeq s1 s2 i => 
      let* (s1', env1) := CTranslateStatement s1 env in
      let* (s2', env2) := CTranslateStatement s2 env1 in
      Some (Ssequence s1' s2', env2)

    | ST.SBlock s => CTranslateStatement s env
    | ST.SVardecl t x i => 
      let (cty, env_cty):= CTranslateType t env in
      Some (Sskip, CCompEnv.add_var tags_t env_cty x cty)

    | ST.SConditional e s1 s2 i => 
      let* (e', env1) := CTranslateExpr e env in
      let* (s1', env2) := CTranslateStatement s1 env1 in
      let* (s2', env3) := CTranslateStatement s2 env2 in                 
      Some(Sifthenelse e' s1' s2', env3)

    | ST.SFunCall f _ (P4cub.Arrow args None) i
    | ST.SActCall f args i => 
      let* (f', id) := CCompEnv.lookup_function tags_t env f in
      let* (elist, env') := CTranslateDirExprList args env in 
      Some(Scall None (Evar id (Clight.type_of_function f')) elist, env')                              

    | ST.SFunCall f _ (P4cub.Arrow args (Some (t,e))) i =>
      let (ct, env_ct) := CTranslateType t env in
      let* (f', id) := CCompEnv.lookup_function tags_t env_ct f in
      let* (elist, env') := CTranslateDirExprList args env_ct in
      let (env', tempid) := CCompEnv.add_temp_nameless tags_t env' ct in
      let* (lvalue, env') := CTranslateExpr e env' in 
      Some(
        (Ssequence 
        (Scall (Some tempid) (Evar id (Clight.type_of_function f')) elist)
        (Sassign lvalue (Etempvar tempid ct) ))
        , env')
    
    | ST.SExternMethodCall e f _ (P4cub.Arrow args x) i => Some (Sskip, env) (*TODO: implement, need to be target specific.*)

    | ST.SReturnFruit t e i => 
      let* (e', env') := CTranslateExpr e env in
      Some ((Sreturn (Some e')), env')

    | ST.SReturnVoid i => Some (Sreturn None, env)
    | ST.SExit i => Some (Sskip, env) (*TODO: implement, what is this?*)
    | ST.SApply x ext args i => Some (Sskip, env) (*TODO: implement, ugh.*)
    | ST.SInvoke tbl i => Some (Sskip, env) (*TODO: implement*)
    | ST.SAssign t e1 e2 i => 
      match e1 with
      | E.EVar dst_t dst i => 
        match e2 with
        | E.EBit width val i => 
          let* dst' := find_ident tags_t env dst in
          let (env', val_id) := find_BitVec_String tags_t env val in 
          let w := Econst_int (Integers.Int.repr (Zpos width)) (int_signed) in
          let signed := Econst_int (Integers.Int.zero) (type_bool) in 
          let val' := Evar val_id Cstring in
          let dst' := Eaddrof (Evar dst' bit_vec) TpointerBitVec in
          Some (Scall None bitvec_init_function [dst'; signed; w; val'], env')
        
        | E.EInt width val i => 
          let* dst' := find_ident tags_t env dst in
          let (env', val_id) := find_BitVec_String tags_t env val in 
          let w := Econst_int (Integers.Int.repr (Zpos width)) (int_signed) in
          let signed := Econst_int (Integers.Int.one) (type_bool) in 
          let val' := Evar val_id Cstring in
          let dst' := Eaddrof (Evar dst' bit_vec) TpointerBitVec in
          Some (Scall None bitvec_init_function [dst'; signed; w; val'], env')

        | E.ESlice n τ hi lo i => 
          let* (n', env') := CTranslateExpr n env in
          let hi' := Econst_int (Integers.Int.repr (Zpos hi)) (int_unsigned) in
          let lo' := Econst_int (Integers.Int.repr (Zpos lo)) (int_unsigned) in
          let* dst' := find_ident tags_t env dst in
          let (tau', env') := CTranslateType τ env' in 
          let dst' := Evar dst' tau' in
          Some (Scall None slice_function [n'; hi'; lo'; dst'], env')

        | E.ECast τ e i => None (*TODO: implement in the runtime*)
        
        | E.EUop op dst_t x i => CTranslateUop dst_t op x dst env

        | E.EBop op dst_t rhs_type x y i => CTranslateBop dst_t op x y dst env
                        
        | E.ETuple es i =>  (*first create a temp of this tuple. then assign all the values to it. then return this temp  *) 
          let tuple := P4cub.Expr.TTuple (CTranslateListType es) in
          let (typ, env) := CTranslateType tuple env in
          let* composite := lookup_composite tags_t env tuple in
          let* dst := find_ident tags_t env dst in
          CTranslateTupleAssgn es composite (Evar dst typ) env

        | E.EStruct fields i => (*first create a temp of this struct. then assign all the values to it. then return this temp *)
          let struct := P4cub.Expr.TStruct (CTranslateFieldType fields) in
          let (typ, env) := CTranslateType struct env in
          let* composite := lookup_composite tags_t env struct in
          let* dst := find_ident tags_t env dst in
          CTranslateStructAssgn fields composite (Evar dst typ) env

        | E.EHeader fields b i => (*first create a temp of this header. then assign all the values to it. then return this temp*)
          let hdr := P4cub.Expr.THeader (CTranslateFieldType fields) in
          let (typ, env) := CTranslateType hdr env in
          let* (valid, env) := CTranslateExpr b env in
          let* composite := lookup_composite tags_t env hdr in
          let* dst := find_ident tags_t env dst in
          CTranslateHeaderAssgn fields composite (Evar dst typ) env valid

        | E.EHeaderStack fields headers size next_index i =>
          let top_typ := P4cub.Expr.THeaderStack fields size in
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
          Some (Sassign e1' e2', env2)
        end
      | _ =>
      let* (e1', env1) := CTranslateExpr e1 env in
      let* (e2', env2) := CTranslateExpr e2 env1 in
      Some (Sassign e1' e2', env2)
      end

    | ST.SHeaderStackOp stack P4cub.Stmt.HSPush n i =>
      let* stack_id := 
        match find_ident_temp_arg tags_t env stack with
        | Some (_, x) => Some x
        | None => find_ident tags_t env stack 
        end
      in
      CTranslatePush stack_id n env

    | ST.SHeaderStackOp stack P4cub.Stmt.HSPop n i => 
      let* stack_id := 
        match find_ident_temp_arg tags_t env stack with
        | Some (_, x) => Some x
        | None => find_ident tags_t env stack 
        end
      in 
      CTranslatePop stack_id n env
    
    (*  *)

    | ST.SSetValidity arg val i =>
      let* (arg', env) := CTranslateExpr arg env in 
      let* index := ValidBitIndex arg env in
      let member :=  Efield arg' index type_bool in
      let val := 
        match val with
        | P4cub.Stmt.Valid => Econst_int Integers.Int.one type_bool
        | P4cub.Stmt.Invalid => Econst_int Integers.Int.zero type_bool
        end in
      let assign := Sassign member val in
      Some(assign , env)  

    end.


  Definition CTranslateParams (params : E.params) (env : ClightEnv tags_t ) 
    : list (AST.ident * Ctypes.type) * ClightEnv tags_t  
  :=
    List.fold_left 
      (fun (cumulator: (list (AST.ident * Ctypes.type))*ClightEnv tags_t ) (p: string * P.paramarg E.t E.t)
      =>let (l, env') := cumulator in
        let (env', new_id) := new_ident tags_t env' in
        let (ct,env_ct) := match p with 
          | (_, P.PAIn x) 
          | (_, P.PADirLess x)
          | (_, P.PAOut x)
          | (_, P.PAInOut x) => (CTranslateType x env')
        end in
        let ct_param := match p with 
        | (_, P.PADirLess _)
        | (_, P.PAIn _) => ct
        | (_, P.PAOut x)
        | (_, P.PAInOut x) => Ctypes.Tpointer ct noattr
        end in
        let s := fst p in
        let env_temp_added := add_temp_arg tags_t env_ct s ct new_id in  (*the temps here are for copy in copy out purpose*)
        (l ++ [(new_id, ct_param)], env_temp_added)) 
    (params) ([],env) . 

  Definition CTranslateConstructorParams (cparams : P4cub.Expr.constructor_params) (env : ClightEnv tags_t)
    : list (AST.ident * Ctypes.type) * ClightEnv tags_t 
  := 
    List.fold_left 
      (fun (cumulator: (list (AST.ident * Ctypes.type)) * ClightEnv tags_t ) (p: string * P4cub.Expr.ct)
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
  
  Definition CCopyIn (fn_params: E.params) (env: ClightEnv tags_t )
    : option (Clight.statement * ClightEnv tags_t)
  := 
    List.fold_left 
      (fun (cumulator: option (Clight.statement * ClightEnv tags_t)) (fn_param: string * (P.paramarg E.t E.t))
      =>let (name, t) := fn_param in 
        let* (prev_stmt, prev_env) := cumulator in
        let* (oldid, tempid) := find_ident_temp_arg tags_t env name in
        match t with
          | P.PAIn t
          | P.PADirLess t => 
            let (ct, env_ct) := CTranslateType t prev_env in
            let new_stmt := Sassign (Evar tempid ct) (Evar oldid ct) in
            Some (Ssequence prev_stmt new_stmt, env_ct)
          | P.PAOut t
          | P.PAInOut t => 
            let (ct, env_ct) := CTranslateType t prev_env in
            let new_stmt := Sassign (Evar tempid ct) (Ederef (Evar oldid (Ctypes.Tpointer ct noattr)) ct) in
            Some (Ssequence prev_stmt new_stmt, env_ct)
        end
      ) fn_params (Some(Sskip, env)).

  Definition CCopyOut (fn_params: E.params) (env: ClightEnv tags_t )
    : option (Clight.statement * ClightEnv tags_t) 
  := 
    List.fold_left 
      (fun (cumulator: option (Clight.statement * ClightEnv tags_t)) (fn_param: string * (P.paramarg E.t E.t))
      =>let (name, t) := fn_param in 
        let* (prev_stmt, prev_env) := cumulator in
        let* (oldid, tempid) := find_ident_temp_arg tags_t env name in 
        match t with
        | P.PADirLess t
        | P.PAIn t => 
          let (ct, env_ct) := CTranslateType t prev_env in
          let new_stmt := Sassign (Evar oldid ct) (Evar tempid ct) in
          Some (Ssequence prev_stmt new_stmt, env_ct)
        | P.PAOut t
        | P.PAInOut t => 
          let (ct, env_ct) := CTranslateType t prev_env in
          let new_stmt := Sassign (Ederef (Evar oldid (Ctypes.Tpointer ct noattr)) ct) (Evar tempid ct) in
          Some (Ssequence prev_stmt new_stmt, env_ct)
        end
      ) fn_params (Some (Sskip, env)).

  (*return the list of args for the params*)
  Definition CFindTempArgs (fn_params: E.params) (env: ClightEnv tags_t )
    : option (list Clight.expr) 
  := 
    List.fold_left 
      (fun (cumulator: option (list Clight.expr)) (fn_param: string * (P.paramarg E.t E.t))
        =>let (name, t) := fn_param in
          let* (oldid, tempid) := find_ident_temp_arg tags_t env name in
          let* cumulator := cumulator in
          match t with 
          | P.PADirLess t
          | P.PAIn t
          | P.PAOut t
          | P.PAInOut t =>
            let (ct, _) := CTranslateType t env in
            Some (cumulator ++ [Evar tempid ct])
          end
      ) fn_params (Some []).

  (*return the list of args for the params but adding directions.
  change the temp to ref temp if it is a out parameter.
  *)
  Definition CFindTempArgsForCallingSubFunctions (fn_params: E.params) (env: ClightEnv tags_t )
    : option (list Clight.expr) 
  := 
    List.fold_left 
      (fun (cumulator: option (list Clight.expr)) (fn_param: string * (P.paramarg E.t E.t))
      =>let (name, t) := fn_param in
        let* (oldid, tempid) := find_ident_temp_arg tags_t env name in
        let* cumulator := cumulator in 
        let (ct, _) := 
          match t with 
          | P.PADirLess t
          | P.PAIn t
          | P.PAOut t
          | P.PAInOut t => CTranslateType t env 
          end in 
        let var := 
          match t with
          | P.PADirLess t
          | P.PAIn t => Evar tempid ct
          | P.PAOut t
          | P.PAInOut t => Eaddrof (Evar tempid ct) (Tpointer ct noattr)
          end in
        Some (cumulator ++ [var])
      ) fn_params (Some []).


  Definition CTranslateArrow (signature : E.arrowT) (env : ClightEnv tags_t )
    : (list (AST.ident * Ctypes.type)) * Ctypes.type * ClightEnv tags_t  
  := 
    let  '(P.Arrow pas ret) := signature in
    let (fn_params, env_params_created) := CTranslateParams pas env in 
    match ret with 
    | None => (fn_params, Ctypes.Tvoid, env_params_created)
    | Some return_t => 
      let (ct, env_ct):= CTranslateType return_t env_params_created in 
      (fn_params, ct , env_ct)
    end.
      
  Definition PaFromArrow (arrow: E.arrowT) : (E.params):=
    let '(P.Arrow pas ret) := arrow in
    pas.

  Definition CTranslatePatternVal (p : P4cub.Parser.pat) (env: ClightEnv tags_t)
    : option (Clight.statement * ident * ClightEnv tags_t) := 
    match p with 
    | P4cub.Parser.PATBit width val =>
        let (env, fresh_id) := new_ident tags_t env in 
        let fresh_name := String.append "_p_e_t_r_4_" (BinaryString.of_pos fresh_id) in
        let env := add_var tags_t env fresh_name bit_vec in 
        let* dst := find_ident tags_t env fresh_name in
        let (env', val_id) := find_BitVec_String tags_t env val in 
        let w := Econst_int (Integers.Int.repr (Zpos width)) (int_signed) in
        let signed := Econst_int (Integers.Int.zero) (type_bool) in 
        let val' := Evar val_id Cstring in
        let dst' := Eaddrof (Evar dst bit_vec) TpointerBitVec in
        Some ((Scall None bitvec_init_function [dst'; signed; w; val']), dst, env')
        
    | P4cub.Parser.PATInt width val => 
        let (env, fresh_id) := new_ident tags_t env in 
        let fresh_name := String.append "_p_e_t_r_4_" (BinaryString.of_pos fresh_id) in
        let env := add_var tags_t env fresh_name bit_vec in 
        let* dst := find_ident tags_t env fresh_name in
        let (env', val_id) := find_BitVec_String tags_t env val in 
        let w := Econst_int (Integers.Int.repr (Zpos width)) (int_signed) in
        let signed := Econst_int (Integers.Int.one) (type_bool) in 
        let val' := Evar val_id Cstring in
        let dst' := Eaddrof (Evar dst bit_vec) TpointerBitVec in
        Some ((Scall None bitvec_init_function [dst'; signed; w; val']), dst, env')

    | _ => None
    end.

  Definition CTranslatePatternMatch (input: Clight.expr) (p: P4cub.Parser.pat) (env: ClightEnv tags_t): option (Clight.statement * ident * ClightEnv tags_t) :=
    let (env, fresh_id) := new_ident tags_t env in 
    let fresh_name := String.append "_p_e_t_r_4_" (BinaryString.of_pos fresh_id) in
    let env := add_var tags_t env fresh_name type_bool in 
    let* dst := find_ident tags_t env fresh_name in
    let dst' := Eaddrof (Evar dst type_bool) TpointerBool in
    match p with
    | P4cub.Parser.PATWild => 
      let assign := Sassign dst' (Econst_int (Integers.Int.one) (type_bool)) in 
      Some (assign, dst, env)
      
    | P4cub.Parser.PATMask  p1 p2 => 
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
      Some (stmts, dst, env)

    | P4cub.Parser.PATRange p1 p2 => 
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
      Some (stmts, dst, env)

    | P4cub.Parser.PATInt width val
    | P4cub.Parser.PATBit width val => 
      let*  (init, var, env) := CTranslatePatternVal p env in
      let assign := 
        Scall None (bop_function _interp_beq) [dst'; input; (Evar var bit_vec)] in
      let stmts := Ssequence init assign in
      Some (stmts, dst, env)

    | P4cub.Parser.PATTuple ps => 
      None
    end.


  Definition CTranslateParserExpressionVal
    (pe: PA.e tags_t) 
    (env: ClightEnv tags_t)
    (rec_call_args : list (Clight.expr))
    : option (Clight.statement * ClightEnv tags_t) :=
    match pe with 
    | PA.PGoto st i => 
      match st with
      | P4cub.Parser.STStart =>
        let* (start_f, start_id) := (lookup_function tags_t env "start") in
        Some (Scall None (Evar start_id (Clight.type_of_function start_f)) rec_call_args, env)

      | P4cub.Parser.STAccept =>
        Some ( Sreturn None, env)
         
      | P4cub.Parser.STReject => None (*TODO: implement*)
      
      | P4cub.Parser.STName x => 
        let*  (x_f, x_id) := lookup_function tags_t env x in
        Some (Scall None (Evar x_id (Clight.type_of_function x_f)) rec_call_args, env)
      end

    | PA.PSelect exp def cases i => 
      None
    end.
    

  Definition CTranslateParserExpression 
    (pe: PA.e tags_t) 
    (env: ClightEnv tags_t)
    (rec_call_args : list (Clight.expr))
    : option (Clight.statement * ClightEnv tags_t) :=
    match pe with 
    | PA.PSelect exp def cases i => 
      let* (input, env) := CTranslateExpr exp env in
      let* (default_stmt, env) := CTranslateParserExpressionVal def env rec_call_args in
      let fold_function 
          (elt: P4cub.Parser.pat * PA.e tags_t) 
          (cumulator: option (Clight.statement * ClightEnv tags_t)) :=
          let '(p, action) := elt in
          let* (fail_stmt, env') := cumulator in
          let* (match_statement, this_match, env') := CTranslatePatternMatch input p env' in
          let* (success_statement, env') := CTranslateParserExpressionVal action env' rec_call_args in 
          let new_stmt := Ssequence match_statement (Sifthenelse (Evar this_match type_bool) success_statement fail_stmt) in
          Some (new_stmt, env')
      in
      List.fold_right fold_function (Some (default_stmt, env)) cases
    
    | _ => CTranslateParserExpressionVal pe env rec_call_args
    end.

  Definition CTranslateParserState (st : PA.state_block tags_t) (env: ClightEnv tags_t ) (params: list (AST.ident * Ctypes.type)): option (Clight.function * ClightEnv tags_t ) :=
    let '(PA.State stmt pe) := st in
    let rec_call_args := List.map (fun (x: AST.ident * Ctypes.type) => Etempvar (fst x) (snd x)) params in
    let* (stmt', env') := CTranslateStatement stmt env in
    let* (estmt, env') := CTranslateParserExpression pe env' rec_call_args in
    Some (Clight.mkfunction
          Ctypes.Tvoid
          (AST.mkcallconv None true true)
          params
          (CCompEnv.get_vars tags_t env')
          (CCompEnv.get_temps tags_t env')
          (Ssequence stmt' estmt)
          , (set_temp_vars tags_t env env')).

  Definition CTranslateTopParser (parsr: TD.d tags_t) (env: ClightEnv tags_t ): option (ClightEnv tags_t )
  :=
    match parsr with
    | TD.TPParser p cparams eps params st states i =>
      let (fn_cparams, env_cparams) := CTranslateConstructorParams cparams env in
      let (fn_eparams, env_eparams) := CTranslateExternParams eps env_cparams in 
      let (fn_params, env_params):= CTranslateParams params env_eparams in 
      let* (copyin, env_copyin) := CCopyIn params env_params in 
      let* (copyout, env_copyout) := CCopyOut params env_copyin in (*copy in and copy out may need to copy cparams and eparams as well*)
      let state_names := F.keys states in 
      let fn_params := fn_cparams ++ fn_eparams ++ fn_params in 
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
        (fun (cumulator: option (ClightEnv tags_t )) (state_name: string) => 
          let* env' := cumulator in
          let* sb := Env.find state_name states in  
          let* (f, env_f_translated) := CTranslateParserState sb env' fn_params in
          Some(CCompEnv.update_function tags_t env_f_translated state_name f)
        ) state_names (Some (set_temp_vars tags_t env env_fn_sig_declared)) in
      (*finished declaring all the state blocks except start state*)
      let* (f_start, env_start_translated) := CTranslateParserState st (set_temp_vars tags_t env env_fn_declared) fn_params in
      let env_start_declared := CCompEnv.update_function tags_t env_start_translated "start" f_start in
      let env_start_declared := set_temp_vars tags_t env_copyout env_start_declared in
      let* (start_f, start_id) := (lookup_function tags_t env_start_declared "start") in
      let* call_args := CFindTempArgsForCallingSubFunctions params env_start_declared in
      let e_call_args := List.map (fun (x: AST.ident * Ctypes.type) => Etempvar (fst x) (snd x)) fn_eparams in
      let call_args := e_call_args ++ call_args in
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
  let* (copyin, env_copyin) := CCopyIn full_signature env_params_created in
  let* (copyout, env_copyout) := CCopyOut full_signature env_copyin in
  let* (c_body, env_body_translated) := CTranslateStatement body env_copyout in
  let body:= Ssequence copyin (Ssequence c_body copyout) in
  Some(
    (Clight.mkfunction 
      Ctypes.Tvoid
      (AST.mkcallconv None true true)
      fn_params 
      (get_vars tags_t env_body_translated)
      (get_temps tags_t env_body_translated)
      body), (set_temp_vars tags_t env env_body_translated))
  .

  Fixpoint CTranslateControlLocalDeclaration 
  (ct : CT.d tags_t) (env: ClightEnv tags_t ) 
  (top_fn_params: list (AST.ident * Ctypes.type))
  (top_signature: E.params)
  : option (ClightEnv tags_t )
  := match ct with
  | CT.CDSeq d1 d2 i=> 
    let* env1 := (CTranslateControlLocalDeclaration d1 env top_fn_params top_signature) in
    CTranslateControlLocalDeclaration d2 env1 top_fn_params top_signature
    
  | CT.CDAction a params body i => 
    let* (f, env_action_translated) := CTranslateAction params body env top_fn_params top_signature in
    Some (CCompEnv.add_function tags_t env_action_translated a f)

  | CT.CDTable t (CT.Table ems acts) i => Some env (*TODO: implement table*)
  end.
  
  Definition CTranslateTopControl (ctrl: TD.d tags_t) (env: ClightEnv tags_t ): option (ClightEnv tags_t )
  := 
    match ctrl with
    | TD.TPControl c cparams eps params body blk i => 
      let (fn_cparams, env_top_fn_cparam) := CTranslateConstructorParams cparams env in
      let (fn_eparams, env_top_fn_eparam) := CTranslateExternParams eps env_top_fn_cparam in
      let (fn_params, env_top_fn_param) := CTranslateParams params env_top_fn_eparam in
      let* (copyin, env_copyin) := CCopyIn params env_top_fn_param in 
      let* (copyout, env_copyout) := CCopyOut params env_copyin in 
      let fn_params := fn_cparams ++ fn_eparams ++ fn_params in 
      let* env_local_decled := CTranslateControlLocalDeclaration body env_copyout fn_params params in
      let* (apply_blk, env_apply_block_translated) := CTranslateStatement blk env_local_decled in
      let body:= Ssequence copyin (Ssequence apply_blk copyout) in
      let top_fn := 
        Clight.mkfunction 
          Ctypes.Tvoid 
          (AST.mkcallconv None true true)
          fn_params 
          (get_vars tags_t env_apply_block_translated)
          (get_temps tags_t env_apply_block_translated)
          body in
      let env_top_fn_declared := 
        CCompEnv.add_function tags_t env_local_decled c top_fn in
      Some (set_temp_vars tags_t env env_top_fn_declared) 

    | _ => None
    end.


  
  Definition CTranslateFunction (funcdecl : TD.d tags_t) (env: ClightEnv tags_t )
    : option (ClightEnv tags_t )
  := 
    match funcdecl with
    | TD.TPFunction name _ signature body _ => 
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
      Some (set_temp_vars tags_t env (CCompEnv.add_function tags_t env_params_created name top_function))

    | _ => None
    end.


  Fixpoint CTranslateTopDeclaration (d: TD.d tags_t) (env: ClightEnv tags_t ) : option (ClightEnv tags_t )
  := 
  match d with
  | TD.TPSeq d1 d2 i => 
    let* env1 := CTranslateTopDeclaration d1 env in
    CTranslateTopDeclaration d2 env1 

  | TD.TPInstantiate c x _ args i => 
    (* let* (init', env') := CTranslateStatement args_init env in *)
    (* Some (set_main_init tags_t (set_instantiate_cargs tags_t env args) Sskip) *)
    (*TODO: Translate each instantiate into a function*)
    (*TODO: Maybe we also want an abstract interpretation in the statementize pass?*)
    None
  | TD.TPFunction _ _ _ _ _ => CTranslateFunction d env
  | TD.TPExtern e _ cparams methods i => None (*TODO: implement*)
  | TD.TPControl _ _ _ _ _ _ _ => CTranslateTopControl d env
  | TD.TPParser _ _ _ _ _ _ _ => CTranslateTopParser d env
  | TD.TPPackage _ _ _ _ => None (*TODO: implement*)
  end.

  Definition Compile (prog: TD.d tags_t) : Errors.res (Clight.program) := 
    let init_env := CCompEnv.newClightEnv tags_t in
    let main_id := $"main" in 
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

  Definition Compile_print (prog: TD.d tags_t): unit := 
    match Compile prog with
    | Errors.Error e => tt
    | Errors.OK prog => print_Clight prog
    end.  
End CCompSel.

Definition helloworld_program_sel := Statementize.TranslateProgram nat helloworld_program.
Definition test := 
  match helloworld_program_sel with 
  | inl helloworld_program_sel => CCompSel.Compile_print nat helloworld_program_sel
  | inr _ => tt
  end.
