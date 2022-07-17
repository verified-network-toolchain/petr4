From compcert Require Import AST Clight Ctypes Integers Cop Clightdefs.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
Require Import BinaryString
        Coq.PArith.BinPosDef Coq.PArith.BinPos
        List Coq.ZArith.BinIntDef String.
Require Coq.PArith.BinPosDef.
Require Import
        Poulet4.P4cub.Syntax.Syntax Poulet4.Utils.Envn.
From Poulet4 Require Import
     P4cub.Transformations.Lifting.Statementize
     Monads.Monad Monads.Option Monads.Error Monads.State Monads.Result
     Ccomp.CCompEnv (*Ccomp.Helloworld Ccomp.CV1Model*) Ccomp.Cconsts.
Import Clightdefs.ClightNotations.
Require Import Poulet4.Ccomp.Petr4Runtime.
Module RunTime := Petr4Runtime.
(** P4Sel -> Clight **)
Section CCompSel.
  Local Open Scope string_scope.
  Local Open Scope list_scope.
  Local Open Scope Z_scope.
  Local Open Scope N_scope.
  Local Open Scope clight_scope.
  Local Open Scope positive_scope.
  Local Open Scope monad_scope.
  
  Parameter print_Clight: Clight.program -> unit.
  
  Fixpoint
    CTranslateType
    (p4t : Expr.t) : State ClightEnv Ctypes.type :=
    match p4t with
    | Expr.TBool => mret Ctypes.type_bool
    | Expr.TBit _
    | Expr.TInt _ => mret bit_vec
    | Expr.TVar _ => mret tvoid
    | Expr.TError => mret int_unsigned
    | Expr.TStruct fields is_header =>
        let* env := get_state in
        match lookup_composite env p4t with
        | Result.Ok _ comp =>
            (* found identifier *)
            mret (Ctypes.Tstruct (Ctypes.name_composite_def comp) noattr)
        | _ =>
            (* need to generate identifiers *)
            let* top_id := CCompEnv.new_ident in
            let* env_top_id := get_state in
            let* init :=
              if is_header then
                let* valid_id := new_ident in
                mret [Member_plain valid_id type_bool]
              else mret [] in
            (* translate fields *)
            let* members :=
              state_list_map
                (fun (t : Expr.t) =>
                   let* new_t := CTranslateType t in
                   let new_t :=
                     match new_t with
                     | Tstruct st noattr =>
                         if (st =? RunTime._BitVec) then
                           Tpointer new_t noattr else new_t
                     | _ => new_t
                     end in
                   let^ new_id := CCompEnv.new_ident in
                   Member_plain new_id new_t)
                fields in
            let comp_def :=
              Ctypes.Composite
                top_id
                Ctypes.Struct
                (init ++ members)
                Ctypes.noattr in
            let* env_fields_declared := get_state in
            let env_comp_added :=
              CCompEnv.add_composite_typ  env_fields_declared p4t comp_def in
            put_state env_comp_added ;;
            mret (Ctypes.Tstruct top_id noattr)
        end
    end.

  (* Definition CTranslateConstructorType (ct: Expr.ct) (env: ClightEnv ) : Ctypes.type * ClightEnv  :=
  match ct with 
  | Expr.CTType type => CTranslateType type env
  | Expr.CTControl cparams _ parameters => (Ctypes.Tvoid, env) (*implement*)
  | Expr.CTParser cparams  _ parameters => (Ctypes.Tvoid, env) (*implement*)
  | Expr.CTPackage cparams => (Ctypes.Tvoid, env) (*implement*)

  | Expr.CTExtern extern_name => 
    match extern_name with
    | "packet_in" => (packet_in,env)
    | "packet_out" => (packet_out, env)
    | _ => (Ctypes.Tvoid, env) (*implement*) 
    end
  end. *)
  
  Fixpoint CTranslateExpr (e: Expr.e)
    : StateT ClightEnv Result.result Clight.expr :=
    match e with
    | Expr.Bool true  => mret Ctrue
    | Expr.Bool false => mret Cfalse
    | Expr.Var ty x =>
        (*first find if x has been declared. If not, declare it *)
        let* cty := State_lift (CTranslateType ty) in
        let* env_ty := get_state in
        match find_ident_temp_arg env_ty x with 
        (*first look for if this is an argument and has its own temp for copy in/out *)
        | Result.Ok _ (_,tempid) => mret (Etempvar tempid cty)
        | _ => match nth_error env_ty.(varMap) x with
              | Some id => mret (Evar id cty)
              | _ =>
                  let env' := add_var env_ty cty in
                  put_state env' ;;
                  let^ id' := state_lift (find_var env' x) in
                  Evar id' cty
              end
        end
    | Expr.Member ty y x =>
        let* cty := State_lift (CTranslateType ty) in
        let* x' := CTranslateExpr x in
        let* env' := get_state in
        match t_of_e x with
        | Expr.TStruct f is_header =>
            match nth_error f y, lookup_composite env' (t_of_e x) with 
            | Some t_member, Result.Ok _ comp =>
                let* ctm := State_lift (CTranslateType t_member) in
                let* index :=
                  state_lift (composite_nth
                                comp
                                ((if is_header then 1 else 0) + y)) in
                let em :=
                  match ctm with
                  | Tstruct st _ =>
                      if st =? RunTime._BitVec
                      then Ederef (Clight.Efield x' index (Tpointer ctm noattr)) ctm
                      else (Clight.Efield x' index ctm)
                  | _ => Clight.Efield x' index ctm
                  end in mret em
            | _, _ => state_lift (Result.error "member is not in struct")
            end
        | _ => state_lift (Result.error "member of an invalid type")
        end
    | Expr.Error x => mret Ctrue(*TODO: implement*)
    | _ => state_lift (Result.error "illegal expression, statementized failed" (*Not Allowed*))
    end.

  Definition CTranslateExprList
    : list Expr.e -> StateT ClightEnv Result.result (list Clight.expr) :=
    state_list_map CTranslateExpr.
  
  Definition CTranslateArgs
    : Expr.args -> StateT ClightEnv Result.result (list Clight.expr) :=
    state_list_map
      (fun (arg : paramarg Expr.e Expr.e) =>
         match arg with
         | PAIn e => CTranslateExpr e
         | PAOut e
         | PAInOut e =>
             let* ct := State_lift (CTranslateType (t_of_e e)) in
             let^ ce := CTranslateExpr e in
             Eaddrof ce (Tpointer ct noattr)
         end).
  
  Definition ValidBitIndex (arg: Expr.e) (env: ClightEnv)
    : Result.result AST.ident :=
    let* comp:= lookup_composite env (t_of_e arg) in
    match comp with
    | Ctypes.Composite _ Ctypes.Struct m _ =>
        match m with
        | [] => Result.error "struct is empty"
        | Member_plain id t :: _ => mret id
        | Member_bitfield _ _ _ _ _ _ :: _ => Result.error "TODO"
        end
    | _ => Result.error "composite looked up is not a composite"
    end.

  Definition statement_of_list
    : list Clight.statement -> Clight.statement :=
    List.fold_right Ssequence Sskip.
  
  (* TODO: set validity ops compilation needs to be here. *)
  Definition
    CTranslateUop 
    (dst_t: Expr.t) (op: Expr.uop) (arg: Expr.e) (dst: nat)
    : StateT ClightEnv Result.result Clight.statement :=
    let* dst_t' := State_lift (CTranslateType dst_t) in
    let* env := get_state in
    let* dst' := state_lift (find_var env dst) in 
    let dst' := Evar dst' dst_t' in
    let* arg' := CTranslateExpr arg in
    let arg_ref := Eaddrof arg' (Tpointer (Clight.typeof arg') noattr) in
    let dst_ref := Eaddrof dst' (Tpointer dst_t' noattr) in  
    match op with
    | Expr.Not => 
        let not_expr := Eunop Onotbool arg' Ctypes.type_bool in 
        mret (Sassign dst' not_expr)
    | Expr.BitNot => 
        (*need implementation in runtime*)
        mret (Scall None (uop_function _interp_bitwise_and) [arg_ref; dst_ref])
    | Expr.UMinus => 
        mret (Scall None (uop_function _eval_uminus)  [arg_ref; dst_ref])
    | Expr.IsValid =>
        let* env := get_state in
        let^ index := state_lift (ValidBitIndex arg env) in
        Sassign dst' (Efield arg' index type_bool)
    | _ => state_lift (Result.error "Unsupported uop")
    end.
 
  Definition bop_function (op: ident) := 
    if(op =? _interp_beq) then
      Evar op (Tfunction typelist_bop_bool tvoid cc_default) 
    else if(op =? _interp_bne) then
      Evar op (Tfunction typelist_bop_bool tvoid cc_default) 
    else if(op =? _interp_bge) then
      Evar op (Tfunction typelist_bop_bool tvoid cc_default) 
    else if(op =? _interp_bgt) then
      Evar op (Tfunction typelist_bop_bool tvoid cc_default) 
    else if(op =? _interp_ble) then
      Evar op (Tfunction typelist_bop_bool tvoid cc_default) 
    else if(op =? _interp_blt) then
      Evar op (Tfunction typelist_bop_bool tvoid cc_default) 
    else
      Evar op (Tfunction typelist_bop_bitvec tvoid cc_default).
  
  Definition
    CTranslateBop  (dst_t: Expr.t) (op: Expr.bop)
    (le: Expr.e) (re: Expr.e) (dst: nat)
    : StateT ClightEnv Result.result Clight.statement :=
    let* env := get_state in
    let* dst' := state_lift (find_var env dst) in
    let* dst_t' := State_lift (CTranslateType dst_t) in
    let dst' := Evar dst' dst_t' in
    let* le' := CTranslateExpr le in
    let^ re' := CTranslateExpr re in
    let le_ref := Eaddrof le' (Tpointer (Clight.typeof le') noattr) in
    let re_ref := Eaddrof re' (Tpointer (Clight.typeof re') noattr) in
    let dst_ref := Eaddrof dst' (Tpointer dst_t' noattr) in  
    let signed :=
      match dst_t with
      | Expr.TInt _ => true
      | _ => false
      end in
    match op with
    | Expr.Plus => Scall None (bop_function _interp_bplus) [dst_ref; le'; re']
    | Expr.PlusSat => Scall None (bop_function _interp_bplus_sat) [dst_ref; le'; re']
    | Expr.Minus => Scall None (bop_function _interp_bminus) [dst_ref; le'; re']
    | Expr.MinusSat => Scall None (bop_function _interp_bminus_sat) [dst_ref; le'; re']
    | Expr.Times => Scall None (bop_function  _interp_bmult) [dst_ref; le'; re']
    | Expr.Shl => Scall None (bop_function _interp_bshl) [dst_ref; le'; re']
    | Expr.Shr => Scall None (bop_function _interp_bshr) [dst_ref; le'; re']
    | Expr.Le => Scall None (bop_function  _interp_ble) [dst_ref; le'; re']
    | Expr.Ge => Scall None (bop_function _interp_bge) [dst_ref; le'; re']
    | Expr.Lt => Scall None (bop_function _interp_blt) [dst_ref; le'; re']
    | Expr.Gt => Scall None (bop_function _interp_bgt) [dst_ref; le'; re']
    | Expr.Eq => 
      match Clight.typeof le' with
      | Tint IBool Signed noattr => Sassign dst' (Ebinop Oeq le' re' type_bool)
      | _ => Scall None (bop_function _interp_beq) [dst_ref; le'; re']
      end
    | Expr.NotEq => 
      match Clight.typeof le' with
      | Tint IBool Signed noattr => Sassign dst' (Ebinop Oeq le' re' type_bool)
      | _ => Scall None (bop_function _interp_bne) [dst_ref; le'; re']
      end
    | Expr.BitAnd => Scall None (bop_function _interp_bitwise_and) [dst_ref; le'; re']
    | Expr.BitXor => Scall None (bop_function _interp_bitwise_xor) [dst_ref; le'; re']
    | Expr.BitOr => Scall None (bop_function _interp_bitwise_or) [dst_ref; le'; re']
    | Expr.PlusPlus => Scall None (bop_function _interp_concat) [dst_ref; le'; re']
    | Expr.And => Sassign dst' (Ebinop Oand le' re' type_bool)
    | Expr.Or => Sassign dst' (Ebinop Oor le' re' type_bool)
    end.

  Fixpoint CTranslateFieldAssgn
           (m : members) (exps : list Expr.e)
           (dst : Clight.expr) : StateT ClightEnv Result.result Clight.statement :=
    match m, exps with
    | Member_plain id typ :: mtl, exp :: etl => 
        let* exp := CTranslateExpr exp in 
        let^ nextAssgn := CTranslateFieldAssgn mtl etl dst in
        let curAssgn :=
          match typ with 
          | Tpointer t _  => Sassign (Ederef (Efield dst id typ) t) exp 
          | _ => Sassign (Efield dst id typ) exp
          end in
        Ssequence curAssgn nextAssgn
    | [],[] => mret Sskip
    | _ , _ => state_lift (Result.error "field different length")
    end.
  
  Definition
    CTranslateStructAssgn (fields: list Expr.e)
    (composite: composite_definition) (dst : Clight.expr)
    : StateT ClightEnv Result.result Clight.statement :=
    match composite with 
    | Composite id su m a =>
        CTranslateFieldAssgn m fields dst
    end.

  Definition
    CTranslateHeaderAssgn (exps: list Expr.e)
    (composite: composite_definition)
    (dst : Clight.expr) (valid: Clight.expr)
    : StateT ClightEnv Result.result Clight.statement :=
    match composite with 
    | Composite id su (Member_plain valid_id valid_typ :: mtl) a =>
        let assignValid := Sassign (Efield dst valid_id valid_typ) valid in
        let^ assigns := CTranslateFieldAssgn mtl exps dst in
        Ssequence assignValid assigns
    |_ => state_lift (Result.error "Not a composite")
    end.

  Definition
    ArrayAccess (arr : Clight.expr)
    (index : Clight.expr) (result_t: Ctypes.type) : Clight.expr := 
    Ederef 
      (Ebinop Oadd arr index (Tpointer result_t noattr))
      result_t.
  
  Fixpoint getTableActionArgs (args: Clight.expr) (length: nat) : list (Clight.expr) :=
    match length with 
    | O => []
    | S l' => 
    getTableActionArgs args l' ++ 
    [(ArrayAccess args (Cint_of_Z (Z.of_nat length)) bit_vec)]
    end.

  Definition
    CTranslateTableInvoke
    (tbl : string) (key : list Expr.e)
    : StateT ClightEnv Result.result Clight.statement :=
    let* env := get_state in
    let* '(table_id, key_typ, fn_names) :=
      state_lift (find_table env tbl) in 
    let* action_id :=
      State_lift (CCompEnv.add_temp_nameless action_ref) in
    (* TODO: are matchkinds important? *)
    let* elist := CTranslateExprList key in
    let key_length := Z.of_nat (List.length key_typ) in 
    let t_keys := Tarray bit_vec key_length noattr in
    let* arrid :=
      State_lift (CCompEnv.add_temp_nameless t_keys) in
    let arg_action := Eaddrof (Evar action_id action_ref) TpointerActionRef in
    let arg_table := Eaddrof (Evar table_id table_t) TpointerTable in
    let arg_keys := Evar arrid t_keys in
    let '(_,assignArray) :=
      List.fold_left 
        (fun '((i, st) : nat * Clight.statement) val =>
           let index := Cint_of_Z (Z.of_nat i) in
           let st' :=
             Ssequence
               st
               (Sassign
                  (ArrayAccess (Evar arrid t_keys) index bit_vec)
                  val) in
           (Nat.add i (1%nat), st')) elist (O%nat, Sskip) in 
    let arg_list := [arg_action; arg_table; arg_keys] in
    let call :=
      Scall
        None
        (table_match_function (Z.of_nat (List.length key_typ)))
        arg_list in
    let action_to_take_id := Efield (Evar action_id action_ref) _action int_signed in
    let action_to_take_args := Efield (Evar action_id action_ref) _arguments TpointerBitVec in
    let^ '(_,application) :=
      state_lift
        (List.fold_right
           (fun f_name (x: Result.result (nat * Clight.statement)) =>
              let* '(f'_id, f') := CCompEnv.lookup_function env f_name in
              let^ '(i, st) := x in 
              let index := Cint_of_Z (Z.of_nat i) in
              let st' :=
                Sifthenelse
                  (Ebinop Oeq action_to_take_id index type_bool)
                  (let total_length := List.length (f'.(fn_params)) in
                   let top_args := get_top_args  env in
                   let top_length := List.length top_args in 
                   let args_length := Nat.sub total_length top_length in
                   let elist := getTableActionArgs action_to_take_args args_length in
                   let elist := top_args ++ elist in 
                   Scall None (Evar f'_id (Clight.type_of_function f')) elist) st in
              let i' := Nat.sub i 1 in
              (i',st'))
           (mret ((List.length fn_names), Sskip)) fn_names) in
    Ssequence assignArray (Ssequence call application).
  
  Fixpoint fold_nat {A} (f: A -> nat -> A) (n : nat) (init:A) : A:=
    match n with
    | O => init
    | S n' => f (fold_nat f n' init) n' 
    end.
  
  Fixpoint CTranslateExtract
           (arg: Expr.e) (type : Expr.t) (pname : nat)
    : StateT ClightEnv Result.result Clight.statement :=
    let* env := get_state in
    let* extern_name :=
      state_lift
        (Result.from_opt
           (nth_error env.(extern_instanceMap) pname)
           "extern name not found") in
    let packet :=
      Eaddrof (Evar extern_name (Ctypes.Tstruct _packet_in noattr)) TpointerPacketIn in
    match type with 
    | Expr.TBool => 
        let^ arg' := CTranslateExpr arg in
        let arg' := Eaddrof arg' TpointerBool in
        Scall None extract_bool_function [packet;arg']
    | Expr.TBit w => 
        let^ arg' := CTranslateExpr arg in
        let arg' := Eaddrof arg' TpointerBitVec in
        let is_signed := Cfalse in
        let width := Cint_of_Z (Z.of_N w) in
        Scall None extract_bitvec_function [packet;arg';is_signed; width]
    | Expr.TInt w => 
        let^ arg' := CTranslateExpr arg in
        let arg' := Eaddrof arg' TpointerBitVec in
        let is_signed := Ctrue in
        let width := Cint_of_Z (Zpos w) in
        Scall None extract_bitvec_function [packet;arg';is_signed; width]
    | Expr.TError => state_lift (Result.error "Can't extract to error")
    | Expr.TStruct fs _ =>
        (* TODO: set the validity if header *)
        state_list_mapi
          (fun i ft =>
             CTranslateExtract (Expr.Member ft i arg) ft pname) fs
          >>| statement_of_list
    | Expr.TVar _ => state_lift (Result.error "Can't extract to TVar")
    end.

  Fixpoint CTranslateEmit (arg: Expr.e) (type : Expr.t) (pname : nat)
    : StateT ClightEnv Result.result Clight.statement :=
    let* env := get_state in
    let* extern_name :=
      state_lift
        (Result.from_opt
           (nth_error env.(extern_instanceMap) pname)
           "extern name not found") in
    let packet :=
      Eaddrof
        (Evar extern_name (Ctypes.Tstruct _packet_out noattr))
        TpointerPacketOut in
    match type with 
    | Expr.TBool =>
        let^ arg' := CTranslateExpr arg in
        let arg' := Eaddrof arg' TpointerBool in
        Scall None emit_bool_function [packet;arg']
    | Expr.TBit w => 
        let^ arg' := CTranslateExpr arg in
        let arg' := Eaddrof arg' TpointerBitVec in 
        (* TODO: unused? 
           let is_signed := Cfalse in
           let width := Cint_of_Z (Z.of_N w) in *)
        Scall None emit_bitvec_function [packet;arg']
    | Expr.TInt w =>
        let^ arg' := CTranslateExpr arg in
        let arg' := Eaddrof arg' TpointerBitVec in
        (* TODO: unused?
           let is_signed := Ctrue in 
           let width := Cint_of_Z (Zpos w) in *)
        Scall None emit_bitvec_function [packet;arg']
    | Expr.TError => state_lift (Result.error "Can't extract to error")
    | Expr.TStruct fs _ =>
        (* TODO: check the validity and decide whether to emit *)
        state_list_mapi
          (fun i ft =>
             CTranslateEmit (Expr.Member ft i arg) ft pname) fs
          >>| statement_of_list
    | Expr.TVar _ => state_lift (Result.error "Can't extract to TVar")
    end.

  Definition CTranslateParams
    : Expr.params -> State ClightEnv (list (AST.ident * Ctypes.type)) :=
    state_list_map
      (fun param =>
         let* new_id := new_ident in
         let* '(ct, cparam) :=
           match param with
           | PAIn t =>
               let^ ct := CTranslateType t in (ct, ct)
           | PAOut t
           | PAInOut t =>
               let^ ct := CTranslateType t in (ct, Ctypes.Tpointer ct noattr)
           end in
         let* env := get_state in
         put_state (add_temp_arg env ct new_id) ;;
         mret (new_id, cparam)).

  (* Definition CTranslateConstructorParams (cparams : Expr.constructor_params) (env : ClightEnv )
    : list (AST.ident * Ctypes.type) * ClightEnv  
  := 
    List.fold_left 
      (fun (cumulator: (list (AST.ident * Ctypes.type)) * ClightEnv  ) (p: string * Expr.ct)
      =>let (l, env') := cumulator in
        let (env', new_id) := new_ident  env' in
        let (pname, typ) := p in
        let (ct,env_ct) :=  (CTranslateConstructorType typ env') in
        (*don't do copy in copy out*)
        (l ++ [(new_id, ct)], env_ct)) 
    (cparams) ([],env) . *)
  
  Definition CTranslateExternParams (extern_params : list string)
    : State ClightEnv (list (AST.ident * Ctypes.type)) :=
    let* (env : ClightEnv) := get_state in
    put_state (clear_extern_instance_types env) ;;
    state_list_map (M_Monad := identity_monad)
      (fun extern_param_type =>
         let* env := get_state (M_Monad := identity_monad) in
         let* (new_id : ident) := new_ident in
         (* TODO: is this correct? *)
         put_state
           (add_extern_instance_type
              (env <| extern_instanceMap := new_id :: env.(extern_instanceMap) |>)
              extern_param_type) ;;
         let ct := Ctypes.Tstruct $extern_param_type noattr in
         state_return (M_Monad := identity_monad) (new_id, ct))
      extern_params.
  
  Definition CCopyIn
    : Expr.params -> StateT ClightEnv Result.result Clight.statement :=
    (lift_monad statement_of_list)
      ∘ (state_list_mapi
           (fun (name : nat) (fn_param: paramarg Expr.t Expr.t) =>
              let* env := get_state in
              let* '(oldid, tempid) := state_lift (find_ident_temp_arg env name) in
              match fn_param with
              | PAIn t =>
                  let^ ct := State_lift (CTranslateType t) in
                  Sassign (Evar tempid ct) (Evar oldid ct)
              | PAOut t
              | PAInOut t => 
                  let^ ct := State_lift (CTranslateType t) in
                  Sassign
                    (Evar tempid ct)
                    (Ederef (Evar oldid (Ctypes.Tpointer ct noattr)) ct)
              end)).
  
  Definition CCopyOut
    : Expr.params ->
      StateT ClightEnv Result.result Clight.statement :=
    (lift_monad statement_of_list)
      ∘ (state_list_mapi
           (fun (name: nat) (fn_param: paramarg Expr.t Expr.t) =>
              let* env := get_state in
              let* (oldid, tempid) := state_lift (find_ident_temp_arg env name) in
              match fn_param with
              | PAIn t => 
                  let^ ct := State_lift (CTranslateType t) in
                  Sassign (Evar oldid ct) (Evar tempid ct)
              | PAOut t
              | PAInOut t =>
                  let^ ct := State_lift (CTranslateType t) in
                  Sassign
                    (Ederef (Evar oldid (Ctypes.Tpointer ct noattr)) ct)
                    (Evar tempid ct)
              end)).

  (** Return the list of args for the params. *)
  Definition CFindTempArgs
    : Expr.params ->
      StateT ClightEnv Result.result (list Clight.expr) :=
    state_list_mapi
      (fun (name: nat) (fn_param: paramarg Expr.t Expr.t) =>
         let* env := get_state in
         let* (oldid, tempid) := state_lift (find_ident_temp_arg env name) in
         match fn_param with 
         | PAIn t
         | PAOut t
         | PAInOut t =>
             State_lift (CTranslateType t >>| Evar tempid)
         end).

  (** Return the list of args for the params but adding directions.
      change the temp to ref temp if it is a out parameter. *)
  (* TODO: originally this function
     dropped state, should it do that? *)
  Definition CFindTempArgsForCallingSubFunctions
    : Expr.params
      -> StateT ClightEnv Result.result (list Clight.expr) :=
    state_list_mapi
      (fun (name: nat) (fn_param: (paramarg Expr.t Expr.t)) =>
         let* env := get_state in
         let* (oldid, tempid) := state_lift (find_ident_temp_arg env name) in
         match fn_param with
         | PAIn t => State_lift (CTranslateType t >>| Evar tempid)
         | PAOut t
         | PAInOut t =>
             let^ ct := State_lift (CTranslateType t) in
             Eaddrof (Evar tempid ct) (Tpointer ct noattr)
         end).

  Definition
    CFindTempArgsForSubCallsWithExtern
    (fn_params: Expr.params)
    (fn_eparams: list (AST.ident * Ctypes.type))
    : StateT ClightEnv Result.result (list Clight.expr) :=
    let^ call_args := CFindTempArgsForCallingSubFunctions fn_params in
    let e_call_args :=
      List.map (fun '(x,t) => Etempvar x t) fn_eparams in
    e_call_args ++ call_args.

  Definition CTranslateArrow '({|paramargs:=pas; rtrns:=ret|} : Expr.arrowT)
    : State ClightEnv (list (AST.ident * Ctypes.type) * Ctypes.type) :=
    let* fn_params := CTranslateParams pas in
    match ret with 
    | None => mret (fn_params, Ctypes.Tvoid)
    | Some return_t => 
        CTranslateType return_t >>| pair fn_params
    end.

  Definition CTranslatePatternVal (p : Parser.pat)
    : StateT ClightEnv Result.result (Clight.statement * ident) :=
    match p with
    | Parser.Bit width val =>
        let* fresh_id := State_lift new_ident in
        (* TODO: is fresh name necessary?
        let fresh_name :=
          String.append
            "_p_e_t_r_4_"
            (BinaryString.of_pos fresh_id) in
        put_state (add_var env fresh_name bit_vec) in
        let* dst := find_ident env fresh_name in *)
        let^ val_id := State_lift (find_BitVec_String val) in
        let w := Cint_of_Z (Z.of_N width) in
        let val' := Evar val_id Cstring in
        let dst' := Eaddrof (Evar fresh_id bit_vec) TpointerBitVec in
        (Scall None bitvec_init_function [dst'; Cfalse; w; val'], fresh_id)
    | Parser.Int width val => 
        let* fresh_id := State_lift new_ident in
        (*let fresh_name := String.append "_p_e_t_r_4_" (BinaryString.of_pos fresh_id) in
        let env := add_var  env fresh_name bit_vec in 
        let* dst := find_ident  env fresh_name in*)
        let^ val_id := State_lift (find_BitVec_String val) in 
        let w := Cint_of_Z (Zpos width) in
        let val' := Evar val_id Cstring in
        let dst' := Eaddrof (Evar fresh_id bit_vec) TpointerBitVec in
        (Scall None bitvec_init_function [dst'; Ctrue; w; val'], fresh_id)
    | _ => state_lift (Result.error "not a pattern value")
    end.

  Definition CTranslatePatternMatch (input: Clight.expr) (p: Parser.pat)
    : StateT ClightEnv Result.result (Clight.statement * ident) :=
    let* dst := State_lift new_ident in
    (* TODO: is fresh_name needed?
    let fresh_name := String.append "_p_e_t_r_4_" (BinaryString.of_pos fresh_id) in
    let env := add_var  env fresh_name type_bool in 
    let* dst := find_ident  env fresh_name in *)
    let dst' := Eaddrof (Evar dst type_bool) TpointerBool in
    match p with
    | Parser.Wild => mret (Sassign dst' Ctrue, dst)
    | Parser.Mask p1 p2 => 
      let* (init1, var_left) := CTranslatePatternVal p1 in
      let* (init2, var_right) := CTranslatePatternVal p2 in
      let* inputand := State_lift new_ident in
      (* TODO: is fresh_name needed?
      let fresh_name := String.append "_p_e_t_r_4_" (BinaryString.of_pos fresh_id) in
      let env := add_var  env fresh_name bit_vec in 
      let* inputand := find_ident  env fresh_name in *)
      let^ valueand := State_lift new_ident in
      (* TODO: is fresh_name needed?
      let fresh_name := String.append "_p_e_t_r_4_" (BinaryString.of_pos fresh_id) in
      let env := add_var  env fresh_name bit_vec in 
      let* valueand := find_ident  env fresh_name in *)
      let inand' := Eaddrof (Evar inputand bit_vec) TpointerBitVec in
      let valand' := Eaddrof (Evar valueand bit_vec) TpointerBitVec in
      let assign_in :=
        Scall
          None (bop_function _interp_bitwise_and)
          [inand'; input; (Evar var_right bit_vec)] in
      let assign_val :=
        Scall
          None (bop_function _interp_bitwise_and)
          [valand'; (Evar var_left bit_vec); (Evar var_right bit_vec)] in
      let assign :=
        Scall
          None (bop_function _interp_beq)
          [dst'; (Evar inputand bit_vec); (Evar valueand bit_vec)] in
      let stmts :=
        (Ssequence
           init1
           (Ssequence
              init2
              (Ssequence
                 assign_in
                 (Ssequence
                    assign_val
                    assign)))) in
      (stmts, dst)
    | Parser.Range p1 p2 =>
      let* (init1, var_left) := CTranslatePatternVal p1 in
      let* (init2, var_right) := CTranslatePatternVal p2 in
      let* lefttrue := State_lift new_ident in
      (* TODO: is fresh name needed?
      let fresh_name := String.append "_p_e_t_r_4_" (BinaryString.of_pos fresh_id) in
      let env := add_var  env fresh_name type_bool in
      let* lefttrue := find_ident  env fresh_name in *)
      let^ righttrue := State_lift new_ident in
      (* TODO: is fresh name needed?
      let fresh_name := String.append "_p_e_t_r_4_" (BinaryString.of_pos fresh_id) in
      let env := add_var  env fresh_name type_bool in 
      let* righttrue := find_ident  env fresh_name in *)
      let lefttrue' := Eaddrof (Evar lefttrue type_bool) TpointerBool in
      let righttrue' := Eaddrof (Evar righttrue type_bool) TpointerBool in
      let assign_left :=
        Scall
          None (bop_function _interp_bge)
          [lefttrue'; input; (Evar var_left bit_vec)] in
      let assign_right :=
        Scall
          None (bop_function _interp_ble)
          [righttrue'; input; (Evar var_right bit_vec)] in
      let and_expr :=
        Ebinop
          Oand (Evar lefttrue type_bool)
          (Evar righttrue type_bool) type_bool in
      let assign := Sassign dst' and_expr in 
      let stmts := 
        (Ssequence
           init1
           (Ssequence
              init2
              (Ssequence
                 assign_left
                 (Ssequence
                    assign_right
                    assign)))) in
      (stmts, dst)
    | Parser.Int _ _
    | Parser.Bit _ _ => 
        let^ (init, var) := CTranslatePatternVal p in
        let assign := 
          Scall None (bop_function _interp_beq) [dst'; input; (Evar var bit_vec)] in
        (Ssequence init assign, dst)
    | Parser.Struct ps =>
        state_lift (Result.error "not a simple pattern match")
    end.

  Definition CTranslateParserExpressionVal (pe: Parser.e)
    : StateT ClightEnv Result.result Clight.statement :=
    let* env := get_state in
    let rec_call_args := get_top_args env in
    match pe with
    | Parser.Goto st =>
        match st with
        | Parser.Start =>
            let^ (start_id, start_f) :=
              state_lift (lookup_function env "start") in
            Scall
              None (Evar start_id (Clight.type_of_function start_f))
              rec_call_args
        | Parser.Accept => state_return (Sreturn (Some Ctrue))
        | Parser.Reject => state_return (Sreturn (Some Cfalse))
        | Parser.Name x =>
            let* x_id :=
              state_lift
                (Result.from_opt
                   (nth_error env.(parser_stateMap) x)
                   "TODO: need helper for this") in
            let^ x_f :=
              state_lift
                (Result.from_opt
                   (Env.find x_id env.(fenv))
                   "TODO: need helper for this") in
            Scall
              None (Evar x_id (Clight.type_of_function x_f))
              rec_call_args
        end
    | Parser.Select exp def cases =>
        state_lift
          (Result.error "nested select expression, currently unsupported")
    end.    
  
  Definition CTranslateParserExpression (pe: Parser.e)
    : StateT ClightEnv Result.result Clight.statement :=
    match pe with 
    | Parser.Select exp def cases => 
        let* input := CTranslateExpr exp in
        let* default_stmt := CTranslateParserExpressionVal (Parser.Goto def) in
        let fold_function
              '((p, action): Parser.pat * Parser.state) fail_stmt :=
          let* (match_statement, this_match) :=
            CTranslatePatternMatch input p in
          let^ success_statement :=
            CTranslateParserExpressionVal (Parser.Goto action) in
          Ssequence
            match_statement
            (Sifthenelse (Evar this_match type_bool) success_statement fail_stmt) in
        state_fold_right fold_function default_stmt cases
    | _ => CTranslateParserExpressionVal pe
    end.

  Fixpoint CTranslateStatement (s: Stmt.s)
    : StateT ClightEnv Result.result Clight.statement :=
    match s with
    | Stmt.Skip => mret Sskip
    | Stmt.Seq s1 s2 =>
        (* TODO: need to correctly consider de bruijn stuff here *)
        let* s1' := CTranslateStatement s1 in
        let^ s2' := CTranslateStatement s2 in
        Ssequence s1' s2'
    | Stmt.Var (inl t) s =>
        (* TODO: why skip returned? *)
        let* cty := State_lift (CTranslateType t) in
        let* env := get_state in
        put_state (CCompEnv.add_var env cty) ;;
        CTranslateStatement s
    | Stmt.Var (inr e) s =>
        (* TODO: need to double check
           that I update env at the correct place. *)
      let t := t_of_e e in
      let* cty := State_lift (CTranslateType t) in
      let* env := get_state in
      put_state (CCompEnv.add_var env cty) ;;
      let* env := get_state in
      let* dst' := state_lift (find_var env 0) in
      match e with
      | Expr.Bit width val =>
          let* val_id := State_lift (find_BitVec_String val) in
          let w := Cint_of_Z (Z.of_N width) in
          let signed := Cfalse in 
          let val' := Evar val_id Cstring in
          let dst' := Eaddrof (Evar dst' bit_vec) TpointerBitVec in
          let^ s' := CTranslateStatement s in
          Ssequence
            (Scall None bitvec_init_function [dst'; signed; w; val'])
            s'
      | Expr.Int width val =>
          let* val_id := State_lift (find_BitVec_String val) in
          let w := Cint_of_Z (Zpos width) in
          let signed := Ctrue in 
          let val' := Evar val_id Cstring in
          let dst' := Eaddrof (Evar dst' bit_vec) TpointerBitVec in
          let^ s' := CTranslateStatement s in
          Ssequence
            (Scall None bitvec_init_function [dst'; signed; w; val'])
            s'
      | Expr.Slice n hi lo =>
          let τ := t_of_e n in
          let* n' := CTranslateExpr n in
          let hi' := Cuint_of_Z (Zpos hi) in
          let lo' := Cuint_of_Z (Zpos lo) in
          let* tau' := State_lift (CTranslateType τ) in
          let dst' := Evar dst' tau' in
          let^ s' := CTranslateStatement s in
          Ssequence
            (Scall None slice_function [n'; hi'; lo'; dst'])
            s'
      | Expr.Cast τ e =>
          let* e' := CTranslateExpr e in
          let* tau' := State_lift (CTranslateType τ) in
          let dst' := Evar dst' tau' in
          let s1 :=
            match τ, t_of_e e with
            | Expr.TBool, Expr.TBit _ =>
                Scall None cast_to_bool_function [dst'; e']
            | Expr.TBit _, Expr.TBool =>
                Scall None cast_from_bool_function [dst'; e']
            | Expr.TBit w, Expr.TInt _
            | Expr.TBit w, Expr.TBit _ =>
                let t := Cuint_zero in
                let width := Cuint_of_Z (Z.of_N w) in
                Scall None cast_numbers_function [dst'; e'; t; width]
            | Expr.TInt w, Expr.TBit _
            | Expr.TInt w, Expr.TInt _ =>
                let t := Cuint_zero in
                let width := Cuint_of_Z (Zpos w) in
                Scall None cast_numbers_function [dst'; e'; t; width]
            | _, _ => Sskip
            end in
          let^ s2 := CTranslateStatement s in
          Ssequence s1 s2
      | Expr.Uop dst_t op x =>
          let* s1 := CTranslateUop dst_t op x 0 in
          let^ s2 := CTranslateStatement s in
          Ssequence s1 s2
      | Expr.Bop dst_t op x y =>
          let* s1 := CTranslateBop dst_t op x y 0 in
          let^ s2 := CTranslateStatement s in
          Ssequence s1 s2
      | Expr.Struct fields None =>
          (*first create a temp of this struct.
            then assign all the values to it. then return this temp *)
          let strct := t_of_e e in
          let* typ := State_lift (CTranslateType strct) in
          let* env := get_state in
          let* composite := state_lift (lookup_composite env strct) in
          let* s1 :=
            CTranslateStructAssgn
              fields composite (Evar dst' typ) in
          let^ s2 := CTranslateStatement s in
          Ssequence s1 s2
      | Expr.Struct fields (Some b) =>
          (*first create a temp of this header.
            then assign all the values to it. then return this temp*)
          let hdr := t_of_e e in
          let* typ := State_lift (CTranslateType hdr) in
          let valid := if b then Ctrue else Cfalse in
          let* env := get_state in
          let* composite := state_lift (lookup_composite env hdr) in
          let* s1 :=
            CTranslateHeaderAssgn
              fields composite (Evar dst' typ) valid in
          let^ s2 := CTranslateStatement s in
          Ssequence s1 s2
      | _ =>
          let* e' := CTranslateExpr e in
          let^ s' := CTranslateStatement s in
          Ssequence (Sassign (Evar dst' (typeof e'))  e') s'
      end
    | Stmt.Conditional e s1 s2 => 
        let* e' := CTranslateExpr e in
        let* s1' := CTranslateStatement s1 in
        let^ s2' := CTranslateStatement s2 in                 
        Sifthenelse e' s1' s2'
    | Stmt.Call (Stmt.Funct f _ None) args =>
        let* env := get_state in
        let* (id, f') := state_lift (CCompEnv.lookup_function env f) in
        let^ elist := CTranslateArgs args in
        Scall None (Evar id (Clight.type_of_function f')) elist
    | Stmt.Call (Stmt.Action f ctrl_args) data_args =>
        let* env := get_state in
        let* (id, f') := state_lift (CCompEnv.lookup_action_function env f) in
        let* ctrl_list := CTranslateExprList ctrl_args in
        let* data_list := CTranslateArgs data_args in
        let^ env' := get_state in 
        let elist := (get_top_args env') ++ ctrl_list ++ data_list in
        Scall None (Evar id (Clight.type_of_function f')) elist
    | Stmt.Call (Stmt.Funct f _ (Some e)) args =>
        let t := t_of_e e in
        let* ct := State_lift (CTranslateType t) in
        let* env_ct := get_state in
        let* (id, f') := state_lift (CCompEnv.lookup_function env_ct f) in
        let* elist := CTranslateArgs args in
        let* env' := get_state in
        let* tempid := State_lift (CCompEnv.add_temp_nameless ct) in
        let^ lvalue := CTranslateExpr e in 
        Ssequence
          (Scall (Some tempid) (Evar id (Clight.type_of_function f')) elist)
          (Sassign lvalue (Etempvar tempid ct))
    | Stmt.Call (Stmt.Method e f _ x) args =>
        let* env := get_state in
        let* t := state_lift (find_extern_type env e) in
        (* TODO: what to do about expecting specific
           architectures? *)
        if String.eqb t "packet_in" then
          if String.eqb f "extract" then
            match nth_error args 0 with
            | Some (PAOut arg) =>
                CTranslateExtract arg (t_of_e arg) e
            | _ => state_lift (Result.error "no out argument named hdr")
            end
          else mret Sskip
        else 
          if String.eqb t "packet_out" then
            if String.eqb f "emit" then
              match nth_error args 0 with 
              | Some (PAIn arg) => 
                  CTranslateEmit arg (t_of_e arg) e
              | _ => state_lift (Result.error "no out argument named hdr")
              end
            else mret Sskip
          else
            if String.eqb f "mark_to_drop" then
              match nth_error args 0 with
              | Some (PAInOut arg) =>
                  let^ elist := CTranslateArgs args in
                  Scall None mark_to_drop_function elist
              | _ => state_lift
                      (Result.error "no inout argument named standard_metadata")
              end
            else
              mret Sskip (*TODO: implement, need to be target specific.*)
    | Stmt.Return (Some e) =>
      let^ e' := CTranslateExpr e in Sreturn (Some e')
    | Stmt.Return None => mret (Sreturn None)
    | Stmt.Exit => mret (Sreturn (Some Cfalse))
    | Stmt.Apply x ext args =>
        let* env := get_state in
        (* TODO: need to know context [apply block, function, etc.]. *)
        let* (id, f') := state_lift (lookup_control_instance_function env x) in
        let* elist := CTranslateArgs args in
        let* resultid := State_lift (CCompEnv.add_temp_nameless type_bool) in
        let result := (Etempvar resultid type_bool) in 
        let kompute :=
          Scall (Some resultid) (Evar id (Clight.type_of_function f')) elist in
        let judge := Sifthenelse (result) Sskip (Sreturn (Some Cfalse)) in
        mret (Ssequence kompute judge)
    | Stmt.Invoke tbl key => CTranslateTableInvoke tbl key
    | Stmt.Assign e1 e2 =>
      let* e1' := CTranslateExpr e1 in
      let^ e2' := CTranslateExpr e2 in
      Sassign e1' e2'
    | Stmt.Transition pe =>
        (* TODO: is this correct? *)
        CTranslateParserExpression pe
    end.
  
  Definition CTranslateParserState
             (stmt : Stmt.s) (params: list (AST.ident * Ctypes.type))
    : StateT ClightEnv Result.result Clight.function :=
    let* env := get_state (M_Monad := Result.result_monad_inst) in
    let* stmt := CTranslateStatement stmt in
    (*let rec_call_args := get_top_args  env' in*)
    let* env' := get_state in
    put_state (set_temp_vars env env') ;;
    state_return
      (Clight.mkfunction
            Ctypes.type_bool
            (AST.mkcallconv None true true)
            params
            (CCompEnv.get_vars env)
            (CCompEnv.get_temps env)
            stmt).

  Definition CTranslateTopParser (parsr: TopDecl.d)
             (init: Clight.statement) (instance_name: nat)
    : StateT ClightEnv Result.result unit :=
    match parsr with
    | TopDecl.Parser p _ eps params start states =>
        let* env := get_state (M_Monad := Result.result_monad_inst) in
        let* fn_eparams := State_lift (M_Monad := Result.result_monad_inst) (CTranslateExternParams eps) in
        let* fn_params := State_lift (M_Monad := Result.result_monad_inst) (CTranslateParams params) in
        let* copyin := CCopyIn params in
        let* copyout := CCopyOut params in
        (*copy in and copy out may need to copy cparams and eparams as well*)
        let* env_copyout := get_state (M_Monad := Result.result_monad_inst) in
        let* call_args := CFindTempArgsForSubCallsWithExtern params fn_eparams env_copyout in
        let env_copyout := set_top_args env_copyout call_args in
        let fn_params := fn_eparams ++ fn_params in
        (*all functions inside one top parser declaration should have the same parameter*)
        let fn_sig :=
          (Clight.mkfunction 
             type_bool 
             (AST.mkcallconv None true true) 
             fn_params [] [] Sskip) in
        let env_start_fn_sig_declared := CCompEnv.add_function env_copyout "start" fn_sig in
        let env_fn_sig_declared :=
          fold_right
            (fun _ env => add_parser_state env fn_sig)
            env_start_fn_sig_declared states in
        put_state (M_Monad := Result.result_monad_inst) (set_temp_vars env env_fn_sig_declared) ;;
        state_fold_righti
          (fun (state_name: nat) (sb : Stmt.s) 'tt =>
             let* f := CTranslateParserState sb fn_params in
             let* env_f_translated := get_state (M_Monad := Result.result_monad_inst) in
             put_state (M_Monad := Result.result_monad_inst) (update_parser_state env_f_translated state_name f))
          tt states ;;
        (*finished declaring all the state blocks except start state*)
        let* f_start := CTranslateParserState start fn_params in
        let* env_start_translated := get_state (M_Monad := Result.result_monad_inst) in
        put_state (M_Monad := Result.result_monad_inst)
          (set_temp_vars
             env_copyout
             (CCompEnv.update_function env_start_translated "start" f_start)) ;;
        let* env_start_declared := get_state (M_Monad := Result.result_monad_inst) in
        let* (start_id, start_f) := state_lift (M_Monad := Result.result_monad_inst) (lookup_function env_start_declared "start") in
        let fn_body :=
          Ssequence
            init
            (Ssequence
               copyin 
               (Ssequence 
                  (Scall None (Evar start_id (Clight.type_of_function start_f)) call_args)
                  (Ssequence
                     copyout
                     (Sreturn (Some Ctrue))))) in
        let top_function :=
          (Clight.mkfunction
             type_bool
             (AST.mkcallconv None true true)
             fn_params
             (get_vars  env_start_declared)
             (get_temps  env_start_declared)
             fn_body) in
        let* instance_name := state_lift (nth_error env.(parser_instanceMap) instance_name) in
        put_state
          (M_Monad := Result.result_monad_inst)
          (set_temp_vars
             env
             (env_start_declared
                <| fenv := Env.bind instance_name top_function env_start_declared.(fenv) |>))
    | _ => state_lift (Result.error "not parser")
    end.


  Definition CTranslateAction 
  (signature: Expr.params) (body: Stmt.s ) 
  (env: ClightEnv  ) (top_fn_params: list (AST.ident * Ctypes.type))
  (top_signature: Expr.params)
  : @error_monad string (Clight.function* ClightEnv  ):= 
  let (fn_params, env_params_created) := CTranslateParams signature env in
  let fn_params := top_fn_params ++ fn_params in 
  let full_signature := top_signature ++ signature in
  let* (copyin, env_copyin) := CCopyIn full_signature env_params_created in
  let* (copyout, env_copyout) := CCopyOut full_signature env_copyin in
  let* (c_body, env_body_translated) := CTranslateStatement body env_copyout in
  let body:= Ssequence copyin (Ssequence c_body copyout) in
  mret (
    (Clight.mkfunction 
      type_bool
      (AST.mkcallconv None true true)
      fn_params 
      (get_vars  env_body_translated)
      (get_temps  env_body_translated)
      body), (set_temp_vars  env env_body_translated))
  .
  
  Fixpoint CTranslateControlLocalDeclaration 
  (ct : Control.d ) (env: ClightEnv  ) 
  (top_fn_params: list (AST.ident * Ctypes.type))
  (top_signature: Expr.params)
  : @error_monad string (Clight.statement * ClightEnv  )
  := match ct with
  | Control.CDSeq d1 d2 i=> 
    let* (s1, env1) := CTranslateControlLocalDeclaration d1 env top_fn_params top_signature in
    let* (s2, env2) := CTranslateControlLocalDeclaration d2 env1 top_fn_params top_signature in 
    mret (Ssequence s1 s2, env2)
    
  | Control.CDAction a params body => 
    let* (f, env_action_translated) := CTranslateAction params body env top_fn_params top_signature in
    mret (Sskip, CCompEnv.add_function  env_action_translated a f)

  | Control.CDTable name {|Control.table_key:=keys; Control.table_actions:=acts|} => 
    let env := add_Table  env name keys acts in 
    let* '(id, _, _) := find_table  env name in 
    let num_keys :=  Cint_of_Z (Z.of_nat (List.length keys)) in
    let size := Cint_of_Z (256) in
    let decl_stmt := Scall (Some id) bitvec_init_function [num_keys; size] in 
    mret (decl_stmt, env)
  end.
  
  Definition CTranslateTopControl (ctrl: TopDecl.d ) (env: ClightEnv ) 
    (init: Clight.statement) (instance_name: string)
    : @error_monad string (ClightEnv  )
  := 
    match ctrl with
    | TopDecl.TPControl c _ eps params body blk => 
      let (fn_eparams, env_top_fn_eparam) := CTranslateExternParams eps env in
      let (fn_params, env_top_fn_param) := CTranslateParams params env_top_fn_eparam in
      let* (copyin, env_copyin) := CCopyIn params env_top_fn_param in 
      let* (copyout, env_copyout) := CCopyOut params env_copyin in
      let* call_args := CFindTempArgsForSubCallsWithExtern params fn_eparams env_copyout in 
      let env_copyout := set_top_args  env_copyout call_args in
      let fn_params := fn_eparams ++ fn_params in 
      let* (table_init, env_local_decled) := CTranslateControlLocalDeclaration body env_copyout fn_params params in
      let* (apply_blk, env_apply_block_translated) := CTranslateStatement blk env_local_decled in
      let body:= Ssequence init (Ssequence copyin (Ssequence apply_blk (Ssequence copyout (Sreturn (Some Ctrue))))) in
      let top_fn := 
        Clight.mkfunction 
          type_bool 
          (AST.mkcallconv None true true)
          fn_params 
          (get_vars  env_apply_block_translated)
          (get_temps  env_apply_block_translated)
          (Ssequence table_init body) in
      let env_top_fn_declared := 
        CCompEnv.add_function  env_apply_block_translated instance_name top_fn in
      mret (set_temp_vars  env env_top_fn_declared) 

    | _ => Result.error "not a top control"
    end.


  
  Definition CTranslateFunction (funcdecl : TopDecl.d ) (env: ClightEnv  )
    : @error_monad string (ClightEnv  )
  := 
    match funcdecl with
    | TopDecl.TPFunction name _ signature body _ => 
      let '(fn_params, fn_return, env_params_created) := CTranslateArrow signature env in 
      let paramargs := AST.paramargs signature in
      let* (copyin, env_copyin) := CCopyIn paramargs env_params_created in
      let* (copyout, env_copyout) := CCopyOut paramargs env_copyin in
      let* (c_body, env_body_translated) := CTranslateStatement body env_copyout in
      let body:= Ssequence copyin (Ssequence c_body copyout) in
      let top_function := 
        (Clight.mkfunction 
          fn_return
          (AST.mkcallconv None true true)
          fn_params 
          (get_vars  env_body_translated)
          (get_temps  env_body_translated)
          body) in
      mret (set_temp_vars  env (CCompEnv.add_function  env_params_created name top_function))

    | _ => Result.error "not a function"
    end.
  
  Definition InjectConstructorArg (arg_name: string) 
    (arg: Expr.constructor_arg ) 
    (cumulator: @error_monad string (ClightEnv  * Clight.statement))
    : @error_monad string (ClightEnv  * Clight.statement) := 
    let* (env, st) := cumulator in 
    match arg with 
    | Expr.CAExpr e => 
      let* (init, env) := 
      match e with 
      | Expr.Bool b =>
        let env := add_var  env arg_name type_bool in 
        let* val_id := find_ident  env arg_name in
        let initialize := 
          if b then 
            Sassign (Evar val_id type_bool) Cfalse 
          else 
            Sassign (Evar val_id type_bool) Ctrue 
        in
        mret (initialize, env)
      | Expr.Bit width val => 
        let env := add_var  env arg_name bit_vec in 
        let* dst := find_ident  env arg_name in
        let (env', val_id) := find_BitVec_String  env val in 
        let w := Cint_of_Z (Z.of_N width) in
        let signed := Cfalse in 
        let val' := Evar val_id Cstring in
        let dst' := Eaddrof (Evar dst bit_vec) TpointerBitVec in
        mret (Scall None bitvec_init_function [dst'; signed; w; val'], env')
      | Expr.Int width val => 
        let env := add_var  env arg_name bit_vec in 
        let* dst := find_ident  env arg_name in
        let (env', val_id) := find_BitVec_String  env val in 
        let w := Cint_of_Z (Zpos width) in
        let signed := Ctrue in 
        let val' := Evar val_id Cstring in
        let dst' := Eaddrof (Evar dst bit_vec) TpointerBitVec in
        mret (Scall None bitvec_init_function [dst'; signed; w; val'], env')
      | _ => Result.error "not folded constant"
        end in 
        mret (env, Ssequence st init)
    | Expr.CAName x =>
      let* instance_id := CCompEnv.find_ident  env x in 
      mret (CCompEnv.bind  env arg_name instance_id, st)
    end.

  Definition InjectConstructorArgs (env: ClightEnv ) (cargs: Expr.constructor_args )
    : @error_monad string (ClightEnv  * Clight.statement) :=
    F.fold InjectConstructorArg cargs (mret (env, Sskip)).

  Fixpoint CCollectTypVar (d: TopDecl.d ) (env: ClightEnv ) : @error_monad string (ClightEnv )
  := match d with 
  | TopDecl.TPSeq d1 d2 => 
    let* env1 := CCollectTypVar d1 env in
    CCollectTypVar d2 env1 

  | TopDecl.TPInstantiate c x ts args => 
    if (String.eqb x "main") then 
      let env' := List.fold_left (fun e t => snd (CTranslateType t e)) ts env in
      match ts, F.get "p" args, F.get "vr" args, F.get "ig" args, F.get "eg" args, F.get "ck" args
      , F.get "dep" args  with 
      | H :: M :: [], Some (Expr.CAName p), Some (Expr.CAName vr),
       Some (Expr.CAName ig), Some (Expr.CAName eg), Some (Expr.CAName ck), Some (Expr.CAName dep) => 
        let* env_H := set_H  env' H in 
        let* env_M := set_M  env_H M in
        let env_p := add_expected_control  env_M "parser" p  in 
        let env_vr := add_expected_control  env_p "verify" vr  in
        let env_ig := add_expected_control  env_vr "ingress" ig in
        let env_eg := add_expected_control  env_ig "egress" eg in
        let env_ck := add_expected_control  env_eg "compute" ck in
        let env_dep := add_expected_control  env_ck "deparser" dep in

        mret env_dep
      | _,_,_,_,_,_,_ => Result.error "main instantiation not following V1model convention"
      end
    else mret env 
 
  | _ => mret env
  end.

  Fixpoint CTranslateTopDeclaration (d: TopDecl.d ) (env: ClightEnv  ) : @error_monad string (ClightEnv  )
  := 
  match d with
  | TopDecl.TPSeq d1 d2 => 
    let* env1 := CTranslateTopDeclaration d1 env in
    CTranslateTopDeclaration d2 env1 

  | TopDecl.TPInstantiate c x ts args => 
    let env := add_tpdecl  env x d in
    let env := if (String.eqb x "main") then set_instantiate_cargs  env args else env in
    match lookup_topdecl  env c with 
    | inl tpdecl => 
      match tpdecl with
      | TopDecl.TPParser _ _ _ _ _ _ _  =>
        let x := 
          match lookup_expected_instance  env "parser" with
          | None => x
          | Some name => if (String.eqb x name) then "parser" else x end in
        let* (env, init) := InjectConstructorArgs env args in
         CTranslateTopParser tpdecl env init x

      | TopDecl.TPControl _ _ _ _ _ _ _ =>
        let x := 
          match lookup_expected_instance  env "verify",
          lookup_expected_instance  env "ingress", 
          lookup_expected_instance  env "egress",
          lookup_expected_instance  env "compute",
          lookup_expected_instance  env "deparser" with  
          | Some vr, Some ig ,Some eg ,Some ck ,Some dep =>
            if (String.eqb x vr) then "verify" else 
            if (String.eqb x ig) then "ingress" else
            if (String.eqb x eg) then "egress" else
            if (String.eqb x ck) then "compute" else
            if (String.eqb x dep) then "deparser" else
            x 
          | _,_,_,_,_ => x 
          end in            
        let* (env, init) := InjectConstructorArgs env args in 
        CTranslateTopControl tpdecl env init x 

      | _ => mret env
      end
    | _ => mret env
    end
  | TopDecl.TPFunction _ _ _ _ _ => CTranslateFunction d env
  | TopDecl.TPExtern e _ cparams methods => mret env (*TODO: implement*)
  | TopDecl.TPControl name _ _ _ _ _ _ => mret (add_tpdecl  env name d)
  (* CTranslateTopControl d env *)
  | TopDecl.TPParser name _ _ _ _ _ _ => mret (add_tpdecl  env name d)
   (* CTranslateTopParser d env *)
  end.

  Fixpoint remove_composite (comps: list Ctypes.composite_definition) (name : ident) :=
    match comps with 
    | [] => comps
    | (Composite id su m a) :: tl => if (Pos.eqb id name) then 
                                        tl
                                     else (Composite id su m a) :: (remove_composite tl name)
    end. 
  (* Fixpoint remove_public (comps: list Ctypes.composite_definition) (name : ident) :=
    match comps with 
    | [] => comps
    | (Composite id su m a) :: tl => if (Pos.eqb id name) then 
                                        tl
                                      else (Composite id su m a) :: (remove_composite tl name)
    end.  *)
  (* Definition RemoveStdMetaDecl (prog: Clight.program) : Clight.program :=
    {|
      prog_defs := prog.(prog_defs);
      prog_public := prog.(prog_public);
      prog_main := prog.(prog_main);
      prog_types := remove_composite prog.(prog_types) ($"standard_metadata_t");
      prog_comp_env := prog.(prog_comp_env);
      prog_comp_env_eq := _
    |}. *)

  Definition Compile (prog: TopDecl.d ) : Errors.res (Clight.program*ident*ident) := 
    let init_env := CCompEnv.newClightEnv  in
    match CCollectTypVar prog init_env with 
    | inr m => Errors.Error (Errors.msg (m ++ "from collectTypVar"))
    | inl init_env  => 
    let main_id := $"dummy_main" in 
    match CTranslateTopDeclaration prog init_env with
    | inr m => Errors.Error (Errors.msg (m ++ "from TopDeclaration"))
    | inl env_all_declared => 
      match CCompEnv.get_functions  env_all_declared with
      | inr _ => Errors.Error (Errors.msg "can't find all the declared functions")
      | inl f_decls => 
      let f_decls := List.map 
        (fun (x: AST.ident * Clight.function) 
        => let (id, f) := x in 
        (id, AST.Gfun(Ctypes.Internal f))) f_decls in
      let typ_decls := CCompEnv.get_composites  env_all_declared in
      let typ_decls := remove_composite typ_decls ($"standard_metadata_t") in
      (* There's no easy way of deleting the main_decl completely *)
      (* Mainly because clight expect a program to have a main function *)
      (* if we don't have a main function, I'm not sure how to print the result out
      as a c file. *)
      (* But we need all definitions to be public now *)
      let main_decl :=
      AST.Gfun (Ctypes.Internal (main_fn  env_all_declared (get_instantiate_cargs  env_all_declared)))
      in 
      let gvars := get_globvars  env_all_declared in 
      let gvars := List.map 
        (fun (x: AST.ident * globvar Ctypes.type)
        => let (id, v) := x in 
        (id, AST.Gvar(v))) gvars in
      let globdecl := gvars ++ ((main_id, main_decl):: f_decls) in
      let pubids := List.map (fun (x: ident * globdef (fundef Clight.function) type) =>
                              let (id, _) := x in 
                              id) globdecl in
      let v1model_H := get_H  env_all_declared in
      let v1model_M := get_M  env_all_declared in
      match (make_program typ_decls globdecl pubids main_id) with
      | @Errors.Error (_) em => Errors.Error em
      | Errors.OK res_p => 
        Errors.OK (res_p, v1model_H, v1model_M)
      end
      end
    end
    end.

  (* Definition Compile_print (prog: TopDecl.d ): unit := 
    match Compile prog with
    | Errors.Error e => tt
    | Errors.OK prog => print_Clight prog
    end.   *)
End CCompSel.

(* Require Poulet4.Compile.ToP4cub.
Require Poulet4.Monads.Result.
Require Poulet4.P4light.Syntax.P4defs.
Require Poulet4.Ccomp.Example.

Definition helloworld_program := 
  match ToP4cub.translate_program' P4defs.Info P4defs.Inhabitant_Info Example.prog with
  | @Result.Error (_) e => Errors.Error (Errors.msg e)
  | @Result.Ok (_) p =>
    p
  end. 

Compute helloworld_program. *)


(* Definition helloworld_program_sel := Statementize.TranslateProgram helloworld_program.
Definition test_program_only := 
  CCompSel.Compile nat helloworld_program_sel.

Definition test := 
  CCompSel.Compile_print nat helloworld_program_sel. *)
