From compcert Require Import AST Clight Ctypes Integers Cop Clightdefs.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
Require Import List BinaryString
  Coq.PArith.BinPos Coq.NArith.BinNat
  Coq.ZArith.BinInt String.
Require Import
        Poulet4.P4cub.Syntax.Syntax Poulet4.Utils.Envn.
From Poulet4 Require Import
     P4cub.Transformations.Lifting.Statementize
     Monads.Monad Monads.Option Monads.Error Monads.State Monads.Result
     Ccomp.CCompEnv (*Ccomp.Helloworld*) Ccomp.CV1Model Ccomp.Cconsts.
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
    | Expr.TArray n t =>
        let^ t := CTranslateType t in
        Tarray t (Z.of_N n) noattr
    | Expr.TStruct is_header fields =>
        let* komposit := search_state (lookup_composite p4t) in
        match komposit with
        | Result.Ok comp =>
            (* found identifier *)
            mret (Ctypes.Tstruct (Ctypes.name_composite_def comp) noattr)
        | _ =>
            (* need to generate identifiers *)
            let* top_id := CCompEnv.new_ident in
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
            modify_state (CCompEnv.add_composite_typ p4t comp_def) ;;
            mret (Ctypes.Tstruct top_id noattr)
        end
    end.

  Definition
    ArrayAccess (arr : Clight.expr)
    (index : Clight.expr) (result_t: Ctypes.type) : Clight.expr := 
    Ederef 
      (Ebinop Oadd arr index (Tpointer result_t noattr))
      result_t.
  
  Fixpoint CTranslateExpr (e: Expr.e)
    : StateT ClightEnv (result string) Clight.expr :=
    match e with
    | Expr.Bool true  => mret Ctrue
    | Expr.Bool false => mret Cfalse
    | Expr.Var ty _ x =>
        (*first find if x has been declared. If not, declare it *)
        let* cty :=
          State_lift
            (M := (result string))
            (A := Ctypes.type) (CTranslateType ty) in
        let* temp_arg :=
          proj_state
            (find_ident_temp_arg x) in
        match temp_arg with 
        (*first look for if this is an argument and has its own temp for copy in/out *)
        | Result.Ok (_,tempid) => mret (Etempvar tempid cty)
        | _ => let* maybe_id := proj_state (fun env_ty => nth_error env_ty.(varMap) x) in
              match maybe_id with
              | Some id => mret (Evar id cty)
              | _ =>
                  modify_state (add_var cty) ;;
                  let^ id' := search_state (find_var x) in
                  Evar id' cty
              end
        end
    | Expr.Index ty e1 e2 =>
        let* cty := State_lift (CTranslateType ty) in
        let* ce1 := CTranslateExpr e1 in
        let^ ce2 := CTranslateExpr e2 in
        ArrayAccess ce1 ce2 cty
    | Expr.Member ty y x =>
        let* cty := State_lift (CTranslateType ty) in
        let* x' := CTranslateExpr x in
        let* env' := get_state in
        match t_of_e x with
        | Expr.TStruct is_header f =>
            match nth_error f y, lookup_composite (t_of_e x) env' with
            | Some t_member, Result.Ok comp =>
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
    : list Expr.e -> StateT ClightEnv (result string) (list Clight.expr) :=
    state_list_map CTranslateExpr.
  
  Definition CTranslateArgs
    : Expr.args -> StateT ClightEnv (result string) (list Clight.expr) :=
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
    : (result string) AST.ident :=
    let* comp:= lookup_composite (t_of_e arg) env in
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
    : StateT ClightEnv (result string) Clight.statement :=
    let* dst_t' := State_lift (CTranslateType dst_t) in
    let* dst' := search_state (find_var dst) in 
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
    | Expr.SetValidity valid =>
        let* env := get_state in
        let^ index := state_lift (ValidBitIndex arg env) in
        let member :=  Efield arg' index type_bool in
        Sassign member (if valid then Ctrue else Cfalse)
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
    : StateT ClightEnv (result string) Clight.statement :=
    let* dst' := search_state (find_var dst) in
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
           (dst : Clight.expr) : StateT ClightEnv (result string) Clight.statement :=
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

  Definition CTranslateArrayElemAssgn (t : type) (exps : list Expr.e) (dst : Clight.expr)
    : StateT ClightEnv (result string) Clight.statement :=
    state_list_mapi
      (fun i exp =>
         let^ exp := CTranslateExpr exp in
         Sassign (ArrayAccess dst (Cuint_of_Z (Z.of_nat i)) t) exp) exps
      >>| statement_of_list.
  
  Definition
    CTranslateStructAssgn (fields: list Expr.e)
    (composite: composite_definition) (dst : Clight.expr)
    : StateT ClightEnv (result string) Clight.statement :=
    match composite with 
    | Composite id su m a =>
        CTranslateFieldAssgn m fields dst
    end.

  Definition
    CTranslateHeaderAssgn (exps: list Expr.e)
    (composite: composite_definition)
    (dst : Clight.expr) (valid: Clight.expr)
    : StateT ClightEnv (result string) Clight.statement :=
    match composite with 
    | Composite id su (Member_plain valid_id valid_typ :: mtl) a =>
        let assignValid := Sassign (Efield dst valid_id valid_typ) valid in
        let^ assigns := CTranslateFieldAssgn mtl exps dst in
        Ssequence assignValid assigns
    |_ => state_lift (Result.error "Not a composite")
    end.
  
  Fixpoint getTableActionArgs (args: Clight.expr) (length: nat) : list (Clight.expr) :=
    match length with 
    | O => []
    | S l' => 
    getTableActionArgs args l' ++ 
    [(ArrayAccess args (Cint_of_Z (Z.of_nat length)) bit_vec)]
    end.

  Definition
    CTranslateTableInvoke
      (tbl : string)
    : StateT ClightEnv (result string) Clight.statement :=
    let* env := get_state in
    let* '(table_id, key, fn_names) :=
      state_lift (find_table tbl env) in 
    let* action_id :=
      State_lift (CCompEnv.add_temp_nameless action_ref) in
    (* TODO: are matchkinds important? *)
    let* elist := CTranslateExprList (List.map fst key) in
    let key_length := Z.of_nat (List.length key) in 
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
        (table_match_function (Z.of_nat (List.length key)))
        arg_list in
    let action_to_take_id := Efield (Evar action_id action_ref) _action int_signed in
    let action_to_take_args := Efield (Evar action_id action_ref) _arguments TpointerBitVec in
    let^ application :=
      state_fold_righti
        (ST := ClightEnv)
        (M := (result string))
        (A := Clight.statement)
        (B := string * Expr.args)
        (fun i '(f_name,args) st =>
           let* args := CTranslateArgs args in
           let^ '(f'_id, f') := state_lift (CCompEnv.lookup_function f_name env) in
           let index := Cint_of_Z (Z.of_nat i) in
             Sifthenelse
               (Ebinop Oeq action_to_take_id index type_bool)
               (let total_length := List.length (f'.(fn_params)) in
                let top_args := get_top_args  env in
                let top_length := List.length top_args in 
                let args_length := Nat.sub total_length top_length in
                let elist := getTableActionArgs action_to_take_args args_length in
                let elist := top_args ++ args ++ elist in 
                Scall None (Evar f'_id (Clight.type_of_function f')) elist) st)
        Sskip fn_names in
    Ssequence assignArray (Ssequence call application).
  
  Fixpoint fold_nat {A} (f: A -> nat -> A) (n : nat) (init:A) : A:=
    match n with
    | O => init
    | S n' => f (fold_nat f n' init) n' 
    end.
  
  Fixpoint CTranslateExtract
           (arg: Expr.e) (type : Expr.t) (name : string)
    : StateT ClightEnv (result string) Clight.statement :=
    let* env := get_state in
    let* extern_name :=
      state_lift
        (Result.from_opt
           (Env.find name env.(instanceMap))
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
    | Expr.TArray n t =>
        state_list_map
          (fun i => CTranslateExtract
                   (Expr.Index t arg (Expr.Bit n (Z.of_nat i)))
                   t name)
          (seq 0 (N.to_nat n))
          >>| statement_of_list
    | Expr.TStruct _ fs =>
        (* TODO: set the validity if header *)
        state_list_mapi
          (fun i ft =>
             CTranslateExtract (Expr.Member ft i arg) ft name) fs
          >>| statement_of_list
    | Expr.TVar _ => state_lift (Result.error "Can't extract to TVar")
    end.

  Fixpoint CTranslateEmit (arg: Expr.e) (type : Expr.t) (name : string)
    : StateT ClightEnv (result string) Clight.statement :=
    let* env := get_state in
    let* extern_name :=
      state_lift
        (Result.from_opt
           (Env.find name env.(instanceMap))
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
    | Expr.TArray n t =>
        state_list_map
          (fun i => CTranslateEmit
                   (Expr.Index t arg (Expr.Bit n (Z.of_nat i)))
                   t name)
          (seq 0 (N.to_nat n))
          >>| statement_of_list
    | Expr.TStruct _ fs =>
        (* TODO: check the validity and decide whether to emit *)
        state_list_mapi
          (fun i ft =>
             CTranslateEmit (Expr.Member ft i arg) ft name) fs
          >>| statement_of_list
    | Expr.TVar _ => state_lift (Result.error "Can't extract to TVar")
    end.

  Definition CTranslateCtrlParams
    : list Expr.t -> State ClightEnv (list (AST.ident * Ctypes.type)) :=
    state_list_map (M_Monad := identity_monad)
      (fun t =>
         let* new_id := new_ident in
         let* t := CTranslateType t in
         modify_state (M_Monad := identity_monad) (add_temp_arg t new_id) ;;
         state_return (M_Monad := identity_monad) (new_id, t)).
  
  Definition CTranslateParams
    : Expr.params -> State ClightEnv (list (AST.ident * Ctypes.type)) :=
    state_list_map
      (fun '(_,param) =>
         let* new_id := new_ident in
         let* '(ct, cparam) :=
           match param with
           | PAIn t =>
               let^ ct := CTranslateType t in (ct, ct)
           | PAOut t
           | PAInOut t =>
               let^ ct := CTranslateType t in (ct, Ctypes.Tpointer ct noattr)
           end in
         modify_state (add_temp_arg ct new_id) ;;
         mret (new_id, cparam)).
  
  Definition CTranslateExternParams (extern_params : list (string * string))
    : State ClightEnv (list (AST.ident * Ctypes.type)) :=
    modify_state clear_extern_instance_types ;;
    state_list_map (M_Monad := identity_monad)
      (fun '(name, extern_param_type) =>
         let* (new_id : ident) := new_ident in
         (* TODO: is this correct? *)
         modify_state
           (fun env =>
              add_extern_instance_type
                name extern_param_type
                (env <| instanceMap := Env.bind name new_id env.(instanceMap) |>)) ;;
         let ct := Ctypes.Tstruct $extern_param_type noattr in
         state_return (M_Monad := identity_monad) (new_id, ct))
      extern_params.
  
  Definition CCopyIn
    : Expr.params -> StateT ClightEnv (result string) Clight.statement :=
    (lift_monad statement_of_list)
      ∘ (state_list_mapi
           (fun (name : nat) '((_,fn_param): string * paramarg Expr.t Expr.t) =>
              let* '(oldid, tempid) := search_state (find_ident_temp_arg name) in
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
      StateT ClightEnv (result string) Clight.statement :=
    (lift_monad statement_of_list)
      ∘ (state_list_mapi
           (fun (name: nat) '((_,fn_param): string * paramarg Expr.t Expr.t) =>
              let* (oldid, tempid) := search_state (find_ident_temp_arg name) in
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
      StateT ClightEnv (result string) (list Clight.expr) :=
    state_list_mapi
      (fun (name: nat) '((_,fn_param): string * paramarg Expr.t Expr.t) =>
         let* (oldid, tempid) := search_state (find_ident_temp_arg name) in
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
      -> StateT ClightEnv (result string) (list Clight.expr) :=
    state_list_mapi
      (fun (name: nat) '((_,fn_param): string * paramarg Expr.t Expr.t) =>
         let* (oldid, tempid) := search_state (find_ident_temp_arg name) in
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
    : StateT ClightEnv (result string) (list Clight.expr) :=
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
    : StateT ClightEnv (result string) (Clight.statement * ident) :=
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
    : StateT ClightEnv (result string) (Clight.statement * ident) :=
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
    | Parser.Lists ps =>
        state_lift (Result.error "not a simple pattern match")
    end.

  Definition CTranslateParserExpressionVal (pe: Parser.pt)
    : StateT ClightEnv (result string) Clight.statement :=
    let* rec_call_args := proj_state get_top_args in
    match pe with
    | Parser.Direct st =>
        match st with
        | Parser.Start =>
            let^ (start_id, start_f) :=
              search_state (lookup_function "start") in
            Scall
              None (Evar start_id (Clight.type_of_function start_f))
              rec_call_args
        | Parser.Accept => state_return (Sreturn (Some Ctrue))
        | Parser.Reject => state_return (Sreturn (Some Cfalse))
        | Parser.Name x =>
            let* env := get_state in
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
  
  Definition CTranslateParserExpression (pe: Parser.pt)
    : StateT ClightEnv (result string) Clight.statement :=
    match pe with 
    | Parser.Select exp def cases => 
        let* input := CTranslateExpr exp in
        let* default_stmt := CTranslateParserExpressionVal (Parser.Direct def) in
        let fold_function
              '((p, action): Parser.pat * Parser.state_label) fail_stmt :=
          let* (match_statement, this_match) :=
            CTranslatePatternMatch input p in
          let^ success_statement :=
            CTranslateParserExpressionVal (Parser.Direct action) in
          Ssequence
            match_statement
            (Sifthenelse (Evar this_match type_bool) success_statement fail_stmt) in
        state_fold_right fold_function default_stmt cases
    | _ => CTranslateParserExpressionVal pe
    end.

  (** Translating top-level rhs expressions
      in variable declarations. *)
  Definition CTranslateRExpr (e : Expr.e)
    : StateT ClightEnv (result string) Clight.statement :=
    let t := t_of_e e in
    let* cty := State_lift (CTranslateType t) in
    modify_state (CCompEnv.add_var cty) ;;
    let* env := get_state in
    let* dst' := state_lift (find_var 0 env) in
    match e with
    | Expr.Bit width val =>
        let^ val_id := State_lift (find_BitVec_String val) in
        let w := Cint_of_Z (Z.of_N width) in
        let signed := Cfalse in 
        let val' := Evar val_id Cstring in
        let dst' := Eaddrof (Evar dst' bit_vec) TpointerBitVec in
        Scall None bitvec_init_function [dst'; signed; w; val']
    | Expr.Int width val =>
        let^ val_id := State_lift (find_BitVec_String val) in
        let w := Cint_of_Z (Zpos width) in
        let signed := Ctrue in 
        let val' := Evar val_id Cstring in
        let dst' := Eaddrof (Evar dst' bit_vec) TpointerBitVec in
        Scall None bitvec_init_function [dst'; signed; w; val']
    | Expr.Slice hi lo n =>
        let τ := t_of_e n in
        let* n' := CTranslateExpr n in
        let hi' := Cuint_of_Z (Zpos hi) in
        let lo' := Cuint_of_Z (Zpos lo) in
        let^ tau' := State_lift (CTranslateType τ) in
        let dst' := Evar dst' tau' in
        Scall None slice_function [n'; hi'; lo'; dst']
    | Expr.Cast τ e =>
        let* e' := CTranslateExpr e in
        let^ tau' := State_lift (CTranslateType τ) in
        let dst' := Evar dst' tau' in
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
        end
    | Expr.Uop dst_t op x =>
        CTranslateUop dst_t op x 0
    | Expr.Bop dst_t op x y =>
        CTranslateBop dst_t op x y 0
    | Expr.Lists Expr.lists_struct fields =>
        (*first create a temp of this struct.
          then assign all the values to it. then return this temp *)
        let strct := t_of_e e in
        let* typ := State_lift (CTranslateType strct) in
        let* composite := search_state (lookup_composite strct) in
        CTranslateStructAssgn
          fields composite (Evar dst' typ)
    | Expr.Lists (Expr.lists_header b) fields =>
        (*first create a temp of this header.
          then assign all the values to it. then return this temp*)
        let hdr := t_of_e e in
        let* typ := State_lift (CTranslateType hdr) in
        let valid := if b then Ctrue else Cfalse in
        let* composite := search_state (lookup_composite hdr) in
        CTranslateHeaderAssgn
          fields composite (Evar dst' typ) valid
    | Expr.Lists (Expr.lists_array t) es =>
        let* typ := State_lift (CTranslateType t) in
        CTranslateArrayElemAssgn typ es (Evar dst' typ)
    | _ =>
        let^ e' := CTranslateExpr e in
        Sassign (Evar dst' (typeof e')) e'
      end.
  
  Fixpoint CTranslateStatement (s: Stmt.s)
    : StateT ClightEnv (result string) Clight.statement :=
    match s with
    | Stmt.Skip => mret Sskip
    | Stmt.Seq s1 s2 =>
        (* TODO: need to correctly consider de bruijn stuff here *)
        let* s1' := CTranslateStatement s1 in
        let^ s2' := CTranslateStatement s2 in
        Ssequence s1' s2'
    | Stmt.Var _ (inl t) s =>
        (* TODO: why skip returned? *)
        let* cty := State_lift (CTranslateType t) in
        modify_state (CCompEnv.add_var cty) ;;
        CTranslateStatement s
    | Stmt.Var _ (inr e) s =>
        (* TODO: need to double check
           that I update env at the correct place. *)
      let t := t_of_e e in
      let* cty := State_lift (CTranslateType t) in
      modify_state (CCompEnv.add_var cty) ;;
      let* s1' := CTranslateRExpr e in
      let^ s2' := CTranslateStatement s in
      Ssequence s1' s2'
    | Stmt.Conditional e s1 s2 => 
        let* e' := CTranslateExpr e in
        let* s1' := CTranslateStatement s1 in
        let^ s2' := CTranslateStatement s2 in                 
        Sifthenelse e' s1' s2'
    | Stmt.Call (Stmt.Funct f _ None) args =>
        let* env := get_state in
        let* (id, f') := state_lift (CCompEnv.lookup_function f env) in
        let^ elist := CTranslateArgs args in
        Scall None (Evar id (Clight.type_of_function f')) elist
    | Stmt.Call (Stmt.Action f ctrl_args) data_args =>
        let* env := get_state in
        let* (id, f') := state_lift (CCompEnv.lookup_action_function f env) in
        let* ctrl_list := CTranslateExprList ctrl_args in
        let* data_list := CTranslateArgs data_args in
        let^ env' := get_state in 
        let elist := (get_top_args env') ++ ctrl_list ++ data_list in
        Scall None (Evar id (Clight.type_of_function f')) elist
    | Stmt.Call (Stmt.Funct f _ (Some e)) args =>
        let t := t_of_e e in
        let* ct := State_lift (CTranslateType t) in
        let* env_ct := get_state in
        let* (id, f') := state_lift (CCompEnv.lookup_function f env_ct) in
        let* elist := CTranslateArgs args in
        let* env' := get_state in
        let* tempid := State_lift (CCompEnv.add_temp_nameless ct) in
        let^ lvalue := CTranslateExpr e in 
        Ssequence
          (Scall (Some tempid) (Evar id (Clight.type_of_function f')) elist)
          (Sassign lvalue (Etempvar tempid ct))
    | Stmt.Call (Stmt.Method e f _ x) args =>
        let* env := get_state in
        let* t := state_lift (find_extern_type e env) in
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
        (* TODO: need to know context [apply block, function, etc.]. *)
        let* (id, f') := search_state (lookup_instance_function x) in
        let* elist := CTranslateArgs args in
        let* resultid := State_lift (CCompEnv.add_temp_nameless type_bool) in
        let result := (Etempvar resultid type_bool) in 
        let kompute :=
          Scall (Some resultid) (Evar id (Clight.type_of_function f')) elist in
        let judge := Sifthenelse (result) Sskip (Sreturn (Some Cfalse)) in
        mret (Ssequence kompute judge)
    | Stmt.Invoke tbl => CTranslateTableInvoke tbl
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
    : StateT ClightEnv (result string) Clight.function :=
    let* env := get_state in
    let* stmt := CTranslateStatement stmt in
    (*let rec_call_args := get_top_args  env' in*)
    modify_state (set_temp_vars env) ;;
    state_return
      (Clight.mkfunction
            Ctypes.type_bool
            (AST.mkcallconv None true true)
            params
            (CCompEnv.get_vars env)
            (CCompEnv.get_temps env)
            stmt).

  Definition CTranslateTopParser (parsr: TopDecl.d)
    (init: Clight.statement) (instance_name: string)
    : StateT ClightEnv (result string) unit :=
    match parsr with
    | TopDecl.Parser p _ _ eps params start states =>
        let* env := get_state in
        let* fn_eparams := State_lift (CTranslateExternParams eps) in
        let* fn_params := State_lift (CTranslateParams params) in
        let* copyin := CCopyIn params in
        let* copyout := CCopyOut params in
        (*copy in and copy out may need to copy cparams and eparams as well*)
        let* env_copyout := get_state in
        let* call_args := CFindTempArgsForSubCallsWithExtern params fn_eparams in
        let env_copyout := set_top_args call_args env_copyout in
        let fn_params := fn_eparams ++ fn_params in
        (*all functions inside one top parser declaration should have the same parameter*)
        let fn_sig :=
          (Clight.mkfunction 
             type_bool 
             (AST.mkcallconv None true true) 
             fn_params [] [] Sskip) in
        let env_start_fn_sig_declared := CCompEnv.add_function "start" fn_sig env_copyout in
        let env_fn_sig_declared :=
          List.fold_right
            (fun _ => add_parser_state fn_sig)
            env_start_fn_sig_declared states in
        put_state (set_temp_vars env env_fn_sig_declared) ;;
        state_fold_righti
          (fun (state_name: nat) (sb : Stmt.s) 'tt =>
             let* f := CTranslateParserState sb fn_params in
             modify_state (update_parser_state state_name f))
          tt states ;;
        (*finished declaring all the state blocks except start state*)
        let* f_start := CTranslateParserState start fn_params in
        let* env_start_translated := get_state in
        put_state
          (set_temp_vars
             env_copyout
             (CCompEnv.update_function "start" f_start env_start_translated)) ;;
        let* (env_start_declared  : ClightEnv) := get_state in
        let* (start_id, start_f) :=
          state_lift
            (lookup_function "start" env_start_declared) in
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
        let* instance_name :=
          state_lift
            (Result.from_opt
               (Env.find instance_name env.(instanceMap))
               "parser instance not found") in
        put_state
          (set_temp_vars
             env
             (env_start_declared
                <| fenv := Env.bind instance_name top_function env_start_declared.(fenv) |>))
    | _ => state_lift (Result.error "not parser")
    end.
  
  Definition
    CTranslateAction 
    (ctrl_params: list Expr.t)
    (signature: Expr.params) (body: Stmt.s)
    (top_fn_params: list (AST.ident * Ctypes.type))
    (top_signature: Expr.params)
    : StateT ClightEnv (result string) Clight.function :=
    let* ctrl_params :=
      State_lift (CTranslateCtrlParams ctrl_params) in
    let* env := get_state in
    let* fn_params := State_lift (CTranslateParams signature) in
    let fn_params := top_fn_params ++ ctrl_params ++ fn_params in 
    let full_signature := top_signature ++ signature in
    let* copyin := CCopyIn full_signature in
    let* copyout := CCopyOut full_signature in
    let* c_body := CTranslateStatement body in
    let* env_body_translated := get_state in
    put_state (set_temp_vars env env_body_translated) ;;
    let body := Ssequence copyin (Ssequence c_body copyout) in
    state_return
      (Clight.mkfunction 
         type_bool
         (AST.mkcallconv None true true)
         fn_params 
         (get_vars  env_body_translated)
         (get_temps  env_body_translated)
         body).
  
  Definition
    CTranslateControlLocalDeclaration
    (top_fn_params: list (AST.ident * Ctypes.type))
    (top_signature: Expr.params) (ct : Control.d)
    : StateT ClightEnv (result string) Clight.statement
    := match ct with
       | Control.Var _ (inl t) =>
           let* cty := State_lift (CTranslateType t) in
           modify_state (M:=(result string)) (CCompEnv.add_var cty) ;;
           state_return Sskip
       | Control.Var _ (inr e) =>
           let t := t_of_e e in
           let* cty := State_lift (M:=(result string)) (CTranslateType t) in
           modify_state (CCompEnv.add_var cty) ;;
           CTranslateRExpr e
       | Control.Action a ctrl_params data_params body =>
           let* f :=
             CTranslateAction
               (List.map snd ctrl_params) data_params
               body top_fn_params top_signature in
           (* TODO should be added to actions *)
           modify_state (CCompEnv.add_function a f) ;;
           state_return Sskip
       | Control.Table name keys acts =>
           modify_state (add_Table name keys acts) ;;
           let^ '(id, _, _) := search_state (find_table name) in
           let num_keys :=  Cint_of_Z (Z.of_nat (List.length keys)) in
           let size := Cint_of_Z 256%Z in
           let decl_stmt := Scall (Some id) bitvec_init_function [num_keys; size] in 
           decl_stmt
       end.

  Definition
    CTranslateControlLocalDeclarations
    (top_fn_params: list (AST.ident * Ctypes.type))
    (top_signature: Expr.params)
    : list Control.d -> StateT ClightEnv (result string) Clight.statement :=
    (lift_monad statement_of_list)
      ∘ (state_list_map
           (CTranslateControlLocalDeclaration
              top_fn_params top_signature)).
  
  Definition CTranslateTopControl (ctrl: TopDecl.d)
             (init: Clight.statement) (instance_name: string)
    : StateT ClightEnv (result string) unit :=
    match ctrl with
    | TopDecl.Control c _ _ eps params body blk =>
        let* env := get_state in
        let* fn_eparams := State_lift (CTranslateExternParams eps) in
        let* fn_params := State_lift (CTranslateParams params) in
        let* copyin := CCopyIn params in
        let* copyout := CCopyOut params in
        let* env_copyout := get_state in
        let* call_args := CFindTempArgsForSubCallsWithExtern params fn_eparams in
        let env_copyout := set_top_args call_args env_copyout in
        let fn_params := fn_eparams ++ fn_params in
        let* table_init :=
          CTranslateControlLocalDeclarations fn_params params body in
        let* apply_blk := CTranslateStatement blk in
        let* env_apply_block_translated := get_state in
        let body :=
          Ssequence
            init
            (Ssequence
               copyin
               (Ssequence
                  apply_blk
                  (Ssequence copyout (Sreturn (Some Ctrue))))) in
        let top_fn := 
          Clight.mkfunction 
            type_bool 
            (AST.mkcallconv None true true)
            fn_params 
            (get_vars env_apply_block_translated)
            (get_temps env_apply_block_translated)
            (Ssequence table_init body) in
        let env_top_fn_declared :=
          CCompEnv.add_function instance_name top_fn env_apply_block_translated in
        put_state (set_temp_vars env env_top_fn_declared)
    | _ => state_lift (Result.error "not a top control")
    end.
  
  Definition CTranslateFunction (funcdecl : TopDecl.d)
    : StateT ClightEnv (result string) unit :=
    match funcdecl with
    | TopDecl.Funct name _ signature body =>
        let* env := get_state in
        let* '(fn_params, fn_return) := State_lift (CTranslateArrow signature) in
        let* env_params_created := get_state in
        let paramargs := AST.paramargs signature in
        let* copyin := CCopyIn paramargs in
        let* copyout := CCopyOut paramargs in
        let* c_body := CTranslateStatement body in
        let body := Ssequence copyin (Ssequence c_body copyout) in
        let* env_body_translated := get_state in
        let top_function := 
          (Clight.mkfunction 
             fn_return
             (AST.mkcallconv None true true)
             fn_params 
             (get_vars env_body_translated)
             (get_temps env_body_translated)
             body) in
        put_state
          (set_temp_vars env (CCompEnv.add_function name top_function env_params_created))
    | _ => state_lift (Result.error "not a function")
    end.
  
  Definition InjectExprConstructorArg (arg: Expr.e)
    : StateT ClightEnv (result string) Clight.statement :=
    match arg with 
    | Expr.Bool b =>
        modify_state (add_var type_bool) ;;
        (* TODO: associate argument with ident *)
        let* val_id := State_lift new_ident in
        let initialize :=
          if b then
            Sassign (Evar val_id type_bool) Cfalse
          else
            Sassign (Evar val_id type_bool) Ctrue
        in state_return initialize
    | Expr.Bit width val =>
        modify_state (add_var bit_vec) ;;
        let* dst := State_lift new_ident in
        let* val_id := State_lift (find_BitVec_String val) in
        let w := Cint_of_Z (Z.of_N width) in
        let signed := Cfalse in 
        let val' := Evar val_id Cstring in
        let dst' := Eaddrof (Evar dst bit_vec) TpointerBitVec in
        state_return (Scall None bitvec_init_function [dst'; signed; w; val'])
    | Expr.Int width val => 
        modify_state (add_var bit_vec) ;;
        let* dst := State_lift new_ident in
        let* val_id := State_lift (find_BitVec_String val) in
        let w := Cint_of_Z (Zpos width) in
        let signed := Ctrue in
        let val' := Evar val_id Cstring in
        let dst' := Eaddrof (Evar dst bit_vec) TpointerBitVec in
        state_return (Scall None bitvec_init_function [dst'; signed; w; val'])
    | _ => state_lift (Result.error "not folded constant")
    end.

  Definition InjectExprConstructorArgs
    : list Expr.e -> StateT ClightEnv (result string) Clight.statement :=
    (lift_monad statement_of_list)
      ∘ (state_list_map InjectExprConstructorArg).

  Definition CCollectTypVar (d: TopDecl.d)
    : StateT ClightEnv (result string) unit :=
    match d with
    | TopDecl.Instantiate c x ts args expr_args =>
        if (String.eqb x "main") then
          State_lift (state_list_map CTranslateType ts) ;;
          match ts, args with 
          | [H; M], [p; vr; ig; eg; ck; dep] =>
              let* env := get_state in
              let* envM := state_lift (set_M M env) in
              let* envH := state_lift (set_H H envM) in
              put_state envH ;;
              modify_state (add_expected_v1_model_args "parser" p) ;;
              modify_state (add_expected_v1_model_args "verify" vr) ;;
              modify_state (add_expected_v1_model_args "ingress" ig) ;;
              modify_state (add_expected_v1_model_args "egress" eg) ;;
              modify_state (add_expected_v1_model_args "compute" ck) ;;
              modify_state (add_expected_v1_model_args "deparser" dep)
          | _,_ =>
              state_lift (Result.error "main instantiation not following V1model convention")
          end
        else state_return tt
    | _ => state_return tt
    end.

  Definition CCollectTypVar_prog : list TopDecl.d -> StateT ClightEnv (result string) unit :=
    state_fold_right (fun d _ => CCollectTypVar d) tt.
  
  Definition CTranslateTopDeclaration
    (d: TopDecl.d) : StateT ClightEnv (result string) unit :=
    match d with
    | TopDecl.Instantiate c x ts args expr_args => 
        modify_state (M:=(result string)) (add_tpdecl x d) ;;
        modify_state
          (M:=(result string))
          (if (String.eqb x "main") then
             set_instantiate_cargs args
           else fun env => env) ;;
        let* rtpdecl := proj_state (M:=(result string)) (lookup_topdecl c) in
        match rtpdecl with
        | Result.Ok (TopDecl.Parser _ _ _ _ _ _ _ as tpdecl) =>
            let* maybe_parser :=
              proj_state (M:=(result string))
                (fun env => Env.find "parser" env.(expected_v1_model_args)) in
            let x :=
              match maybe_parser with
              | None => x
              | Some name => if (String.eqb x name) then "parser" else x end in
            let* init := InjectExprConstructorArgs expr_args in
            CTranslateTopParser tpdecl init x
        | Result.Ok (TopDecl.Control _ _ _ _ _ _ _ as tpdecl) =>
            let* maybe_verify :=
              proj_state (M:=(result string))
                (Env.find "verify" ∘ expected_v1_model_args) in
            let* maybe_ingress :=
              proj_state (M:=(result string))
                (Env.find "ingress" ∘ expected_v1_model_args) in
            let* maybe_egress :=
              proj_state (M:=(result string))
                (Env.find "egress" ∘ expected_v1_model_args) in
            let* maybe_compute :=
              proj_state (M:=(result string))
                (Env.find "compute" ∘ expected_v1_model_args) in
            let* maybe_deparser :=
              proj_state (M:=(result string))
                (Env.find "deparser" ∘ expected_v1_model_args) in
            let x :=
              match maybe_verify, maybe_ingress,
                maybe_egress, maybe_compute, maybe_deparser with
              | Some vr, Some ig ,Some eg ,Some ck ,Some dep =>
                  if (String.eqb x vr) then "verify" else
                    if (String.eqb x ig) then "ingress" else
                      if (String.eqb x eg) then "egress" else
                        if (String.eqb x ck) then "compute" else
                          if (String.eqb x dep) then "deparser" else x
              | _,_,_,_,_ => x
              end in   
            let* init := InjectExprConstructorArgs expr_args in
            CTranslateTopControl tpdecl init x                       
        | _ => mret tt
        end
    | TopDecl.Funct _ _ _ _ => CTranslateFunction d
    | TopDecl.Extern e _ cparams expr_cparams methods => mret tt (*TODO: implement*)
    | TopDecl.Control name _ _ _ _ _ _ => modify_state (M:=(result string)) (add_tpdecl name d)
    (* CTranslateTopControl d env *)
    | TopDecl.Parser name _ _ _ _ _ _ => modify_state (M:=(result string)) (add_tpdecl name d)
                                               (* CTranslateTopParser d env *)
    end.

  Definition CTranslate_prog : list TopDecl.d -> StateT ClightEnv (result string) unit :=
    state_fold_right (fun d _ => CTranslateTopDeclaration d) tt.
  
  Fixpoint remove_composite (comps: list Ctypes.composite_definition) (name : ident) :=
    match comps with 
    | [] => comps
    | (Composite id su m a) :: tl => if (Pos.eqb id name) then 
                                        tl
                                     else (Composite id su m a) :: (remove_composite tl name)
    end.

  Definition Compile (prog: list TopDecl.d) : Errors.res (Clight.program*ident*ident) := 
    let init_env := CCompEnv.newClightEnv  in
    match CCollectTypVar_prog prog init_env with 
    | Result.Error m => Errors.Error (Errors.msg (m ++ "from collectTypVar"))
    | Result.Ok (_, init_env)  => 
    let main_id := $"dummy_main" in 
    match CTranslate_prog prog init_env with
    | Result.Error m => Errors.Error (Errors.msg (m ++ "from TopDeclaration"))
    | Result.Ok (_, env_all_declared) => 
      match CCompEnv.get_functions  env_all_declared with
      | Result.Error _ => Errors.Error (Errors.msg "can't find all the declared functions")
      | Result.Ok f_decls => 
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
