Require Import Coq.Strings.String.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Poulet4.Syntax.
Require Import Poulet4.Typed.
Require Import Poulet4.P4Arith.
Require Import Poulet4.P4String.
Require Import Poulet4.Semantics.
Require Import Poulet4.Monads.Monad.
Require Import Poulet4.Monads.Option.

Section Interpreter.
  Context {tags_t: Type} {inhabitant_tags_t : Inhabitant tags_t}.
  Notation Val := (@ValueBase bool).
  Notation Sval := (@ValueBase (option bool)).
  Notation ValSet := (@ValueSet tags_t).
  Notation Lval := (@ValueLvalue tags_t).

  Notation ident := string.
  Notation path := (list ident).
  Notation P4Int := (P4Int.t tags_t).

  Context {target : @Target tags_t (@Expression tags_t)}.
  Variable (ge : genv).

  Definition last_index_of_next (next: N) : option Sval :=
    if (next =? 0)%N
    then uninit_sval_of_typ None (TypBit 32)
    else Some (ValBaseBit (to_loptbool 32 (Z.of_N (next - 1)))).

  (* This function implements the get_member relation from the
     big-step semantics. *)
  Definition find_member (v: Sval) (member: string) : option Sval :=
    match v with
    | ValBaseStruct fields
    | ValBaseRecord fields
    | ValBaseUnion fields
    | ValBaseHeader fields _ =>
      AList.get fields member
    | ValBaseStack headers next =>
      if string_dec member "size"
      then Some (ValBaseBit (to_loptbool 32%N (Zlength headers)))
      else if string_dec member "lastIndex"
           then last_index_of_next next
           else None
    | _ => None
    end.

  (* This function implements the update_member relation from the
     big-step semantics. *)
  Definition set_member (v: Sval) (fname: ident) (fv: Sval) : option Sval :=
    match v with
    | ValBaseStruct fields =>
      let* fields' := AList.set fields fname fv in
      Some (ValBaseStruct fields')
    | ValBaseHeader fields is_valid =>
      (* Not correct, need an implementation for write_header_field *)
      let* fields' := AList.set fields fname fv in
      Some (ValBaseHeader fields' is_valid)
    | ValBaseUnion fields =>
      match fv with
      | ValBaseHeader hfields is_valid0 =>
        let* fields' := update_union_member fields fname hfields is_valid0 in
        Some (ValBaseUnion fields')
      | _ => None
      end
    | _ => None
    end.

  Definition interp_val_sval (v: Val) : option Sval :=
    Some (eval_val_to_sval v).

  Definition bit_init (b: option bool) : bool :=
    match b with
    | Some b => b
    | None => false
    end.

  Definition bits_init : list (option bool) -> list bool :=
    List.map bit_init.

  (* Corresponds to exec_val from the big-step semantics. *)
  Fixpoint interp_sval_val (v: Sval) : Val :=
    match v with
    | ValBaseNull =>
      ValBaseNull
    | ValBaseBool b =>
      ValBaseBool (bit_init b)
    | ValBaseInteger i =>
      ValBaseInteger i
    | ValBaseBit bs =>
      ValBaseBit (bits_init bs)
    | ValBaseInt bs =>
      ValBaseInt (bits_init bs)
    | ValBaseVarbit max bs =>
      ValBaseVarbit max (bits_init bs)
    | ValBaseString s =>
      ValBaseString s
    | ValBaseTuple vs =>
      ValBaseTuple (List.map interp_sval_val vs)
    | ValBaseRecord fields =>
      ValBaseRecord (AList.map_values interp_sval_val fields)
    | ValBaseError e =>
      ValBaseError e
    | ValBaseMatchKind m =>
      ValBaseMatchKind m
    | ValBaseStruct fields =>
      ValBaseStruct (AList.map_values interp_sval_val fields)
    | ValBaseHeader fields is_valid =>
      ValBaseHeader (AList.map_values interp_sval_val fields) (bit_init is_valid)
    | ValBaseUnion fields =>
      ValBaseUnion (AList.map_values interp_sval_val fields)
    | ValBaseStack headers next =>
      ValBaseStack (List.map interp_sval_val headers) next
    | ValBaseEnumField typ_name enum_name =>
      ValBaseEnumField typ_name enum_name
    | ValBaseSenumField typ_name enum_name value =>
      ValBaseSenumField typ_name enum_name (interp_sval_val value)
    end.

  Fixpoint interp_expr (this: path) (st: state) (expr: @Expression tags_t) : option Sval :=
    match expr with
      MkExpression tags expr typ dir =>
        match expr with
    | ExpBool b =>
      mret (ValBaseBool (Some b))
    | ExpInt i =>
      mret (eval_p4int_sval i)
    | ExpString s =>
      mret (ValBaseString (str s))
    | ExpName x loc =>
      if is_directional dir
      then loc_to_sval loc st
      else loc_to_sval_const ge this loc
    | ExpArrayAccess array idx =>
      let* idxsv := interp_expr this st idx in
      let idxv := interp_sval_val idxsv in
      let* idxz := array_access_idx_to_z idxv in
      match interp_expr this st array with
      | Some (ValBaseStack headers next) =>
        let* rtyp := get_real_type ge typ in
        let* default_header := uninit_sval_of_typ None rtyp in
        Some (Znth_def idxz headers default_header)
      | _ => None
      end
    | ExpBitStringAccess bits lo hi =>
      let* bitssv := interp_expr this st bits in
      let* (bitsbl, wn) := sval_to_bits_width bitssv in
      let lonat := N.to_nat lo in
      let hinat := N.to_nat hi in
      if andb (Nat.leb lonat hinat) (Nat.ltb hinat wn)
      then Some (ValBaseBit (bitstring_slice bitsbl lonat hinat))
      else None
    | ExpList es =>
      let* svs := lift_option (List.map (interp_expr this st) es) in
      Some (ValBaseTuple svs)
    | ExpRecord entries =>
      let* entries_svs := lift_option_kv (AList.map_values (interp_expr this st) entries) in
      let entries' := List.map (fun '(k, v) => (str k, v)) entries_svs in
      Some (ValBaseRecord entries')
    | ExpUnaryOp op arg =>
      let* argsv := interp_expr this st arg in
      let argv := interp_sval_val argsv in
      let* v := Ops.eval_unary_op op argv in
      interp_val_sval v
    | ExpBinaryOp op (larg, rarg) =>
      let* largsv := interp_expr this st larg in
      let* rargsv := interp_expr this st rarg in
      let largv := interp_sval_val largsv in
      let rargv := interp_sval_val rargsv in
      let* v := Ops.eval_binary_op op largv rargv in
      interp_val_sval v
    | ExpCast newtyp expr =>
      let* oldsv := interp_expr this st expr in
      let oldv := interp_sval_val oldsv in
      let* real_typ := get_real_type ge newtyp in
      let* newv := Ops.eval_cast real_typ oldv in
      Some (eval_val_to_sval newv)
    | ExpTypeMember typ_name member =>
      let* typ := IdentMap.get (str typ_name) (ge_typ ge) in
      match typ with
      | TypEnum ename None members =>
        if List.find (equivb member) members
        then Some (ValBaseEnumField (str ename) (str member))
        else None
      | TypEnum ename (Some etyp) members =>
        let* fields := IdentMap.get (str ename) (ge_senum ge) in
        let* sv := AList.get fields (str member) in
        Some (ValBaseSenumField (str ename) (str member) sv)
      | _ => None
      end
    | ExpErrorMember err =>
      Some (ValBaseError (str err))
    | ExpExpressionMember expr member =>
      let* sv := interp_expr this st expr in
      let* sv' := find_member sv (str member) in
      Some sv'
    | ExpTernary cond tru fls =>
      let* sv := interp_expr this st cond in
      let v := interp_sval_val sv in
      match v with
      | ValBaseBool b =>
        interp_expr this st (if b then tru else fls)
      | _ =>
        None
      end
    | ExpDontCare =>
      Some ValBaseNull
    | ExpFunctionCall func type_args args =>
      None (* not implemented in exec_expr *)
    | ExpNamelessInstantiation typ args =>
      None (* not implemented in exec_expr *)
        end
    end.

  Fixpoint interp_lexpr (this: path) (st: state) (expr: @Expression tags_t) : option (Lval * signal) :=
    match expr with
    | MkExpression tag (ExpName name loc) typ dir =>
      Some (MkValueLvalue (ValLeftName name loc) typ, SContinue)
    | MkExpression tag (ExpExpressionMember expr name) typ dir =>
      let* (lv, sig) := interp_lexpr this st expr in
      if String.eqb (str name) "next"
      then let* v := interp_expr this st expr in
           match v with
           | ValBaseStack headers next =>
             let ret_sig := if (next <? N.of_nat (List.length headers))%N
                            then sig
                            else SReject "StackOutOfBounds" in
             Some (MkValueLvalue (ValLeftArrayAccess lv next) typ, ret_sig)
           | _ => None
           end
      else Some ((MkValueLvalue (ValLeftMember lv (str name)) typ), sig)
    | MkExpression tag (ExpBitStringAccess bits lo hi) typ dir =>
      let* (lv, sig) := interp_lexpr this st bits in
      let* bitsv := interp_expr this st bits in
      let* (bitsbl, wn) := sval_to_bits_width bitsv in
      if ((lo <=? hi)%N && (hi <? N.of_nat wn)%N)%bool
      then Some (MkValueLvalue (ValLeftBitAccess lv hi lo) typ, sig)
      else None
    | MkExpression tag (ExpArrayAccess array idx) typ dir =>
      let* (lv, sig) := interp_lexpr this st array in
      let* idxv := interp_expr this st idx in
      let* idxz := array_access_idx_to_z (interp_sval_val idxv) in
      let* idxn := if idxz >=? 0 then Some (Z.to_N idxz) else None in
      Some (MkValueLvalue (ValLeftArrayAccess lv idxn) typ, sig)
    | _ => None
    end.


  Fixpoint interp_read (st: state) (lv: Lval) : option Sval :=
    match lv with
    | MkValueLvalue (ValLeftName name loc) typ =>
      loc_to_sval loc st
    | MkValueLvalue (ValLeftMember lv fname) typ =>
      let* sv := interp_read st lv in
      find_member sv fname
    | MkValueLvalue (ValLeftBitAccess lv hi lo) typ =>
      let* bitssv := interp_read st lv in
      let* (bitsbl, wn) := sval_to_bits_width bitssv in
      let lonat := N.to_nat lo in
      let hinat := N.to_nat hi in
      if ((lonat <=? hinat)%nat && (hinat <? wn)%nat)%bool
      then Some (ValBaseBit (bitstring_slice bitsbl lonat hinat))
      else None
    | MkValueLvalue (ValLeftArrayAccess lv idx) typ =>
      let* v := interp_read st lv in
      match v with
      | ValBaseStack headers next =>
        let* rtyp := get_real_type ge typ in
        let* default_header := uninit_sval_of_typ None rtyp in
        let header := Znth_def (Z.of_N idx) headers default_header in
        Some header
      | _ => None
      end
    end.

  Fixpoint interp_write (st: state) (lv: Lval) (rhs: Sval) : option state :=
    match lv with
    | MkValueLvalue (ValLeftName name loc) typ =>
      Some (update_val_by_loc st loc rhs)
    | MkValueLvalue (ValLeftMember lv fname) typ =>
      let* sv := interp_read st lv in
      let* sv' := set_member sv fname rhs in
      interp_write st lv sv'
    | MkValueLvalue (ValLeftBitAccess lv hi lo) typ =>
      let* sv := interp_read st lv in
      let lonat := N.to_nat lo in
      let hinat := N.to_nat hi in
      match sv with
      | ValBaseBit bits =>
        let bits' := update_bitstring bits lonat hinat bits in
        if ((lonat <=? hinat)%nat && (hinat <? List.length bits)%nat)%bool
        then let sv' := ValBaseBit bits' in
             interp_write st lv sv'
        else None
      | ValBaseInt bits =>
        let bits' := update_bitstring bits lonat hinat bits in
        if ((lonat <=? hinat)%nat && (hinat <? List.length bits)%nat)%bool
        then let sv' := (ValBaseInt bits') in
             interp_write st lv sv'
        else None
      | _ => None
      end
    | MkValueLvalue (ValLeftArrayAccess lv idx) typ =>
      let* sv := interp_read st lv in
      match sv with
      | ValBaseStack headers next =>
        let headers' := update_stack_header headers idx rhs in
        interp_write st lv (ValBaseStack headers' next)
      | _ =>
        None
      end
    end.

  (* Corresponds to exec_write_option *)
  Definition interp_write_option (st: state) (lv: option Lval) (rhs: Sval) : option state :=
    match lv with
    | Some lval => interp_write st lval rhs
    | None => Some st
    end.

  Definition is_call (expr: @Expression tags_t) : bool :=
    match expr with
    | MkExpression _ (ExpFunctionCall func targs args) _ _ => true
    | _ => false
    end.

  Definition interp_table_match (this: path) (st: state) (name: ident) (entries: option (list (@table_entry tags_t (@Expression tags_t)))) : option (@action_ref (@Expression tags_t)).
  Admitted.

  Definition interp_extern:
    extern_env ->
    extern_state ->
    ident ->
    ident ->
    path ->
    list (@P4Type tags_t) ->
    list Val ->
    option (extern_state *
            list Val *
            signal).
  Admitted.

  Definition interp_builtin :
    path -> state -> Lval -> ident -> list Sval -> option (state * signal).
  Admitted.

  Fixpoint interp_arg (this: path) (st: state) (exp: option (@Expression tags_t)) (dir: direction) : option ((@argument tags_t) * signal) :=
    match exp, dir with
    | Some expr, In =>
      let* sv := interp_expr this st expr in
      Some ((Some sv, None), SContinue)
    | None, Out =>
      Some ((None, None), SContinue)
    | Some expr, Out =>
      let* (lv, sig) := interp_lexpr this st expr in
      let* sv' := interp_read st lv in
      Some ((Some sv', Some lv), sig)
    | Some expr, InOut =>
      let* (lv, sig) := interp_lexpr this st expr in
      let* sv := interp_read st lv in
      let v := interp_sval_val sv in
      let* sv' := interp_val_sval v in
      Some ((Some sv', Some lv), sig)
    | _, _ => None
    end.

  Fixpoint interp_args (this: path) (st: state) (exps: list (option (@Expression tags_t))) (dirs: list direction) : option (list argument * signal) :=
    match exps, dirs with
    | nil, nil =>
      Some (nil, SContinue)
    | exp :: exps, dir :: dirs =>
      let* (arg, sig) := interp_arg this st exp dir in
      let* (args, sig') := interp_args this st exps dirs in
      let ret_sig := if is_continue sig then sig' else sig in
      Some (arg :: args, ret_sig)
    | _, _ => None
    end.

  Fixpoint interp_write_options (st: state) (args: list (option Lval)) (vals: list Sval) : option state :=
    match args, vals with
    | nil, nil =>
      Some st
    | arg :: args, val :: vals =>
      let* st' := interp_write_option st arg val in
      interp_write_options st' args vals
    | _, _ => None
    end.

  Definition interp_call_copy_out (args : list (option Lval * direction)) (vals : list Sval) (s: state) : option state :=
    interp_write_options s (filter_out args) vals.

  Fixpoint interp_stmt (this: path) (st: state) (fuel: nat) (stmt: @Statement tags_t) : option (state * signal) :=
    match fuel with
    | O => None
    | S fuel =>
      match stmt with
      | MkStatement tags (StatAssignment lhs rhs) typ =>
        if is_call rhs
        then let* (st', sig_call) := interp_call this st fuel rhs in
             let* (lv, sig_lhs) := interp_lexpr this st lhs in
             if not_continue sig_lhs
             then Some (st, sig_lhs)
             else match sig_call with
                  | SReturn v =>
                    let* sv := interp_val_sval v in
                    let* st'' := interp_write st' lv sv in
                    Some (st'', SContinue)
                  | _ =>
                    Some (st', sig_call)
                  end
        else let* v := interp_expr this st rhs in
             let* (lv, sig) := interp_lexpr this st lhs in
             let* st' := interp_write st lv v in
             Some (if is_continue sig then st' else st, sig)
      | MkStatement tags (StatMethodCall func targs args) typ =>
        let* (st', sig) := interp_call this st fuel (MkExpression dummy_tags (ExpFunctionCall func targs args) TypVoid Directionless) in
        let sig' := force_continue_signal sig in
        Some (st', sig')
      | MkStatement tags (StatDirectApplication typ' args) typ =>
        None
      | MkStatement tags (StatConditional cond tru (Some fls)) typ =>
        None
      | MkStatement tags (StatConditional cond tru None) typ =>
        None
      | MkStatement tags (StatBlock block) typ =>
        interp_block this st fuel block
      | MkStatement tags StatExit typ =>
        None
      | MkStatement tags (StatReturn None) typ =>
        None
      | MkStatement tags (StatReturn (Some e)) typ =>
        None
      | MkStatement tags StatEmpty typ =>
        None
      | MkStatement tags (StatSwitch expr cases) typ =>
        None
      | MkStatement tags (StatVariable typ' name (Some e) loc) typ =>
        None
      | MkStatement tags (StatVariable typ' name None loc) typ =>
        None
      | MkStatement tags (StatConstant typ' name e loc) typ =>
        None
      | _ => None
      end
    end
  with interp_block (this: path) (st: state) (fuel: nat) (block: @Block tags_t) : option (state * signal) :=
         match fuel with
         | O => None
         | S fuel =>
           match block with
           | BlockEmpty tags => Some (st, SContinue)
           | BlockCons stmt rest =>
             let* (st, sig) := interp_stmt this st fuel stmt in
             let* (st', sig') :=
                interp_block this st fuel (if is_continue sig then rest else empty_block)
             in
             Some (st', if is_continue sig then sig' else sig)
           end
         end 
  with interp_call (this: path) (st: state) (fuel: nat) (call: @Expression tags_t) : option (state * signal) :=
         match fuel with
         | S fuel =>
           match call with 
           | MkExpression tags (ExpFunctionCall
                                  (MkExpression _
                                                (ExpExpressionMember expr fname)
                                                (TypFunction
                                                   (MkFunctionType tparams params FunBuiltin typ'))
                                                dir')
                                  nil args) typ dir =>
             let dirs := List.map get_param_dir params in
             let* (lv, sig) := interp_lexpr this st expr in
             let* (argvals, sig') := interp_args this st args dirs in
             if not_continue sig
             then Some (st, sig)
             else if not_continue sig'
                  then Some (st, sig')
                  else interp_builtin this st lv (str fname) (extract_invals argvals)
           | MkExpression tags (ExpFunctionCall func targs args) typ dir =>
             if is_builtin_func func
             then None
             else let dirs := get_arg_directions func in
                  let* (argvals, sig) := interp_args this st args dirs in
                  let* (obj_path, fd) := lookup_func ge this func in
                  let s2 := if is_some obj_path then set_memory PathMap.empty st else st in
                  let* (s3, outvals, sig') := interp_func (force this obj_path) s2 fuel fd targs (extract_invals argvals) in
                  let s4 := if is_some obj_path then set_memory (get_memory st) s3 else s3 in
                  let* s5 := interp_call_copy_out (List.combine (List.map snd argvals) dirs) outvals s4 in
                  let (ret_s, ret_sig) := if is_continue sig then (s5, sig') else (st, sig) in
                  Some (ret_s, ret_sig)
           | _ => None
           end
         | O => None
         end
  with interp_func (obj_path: path) (s: state) (fuel: nat) (fn: @fundef tags_t) (typ_args: list (@P4Type tags_t)) (args: list Sval) : option (state * list Sval * signal) :=
         match fuel with
         | S fuel =>
           match fn with
           | FInternal params body =>
             let s' := exec_func_copy_in params args s in
             let* (s'', sig) := interp_block obj_path s' fuel body in
             let sig' := force_return_signal sig in
             let* args' := exec_func_copy_out params s'' in
             Some (s'', args', sig')
           | FTable name keys actions (Some default_action) const_entries =>
             let action_ref := interp_table_match obj_path s name const_entries in
             let* (action, retv) :=
                match action_ref with
                | Some (mk_action_ref action_name ctrl_args) =>
                  let* action := add_ctrl_args (get_action actions action_name) ctrl_args in
                  let retv := SReturn (table_retv true "" (get_expr_func_name action)) in
                  Some (action, retv)
                | None =>
                  let action := default_action in
                  let retv := SReturn (table_retv false "" (get_expr_func_name default_action)) in
                  Some (action, retv)
                end
             in
             let* (s', call_sig) := interp_call obj_path s fuel action in
             match call_sig with
             | SReturn ValBaseNull => Some (s', nil, retv)
             | _ => None
             end
           | FTable name keys actions None const_entries =>
             None
           | FExternal class_name name =>
             let (m, es) := s in
             let argvs := List.map interp_sval_val args in
             let* (es', argvs', sig) := interp_extern ge es class_name name obj_path typ_args argvs in
             let* args' := lift_option (List.map interp_val_sval argvs') in
             Some ((m, es'), args', sig)
           end
         | O => None
         end.
  
End Interpreter.
