From Coq Require Import Strings.String
     NArith.NArith ZArith.ZArith.
From Poulet4 Require Import
     Utils.Utils
     P4light.Syntax.Syntax
     P4light.Syntax.Typed
     Utils.P4Arith
     P4light.Syntax.P4String
     P4light.Semantics.Semantics
     Monads.Option
     Utils.AListUtil
     ListUtil.
From Equations Require Import Equations.
Import List.ListNotations.

Open Scope string_scope.

Section Interpreter.
  Context {tags_t: Type} {inhabitant_tags_t : Inhabitant tags_t}.
  Notation Val := (@ValueBase bool).
  Notation Sval := (@ValueBase (option bool)).
  Notation ValSet := (@ValueSet tags_t).
  Notation Lval := ValueLvalue.

  Notation ident := string.
  Notation path := (list ident).
  Notation P4Int := (P4Int.t tags_t).

  Context {target : @Target tags_t (@Expression tags_t)}.
  Variable (ge : genv).

  Definition last_index_of_next (next: N) : option Sval :=
    if (next =? 0)%N
    then uninit_sval_of_typ None (@TypBit tags_t 32)
    else Some (ValBaseBit (to_loptbool 32 (Z.of_N (next - 1)))).

  (* This function implements the get_member relation from the
     big-step semantics. *)
  Definition find_member (v: Sval) (member: string) : option Sval :=
    match v with
    | ValBaseStruct fields
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

  Definition set_header_field (fields: AList.AList string Sval eq) (is_valid: option bool) (fname: string) (fv: Sval) : option Sval :=
    match is_valid with
    | Some true =>
      let* fields' := AList.set fields fname fv in
      Some (ValBaseHeader fields' (Some true))
    | Some false =>
      let* fields' := AList.set fields fname (uninit_sval_of_sval None fv) in
      Some (ValBaseHeader fields' (Some false))
    | None =>
      let* fields' := AList.set fields fname (uninit_sval_of_sval None fv) in
      Some (ValBaseHeader fields' None)
    end.

  (* This function implements the update_member relation from the
     big-step semantics. *)
  Definition set_member (v: Sval) (fname: ident) (fv: Sval) : option Sval :=
    match v with
    | ValBaseStruct fields =>
      let* fields' := AList.set fields fname fv in
      Some (ValBaseStruct fields')
    | ValBaseHeader fields is_valid =>
      set_header_field fields is_valid fname fv
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
    | ValBaseError e =>
      ValBaseError e
    | ValBaseMatchKind m =>
      ValBaseMatchKind m
    | ValBaseStruct fields =>
      ValBaseStruct (AListUtil.map_values interp_sval_val fields)
    | ValBaseHeader fields is_valid =>
      ValBaseHeader (AListUtil.map_values interp_sval_val fields) (bit_init is_valid)
    | ValBaseUnion fields =>
      ValBaseUnion (AListUtil.map_values interp_sval_val fields)
    | ValBaseStack headers next =>
      ValBaseStack (List.map interp_sval_val headers) next
    | ValBaseEnumField typ_name enum_name =>
      ValBaseEnumField typ_name enum_name
    | ValBaseSenumField typ_name value =>
      ValBaseSenumField typ_name (interp_sval_val value)
    end.

  Fixpoint interp_expr (this: path) (st: state) (expr: @Expression tags_t) : option Sval :=
    match expr with
      MkExpression tags expr typ dir =>
        match expr with
    | ExpBool b =>
      Some (ValBaseBool (Some b))
    | ExpInt i =>
      Some (eval_p4int_sval i)
    | ExpString s =>
      Some (ValBaseString (str s))
    | ExpName x loc =>
      if is_directional dir
      then loc_to_sval loc st
      else loc_to_sval_const ge this loc
    | ExpArrayAccess array idx =>
      let* idxsv := interp_expr this st idx in
      let idxv := interp_sval_val idxsv in
      let* idxz := array_access_idx_to_z idxv in
      let* arrayv := interp_expr this st array in
      match arrayv with
      | ValBaseStack headers next =>
        let* rtyp := get_real_type ge typ in
        let* default_header := uninit_sval_of_typ None rtyp in
        Some (Znth_default default_header idxz headers)
      | _ => None
      end : option _
    | ExpBitStringAccess bits lo hi =>
      let* bitssv := interp_expr this st bits in
      let* (bitsbl, wn) := sval_to_bits_width bitssv in
      let lonat := N.to_nat lo in
      let hinat := N.to_nat hi in
      if andb (Nat.leb lonat hinat) (Nat.ltb hinat wn)
      then Some (ValBaseBit (Ops.bitstring_slice bitsbl lonat hinat))
      else None
    | ExpList es =>
      let* svs := lift_option (List.map (interp_expr this st) es) in
      Some (ValBaseTuple svs)
    | ExpRecord entries =>
      let* entries_svs := lift_option_kv (AListUtil.map_values (interp_expr this st) entries) in
      let entries' := List.map (fun '(k, v) => (str k, v)) entries_svs in
      Some (ValBaseStruct entries')
    | ExpUnaryOp op arg =>
      let* argsv := interp_expr this st arg in
      let argv := interp_sval_val argsv in
      let* v := Ops.eval_unary_op op argv in
      interp_val_sval v
    | ExpBinaryOp op larg rarg =>
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
        Some (ValBaseSenumField (str ename) sv)
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

  Definition interp_expr_det (this: path) (st: state) (expr: @Expression tags_t) : option Val :=
    let* sv := interp_expr this st expr in
    Some (interp_sval_val sv).

  Definition interp_exprs (this: path) (st: state) (exprs: list (@Expression tags_t)) : option (list Val) :=
    let* svs := lift_option (List.map (interp_expr this st) exprs) in
    Some (List.map interp_sval_val svs).

  Fixpoint interp_lexpr (this: path) (st: state) (expr: @Expression tags_t) : option (Lval * signal) :=
    match expr with
    | MkExpression tag (ExpName _ loc) typ dir =>
      Some (ValLeftName loc, SContinue)
    | MkExpression tag (ExpExpressionMember expr name) typ dir =>
      let* (lv, sig) := interp_lexpr this st expr in
      if String.eqb (str name) "next"
      then let* v := interp_expr this st expr in
           match v with
           | ValBaseStack headers next =>
             let ret_sig := if (next <? N.of_nat (List.length headers))%N
                            then sig
                            else SReject "StackOutOfBounds" in
             Some (ValLeftArrayAccess lv (Z.of_N next), ret_sig)
           | _ => None
           end
      else Some (ValLeftMember lv (str name), sig)
    | MkExpression tag (ExpBitStringAccess bits lo hi) typ dir =>
      let* (lv, sig) := interp_lexpr this st bits in
      let* bitsv := interp_expr this st bits in
      let* (bitsbl, wn) := sval_to_bits_width bitsv in
      if ((lo <=? hi)%N && (hi <? N.of_nat wn)%N)%bool
      then Some (ValLeftBitAccess lv hi lo, sig)
      else None
    | MkExpression tag (ExpArrayAccess array idx) typ dir =>
      let* (lv, sig) := interp_lexpr this st array in
      let* v := interp_expr_det this st array in
      let* size :=
         match v with
         | ValBaseStack headers next =>
           Some (List.length headers)
         | _ => None
         end in
      let* idxv := interp_expr_det this st idx in
      let* idxz := array_access_idx_to_z idxv in
      Some (ValLeftArrayAccess lv idxz, sig)
    | _ => None
    end.

  Fixpoint interp_read (st: state) (lv: Lval) : option Sval :=
    match lv with
    | ValLeftName loc => loc_to_sval loc st
    | ValLeftMember lv fname =>
      let* sv := interp_read st lv in
      find_member sv fname
    | ValLeftBitAccess lv hi lo =>
      let* bitssv := interp_read st lv in
      let* (bitsbl, wn) := sval_to_bits_width bitssv in
      let lonat := N.to_nat lo in
      let hinat := N.to_nat hi in
      if ((lonat <=? hinat)%nat && (hinat <? wn)%nat)%bool
      then Some (ValBaseBit (Ops.bitstring_slice bitsbl lonat hinat))
      else None
    | ValLeftArrayAccess lv idx =>
      let* v := interp_read st lv in
      match v with
      | ValBaseStack headers next =>
        let* default_header := List.hd_error headers in
        let header := Znth_default default_header idx headers in
        Some header
      | _ => None
      end
    end.


  Fixpoint interp_write (st: state) (lv: Lval) (rhs: Sval) : option state :=
    match lv with
    |  ValLeftName loc =>
      Some (update_val_by_loc st loc rhs)
    |  ValLeftMember lv fname =>
      let* sv := interp_read st lv in
      let* sv' := set_member sv fname rhs in
      interp_write st lv sv'
    |  ValLeftBitAccess lv hi lo =>
      let* sv := interp_read st lv in
      let lonat := N.to_nat lo in
      let hinat := N.to_nat hi in
      match rhs with
      | ValBaseBit bits' =>
        match sv with
        | ValBaseBit bits =>
          let bits'' := update_bitstring bits lonat hinat bits' in
          if ((lonat <=? hinat)%nat && (hinat <? List.length bits)%nat)%bool
          then interp_write st lv (ValBaseBit bits'')
          else None
        | ValBaseInt bits =>
          let bits'' := update_bitstring bits lonat hinat bits' in
          if ((lonat <=? hinat)%nat && (hinat <? List.length bits)%nat)%bool
          then interp_write st lv (ValBaseInt bits'')
          else None
        | _ => None
        end
      | _ => None
      end
    |  ValLeftArrayAccess lv idx =>
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

  Definition interp_match (this: path) (m: @Match tags_t) : option ValSet :=
    match m with
    | MkMatch _ MatchDontCare _ =>
      Some ValSetUniversal
    | MkMatch  _ (MatchMask expr mask) typ =>
      let* exprv := interp_expr_det this empty_state expr in
      let* maskv := interp_expr_det this empty_state mask in
      Some (ValSetMask exprv maskv)
    | MkMatch _ (MatchRange lo hi) _ =>
      let* lov := interp_expr_det this empty_state lo in
      let* hiv := interp_expr_det this empty_state hi in
      Some (ValSetRange lov hiv)
    | MkMatch _ (MatchCast newtyp expr) _ =>
      let* oldv := interp_expr_det this empty_state expr in
      let* real_typ := get_real_type ge newtyp in
      Ops.eval_cast_set real_typ oldv
    end.

  Fixpoint interp_matches (this: path) (matches: list (@Match tags_t)) : option (list ValSet) :=
    match matches with
    | nil => Some nil
    | m :: ms =>
      let* sv := interp_match this m in
      let* svs := interp_matches this ms in
      Some (sv :: svs)
    end.

  Definition interp_table_entry (this: path) (entry: table_entry) : option (@table_entry_valset tags_t (@Expression tags_t)) :=
    let 'mk_table_entry ms action := entry in
    let* svs := interp_matches this ms in
    if (List.length svs =? 1)%nat
    then Some (List.hd ValSetUniversal svs, action)
    else Some (ValSetProd svs, action).

  Fixpoint interp_table_entries (this: path) (entries: list table_entry) : option (list (@table_entry_valset tags_t (@Expression tags_t))) :=
    match entries with
    | nil => Some nil 
    | te :: tes =>
      let* tev := interp_table_entry this te in
      let* tevs := interp_table_entries this tes in
      Some (tev :: tevs)
    end.

  Definition interp_table_match (this: path) (st: state) (name: ident) (keys: list (@TableKey tags_t)) (const_entries: option (list (@table_entry tags_t (@Expression tags_t)))) : option (option (@action_ref (@Expression tags_t))) :=
    let entries := get_entries st (this ++ [name]) const_entries in
    let match_kinds := List.map table_key_matchkind keys in
    let* keyvals := interp_exprs this st (List.map table_key_key keys) in
    let* entryvs := interp_table_entries this entries in
    Some (extern_match (List.combine keyvals match_kinds) entryvs).

  Equations interp_isValid (sv: Sval) : option bool :=
    { interp_isValid (ValBaseHeader fields valid_bit) :=
        Some (bit_init valid_bit);
      interp_isValid (ValBaseUnion fields) :=
        let* valid_bits := interp_isValid_fields fields in
        Some (List.fold_left orb valid_bits false);
      interp_isValid _ := None }
  where interp_isValid_fields (fields: list (string * Sval)) : option (list bool) :=
    { interp_isValid_fields (f :: rest) :=
         let* hd_valid := interp_isValid (snd f) in
         let* rest_valid := interp_isValid_fields rest in
         Some (hd_valid :: rest_valid);
      interp_isValid_fields nil := Some nil }.

  Definition interp_builtin (this: path) (st: state) (lv: Lval) (name: ident) (args: list Sval) : option (state * signal) :=
    if name =? "isValid"
    then let* sv := interp_read st lv in
         let* is_valid := interp_isValid sv in
         match args with
         | nil => Some (st, SReturn (ValBaseBool is_valid))
         | _ => None
         end
    else if name =? "setValid"
         then let* sv := interp_read st lv in
              match sv with
              | ValBaseHeader fields is_valid =>
                match args with
                | nil => let* st' := interp_write st lv (ValBaseHeader fields (Some true)) in
                        Some (st', SReturn ValBaseNull)
                | _ => None
                end
              | _ => None
              end
         else if name =? "setInvalid"
              then let* sv := interp_read st lv in
                   match sv with
                   | ValBaseHeader fields is_valid =>
                     match args with
                     | nil => let* st' := interp_write st lv (ValBaseHeader fields (Some false)) in
                             Some (st', SReturn ValBaseNull)
                     | _ => None
                     end
                   | _ => None
                   end
              else if name =? "push_front"
                   then let* sv := interp_read st lv in
                        match sv with
                        | ValBaseStack headers next =>
                          match args with
                          | [ValBaseInteger count] =>
                            let* _ := if (0 <=? count)%Z then Some tt else None in
                            let* st' := interp_write st lv (push_front headers next count) in
                            Some (st', SReturn ValBaseNull)
                          | _ => None
                          end
                        | _ => None
                        end
                   else if name =? "pop_front"
                        then let* sv := interp_read st lv in
                             match sv with
                             | ValBaseStack headers next =>
                               match args with
                               | [ValBaseInteger count] =>
                                 let* _ := if (0 <=? count)%Z then Some tt else None in
                                 let* st' := interp_write st lv (pop_front headers next count) in
                                 Some (st', SReturn ValBaseNull)
                               | _ => None
                               end
                             | _ => None
                             end
                        else None.

  Definition interp_arg (this: path) (st: state) (exp: option (@Expression tags_t)) (dir: direction) : option (argument * signal) :=
    match exp, dir with
    | Some expr, Typed.In =>
      let* v := interp_expr_det this st expr in
      let* sv := interp_val_sval v in
      Some ((Some sv, None), SContinue)
    | None, Out =>
      Some ((None, None), SContinue)
    | Some expr, Out =>
      let* (lv, sig) := interp_lexpr this st expr in
      Some ((None, Some lv), sig)
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
        else let* v := interp_expr_det this st rhs in
             let* sv := interp_val_sval v in 
             let* (lv, sig) := interp_lexpr this st lhs in
             let* st' := interp_write st lv sv in
             Some (if is_continue sig then st' else st, sig)
      | MkStatement tags (StatMethodCall func targs args) typ =>
        let* (st', sig) := interp_call this st fuel (MkExpression dummy_tags (ExpFunctionCall func targs args) TypVoid Directionless) in
        let sig' := force_continue_signal sig in
        Some (st', sig')
      | MkStatement tags (StatDirectApplication typ' func_typ args) typ =>
        let* (st', sig) := interp_call this st fuel
                (MkExpression
                   dummy_tags
                   (ExpFunctionCall
                      (direct_application_expression typ' func_typ)
                      nil args) TypVoid Directionless) in
        let sig' := force_continue_signal sig in
        Some (st', sig')
      | MkStatement tags (StatConditional cond tru (Some fls)) typ =>
        let* condsv := interp_expr this st cond in
        match interp_sval_val condsv with
        | ValBaseBool b =>
          interp_stmt this st fuel (if b then tru else fls)
        | _ => None
        end
      | MkStatement tags (StatConditional cond tru None) typ =>
        let* condsv := interp_expr this st cond in
        match interp_sval_val condsv with
        | ValBaseBool b =>
          interp_stmt this st fuel (if b then tru else empty_statement)
        | _ => None
        end
      | MkStatement tags (StatBlock block) typ =>
        interp_block this st fuel block
      | MkStatement tags StatExit typ =>
        Some (st, SExit)
      | MkStatement tags (StatReturn None) typ =>
        Some (st, SReturnNull)
      | MkStatement tags (StatReturn (Some e)) typ =>
        let* sv := interp_expr this st e in
        Some (st, SReturn (interp_sval_val sv))
      | MkStatement tags StatEmpty typ =>
        Some (st, SContinue)
      | MkStatement tags (StatSwitch expr cases) typ =>
        let* sv := interp_expr this st expr in
        match interp_sval_val sv with
        | ValBaseString s =>
          let block := match_switch_case s cases in
          interp_block this st fuel block
        | _ =>
          None
        end
      | MkStatement tags (StatVariable typ' name (Some e) loc) typ =>
        if is_call e
        then let* (st', sig) := interp_call this st fuel e in
             match sig with
             | SReturn v =>
               let* sv := interp_val_sval v in
               let* st'' := interp_write st' (ValLeftName loc) sv in
               Some (st'', SContinue)
             | _ => 
               Some (st', sig)
             end
        else let* v := interp_expr_det this st e in
             let* sv := interp_val_sval v in 
             let* st' := interp_write st (ValLeftName loc) sv in
             Some (st', SContinue)
      | MkStatement tags (StatVariable typ' name None loc) typ =>
        let* rtyp := get_real_type ge typ' in
        let* sv := uninit_sval_of_typ (Some false) rtyp in
        let* st' := interp_write st (ValLeftName loc) sv in
        Some (st', SContinue)
      | MkStatement tags (StatConstant typ' name e loc) typ =>
        Some (st, SContinue)
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
           | MkExpression _ (ExpFunctionCall func targs args) _ _ =>
             if is_builtin_func func
             then match func, targs with 
                  | MkExpression _ (ExpExpressionMember expr fname)
                                 (TypFunction (MkFunctionType tparams params FunBuiltin typ'))
                                 _,
                    nil =>
                    let dirs := List.map get_param_dir params in
                    let* (lv, sig) := interp_lexpr this st expr in
                    let* (argvals, sig') := interp_args this st args dirs in
                    if not_continue sig
                    then Some (st, sig)
                    else if not_continue sig'
                         then Some (st, sig')
                         else interp_builtin this st lv (str fname) (extract_invals argvals)
                                             
                  | _, _ => None
                  end
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
             match typ_args with
             | nil =>
               let s' := exec_func_copy_in params args s in
               let* (s'', sig) := interp_block obj_path s' fuel body in
               let sig' := force_return_signal sig in
               let* args' := exec_func_copy_out params s'' in
               Some (s'', args', sig')
             | _ :: _ => None
             end
           | FTable name keys actions (Some default_action) const_entries =>
             match typ_args, args with
             | nil, nil =>
               let* action_ref := interp_table_match obj_path s name keys const_entries in
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
             | _, _ => None
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
