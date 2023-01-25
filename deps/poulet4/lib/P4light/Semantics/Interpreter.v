From Coq Require Import Strings.String
     NArith.NArith ZArith.ZArith.
From Poulet4 Require Import Utils.Utils
     P4light.Syntax.Syntax P4light.Syntax.Typed
     Utils.P4Arith P4light.Syntax.P4String
     P4light.Semantics.Semantics P4light.Semantics.Ops
     Monads.Option Utils.AListUtil.
From Equations Require Import Equations.
Import List.ListNotations.
Import ResultNotations.

Open Scope string_scope.

Inductive Fuel :=
| NoFuel
| MoreFuel (t: Fuel).

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
  Section WithGE.
    Variable (ge : genv).
    
    Definition last_index_of_next (next: N) : option Sval :=
      if (next =? 0)%N
      then uninit_sval_of_typ None (@TypBit tags_t 32)
      else Some (ValBaseBit (to_loptbool 32 (Z.of_N (next - 1)))).
    
    (* This function implements the get_member relation from the
     b ig-step semantics. *)
    Definition find_member (v: Sval) (member: string) : result Exn.t Sval :=
      match v with
      | ValBaseStruct fields
      | ValBaseUnion fields
      | ValBaseHeader fields _ =>
          from_opt (AList.get fields member)
                   (Exn.Other "find_member: member not in fields")
      | ValBaseStack headers next =>
          if string_dec member "size"
          then mret (ValBaseBit (to_loptbool 32%N (Zlength headers)))
          else if string_dec member "lastIndex"
               then from_opt (last_index_of_next next)
                             (Exn.Other "failure in last_index_of_next")
               else error (Exn.Other "find_member: member not a property of a stack")
      | _ => error (Exn.Other "find_member called on a bad value (not a struct, union, header, or stack")
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

    Definition val_to_string {bit: Type} (v: @ValueBase bit) : string :=
      match v with
      | ValBaseNull => "null"
      | ValBaseBool x => "bool"
      | ValBaseInteger x => "integer"
      | ValBaseBit value => "bit<>"
      | ValBaseInt value => "int<>"
      | ValBaseVarbit max value => "varbit<>"
      | ValBaseString x => "string"
      | ValBaseTuple x => "tuple"
      | ValBaseError x => "error"
      | ValBaseMatchKind x => "match_kind"
      | ValBaseStruct fields => "struct"
      | ValBaseHeader fields is_valid => "header"
      | ValBaseUnion fields => "union"
      | ValBaseStack headers next => "stack"
      | ValBaseEnumField typ_name enum_name => "enum field"
      | ValBaseSenumField typ_name value => "senum field"
      end.

    (* This function implements the update_member relation from the
     big-step semantics. *)
    Definition set_member (v: Sval) (fname: ident) (fv: Sval) : result Exn.t Sval :=
      match v with
      | ValBaseStruct fields =>
          let+ fields' :=
            from_opt (AList.set fields fname fv)
                     (Exn.Other ("set_member: unable to set struct field: " ++ fname))
          in
          ValBaseStruct fields'
      | ValBaseHeader fields is_valid =>
          from_opt (set_header_field fields is_valid fname fv)
                   (Exn.Other ("set_member: unable to set header field: " ++ fname))
      | ValBaseUnion fields =>
          match fv with
          | ValBaseHeader hfields is_valid0 =>
              let* fields' := from_opt (update_union_member fields fname hfields is_valid0)
              (Exn.Other ("set_member: unable to set union field " ++ fname))in
              mret (ValBaseUnion fields')
          | _ => error (Exn.Other "union value contains non-headers")
          end
      | _ => error (Exn.Other ("set_member "
                               ++ fname
                               ++ " called on value that is not struct-like: "
                               ++ val_to_string v))
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

    Fixpoint interp_expr (this: path) (st: state) (expr: @Expression tags_t) : result Exn.t Sval :=
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
              else from_opt (loc_to_sval_const ge this loc)
                            (Exn.Other "couldn't find loc in const env")
          | ExpArrayAccess array idx =>
              let* idxsv := interp_expr this st idx in
              let idxv := interp_sval_val idxsv in
              let* idxz := from_opt (array_access_idx_to_z idxv)
                                    (Exn.Other "failure in array_access_idx_to_z") in
              let* v := interp_expr this st array in
              match v with
              | ValBaseStack headers next =>
                  let* rtyp :=
                    from_opt (get_real_type ge typ)
                             (Exn.Other "failure in get_real_type")
                  in
                  let* default_header := from_opt (uninit_sval_of_typ None rtyp)
                                                  (Exn.Other "interp_expr: failure in uninit_sval_of_typ")
                  in
                  mret (Znth_default default_header idxz headers)
              | _ => error (Exn.Other "expected valbasestack in array access")
              end
          | ExpBitStringAccess bits lo hi =>
              let* bitssv := interp_expr this st bits in
              let* (bitsbl, wn) := from_opt (sval_to_bits_width bitssv)
                                            (Exn.Other "interp_expr: error in sval_to_bits_width") in
              let lonat := N.to_nat lo in
              let hinat := N.to_nat hi in
              if andb (Nat.leb lonat hinat) (Nat.ltb hinat wn)
              then mret (ValBaseBit (Ops.bitstring_slice bitsbl lonat hinat))
              else error (Exn.Other "bad bounds in slice expression")
          | ExpList es =>
              let* svs := sequence (List.map (interp_expr this st) es) in
              mret (ValBaseTuple svs)
          | ExpRecord entries =>
              let* entries_svs := asequence (AListUtil.map_values (interp_expr this st) entries) in
              let entries' := List.map (fun '(k, v) => (str k, v)) entries_svs in
              mret (ValBaseStruct entries')
          | ExpUnaryOp op arg =>
              let* argsv := interp_expr this st arg in
              let argv := interp_sval_val argsv in
              let* v := from_opt (Ops.eval_unary_op op argv)
                                 (Exn.Other "interp_expr: failure in eval_unary_op") in
              mret (eval_val_to_sval v)
          | ExpBinaryOp op larg rarg =>
              let* largsv := interp_expr this st larg in
              let* rargsv := interp_expr this st rarg in
              let largv := interp_sval_val largsv in
              let rargv := interp_sval_val rargsv in
              let* v := from_opt (Ops.eval_binary_op op largv rargv)
                                 (Exn.Other "interp_expr: failure in eval_binary_op") in
              mret (eval_val_to_sval v)
          | ExpCast newtyp expr =>
              let* oldsv := interp_expr this st expr in
              let oldv := interp_sval_val oldsv in
              let* real_typ :=
                from_opt (get_real_type ge newtyp)
                         (Exn.Other "failure in get_real_type")
              in
              let* newv := from_opt (Ops.eval_cast real_typ oldv)
                                    (Exn.Other "interp_expr: failure in eval_cast") in
              mret (eval_val_to_sval newv)
          | ExpTypeMember typ_name member =>
              let* typ := from_opt (IdentMap.get (str typ_name) (ge_typ ge))
                                   (Exn.Other "interp_expr: enum name in TypeMember not bound in ge_typ") in
              match typ with
              | TypEnum ename None members =>
                  if List.find (equivb member) members
                  then mret (ValBaseEnumField (str ename) (str member))
                  else error (Exn.Other "interp_expr: member in TypeMember not found in enum")
              | TypEnum ename (Some etyp) members =>
                  let* fields := from_opt (IdentMap.get (str ename) (ge_senum ge))
                                          (Exn.Other "interp_expr: serializable enum not in ge_senum environment") in
                  let* sv := from_opt (AList.get fields (str member))
                                      (Exn.Other "interp_expr: member in TypeMember not found in enum") in
                  mret (ValBaseSenumField (str ename) sv)
              | _ => error (Exn.Other "interp_expr: typ in TypeMember not an enum")
              end
          | ExpErrorMember err =>
              mret (ValBaseError (str err))
          | ExpExpressionMember expr member =>
              let* sv := interp_expr this st expr in
              find_member sv (str member)
          | ExpTernary cond tru fls =>
              let* sv := interp_expr this st cond in
              let v := interp_sval_val sv in
              match v with
              | ValBaseBool b =>
                  interp_expr this st (if b then tru else fls)
              | _ =>
                  error (Exn.Other "interp_expr: ternary condition evaluated to a non-bool value")
              end
          | ExpDontCare =>
              error (Exn.Other "interp_expr: attempting to evaluate a don't care exp?")
          | ExpFunctionCall func type_args args =>
              error (Exn.Other "function calls are not handled by interp_expr")
          | ExpNamelessInstantiation typ args =>
              error (Exn.Other "nameless instantiations are not handled by interp_expr")
          end
      end.

    Definition interp_expr_det (this: path) (st: state) (expr: @Expression tags_t) : result Exn.t Val :=
      interp_expr this st expr |=> interp_sval_val.

    Definition interp_exprs (this: path) (st: state) (exprs: list (@Expression tags_t)) : result Exn.t (list Val) :=
      let* svs := sequence (List.map (interp_expr this st) exprs) in
      mret (List.map interp_sval_val svs).

    Fixpoint interp_lexpr (this: path) (st: state) (expr: @Expression tags_t) : result Exn.t (Lval * signal) :=
      match expr with
      | MkExpression tag (ExpName _ loc) typ dir =>
          mret (ValLeftName loc, SContinue)
      | MkExpression tag (ExpExpressionMember expr name) typ dir =>
          let* (lv, sig) := interp_lexpr this st expr in
          if String.eqb (str name) "next"
          then let* v := interp_expr this st expr in
               match v with
               | ValBaseStack headers next =>
                   let ret_sig := if (next <? N.of_nat (List.length headers))%N
                                  then sig
                                  else SReject "StackOutOfBounds" in
                   mret (ValLeftArrayAccess lv (Z.of_N next), ret_sig)
               | _ => error (Exn.Other "in lvalue e.next, e is not a stack")
               end
          else mret (ValLeftMember lv (str name), sig)
      | MkExpression tag (ExpBitStringAccess bits lo hi) typ dir =>
          let* (lv, sig) := interp_lexpr this st bits in
          let* bitsv := interp_expr this st bits in
          let* (bitsbl, wn) := from_opt (sval_to_bits_width bitsv)
                                        (Exn.Other "error in sval_to_bits_width") in
          if ((lo <=? hi)%N && (hi <? N.of_nat wn)%N)%bool
          then mret (ValLeftBitAccess lv hi lo, sig)
          else error (Exn.Other "bad bounds on bit slice")
      | MkExpression tag (ExpArrayAccess array idx) typ dir =>
          let* (lv, sig) := interp_lexpr this st array in
          let* v := interp_expr_det this st array in
          let* size :=
            match v with
            | ValBaseStack headers next =>
              mret (List.length headers)
            | _ => error (Exn.Other "indexed value not a stack")
            end in
          let* idxv := interp_expr_det this st idx in
          let* idxz := from_opt (array_access_idx_to_z idxv)
                                (Exn.Other "error in array_access_idx_to_z") in
          mret (ValLeftArrayAccess lv idxz, sig)
      | _ => error (Exn.Other "expr not an lvalue")
      end.

    Fixpoint interp_read (st: state) (lv: Lval) : result Exn.t Sval :=
      match lv with
      |  ValLeftName loc => loc_to_sval loc st
      |  ValLeftMember lv fname =>
           let* sv := interp_read st lv in
           find_member sv fname
      |  ValLeftBitAccess lv hi lo =>
           let* bitssv := interp_read st lv in
           let* (bitsbl, wn) := from_opt (sval_to_bits_width bitssv)
                                         (Exn.Other "sval_to_bits_width") in
           let lonat := N.to_nat lo in
           let hinat := N.to_nat hi in
           if ((lonat <=? hinat)%nat && (hinat <? wn)%nat)%bool
           then mret (ValBaseBit (Ops.bitstring_slice bitsbl lonat hinat))
           else error (Exn.Other "interp_read")
      |  ValLeftArrayAccess lv idx =>
           let* v := interp_read st lv in
           match v with
           | ValBaseStack headers next =>
               let* default_header := from_opt (List.hd_error headers)
                                               (Exn.Other "interp_read: indexing into empty header stack") in
               let header := Znth_default default_header idx headers in
               mret header
           | _ => error (Exn.Other "interp_read")
           end
      end.

    Fixpoint interp_write (st: state) (lv: Lval) (rhs: Sval) : result Exn.t state :=
      match lv with
      |  ValLeftName loc =>
           mret (update_val_by_loc st loc rhs)
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
                   else error (Exn.Other "interp_write")
               | ValBaseInt bits =>
                   let bits'' := update_bitstring bits lonat hinat bits' in
                   if ((lonat <=? hinat)%nat && (hinat <? List.length bits)%nat)%bool
                   then interp_write st lv (ValBaseInt bits'')
                   else error (Exn.Other "interp_write")
               | _ => error (Exn.Other "interp_write")
               end
           | _ => error (Exn.Other "interp_write")
           end
      |  ValLeftArrayAccess lv idx =>
           let* sv := interp_read st lv in
           match sv with
           | ValBaseStack headers next =>
               let headers' := update_stack_header headers idx rhs in
               interp_write st lv (ValBaseStack headers' next)
           | _ =>
               error (Exn.Other "interp_write")
           end
      end.

    (* Corresponds to exec_write_option *)
    Definition interp_write_option (st: state) (lv: option Lval) (rhs: Sval) : result Exn.t state :=
      match lv with
      | Some lval => interp_write st lval rhs
      | None => mret st
      end.

    Definition is_call (expr: @Expression tags_t) : bool :=
      match expr with
      | MkExpression _ (ExpFunctionCall func targs args) _ _ => true
      | _ => false
      end.

  Definition interp_match (this: path) (m: @Match tags_t) : result Exn.t ValSet :=
    match m with
    | MkMatch _ MatchDontCare _ =>
      mret ValSetUniversal
    | MkMatch  _ (MatchMask expr mask) typ =>
      let* exprv := interp_expr_det this empty_state expr in
      let* maskv := interp_expr_det this empty_state mask in
      mret (ValSetMask exprv maskv)
    | MkMatch _ (MatchRange lo hi) _ =>
      let* lov := interp_expr_det this empty_state lo in
      let* hiv := interp_expr_det this empty_state hi in
      mret (ValSetRange lov hiv)
    | MkMatch _ (MatchCast newtyp expr) _ =>
      let* oldv := interp_expr_det this empty_state expr in
      let* real_typ := from_opt (get_real_type ge newtyp)
                                (Exn.Other "interp_match: failure in get_real_type") in
      from_opt (Ops.eval_cast_set real_typ oldv)
               (Exn.Other "interp_match: failure in eval_cast_set")
    end.

    Fixpoint interp_matches (this: path) (matches: list (@Match tags_t)) : result Exn.t (list ValSet) :=
      match matches with
      | nil => mret nil
      | m :: ms =>
          let* sv := interp_match this m in
          let+ svs := interp_matches this ms in
          sv :: svs
      end.

    Definition interp_table_entry (this: path) (entry: table_entry)
      : result Exn.t (@table_entry_valset tags_t (@Expression tags_t)) :=
      let 'mk_table_entry ms action := entry in
      let* svs := interp_matches this ms in
      if (List.length svs =? 1)%nat
      then mret (List.hd ValSetUniversal svs, action)
      else mret (ValSetProd svs, action).

    Fixpoint interp_table_entries (this: path) (entries: list table_entry)
      : result Exn.t (list (@table_entry_valset tags_t (@Expression tags_t))) :=
      match entries with
      | nil => mret nil 
      | te :: tes =>
          let* tev := interp_table_entry this te in
          let* tevs := interp_table_entries this tes in
          mret (tev :: tevs)
      end.

    Definition interp_table_match
               (this: path)
               (st: state)
               (name: ident)
               (keys: list (@TableKey tags_t))
               (const_entries: option (list (@table_entry tags_t (@Expression tags_t))))
      : result Exn.t (option (@action_ref (@Expression tags_t))) :=
      let entries := get_entries st (this ++ [name]) const_entries in
      let match_kinds := List.map table_key_matchkind keys in
      let* keyvals := interp_exprs this st (List.map table_key_key keys) in
      let* entryvs := interp_table_entries this entries in
      mret (extern_match (List.combine keyvals match_kinds) entryvs).

    Equations interp_isValid (sv: Sval) : result Exn.t bool :=
      { interp_isValid (ValBaseHeader fields valid_bit) :=
            mret (bit_init valid_bit);
        interp_isValid (ValBaseUnion fields) :=
            let* valids := interp_isValid_fields fields in
            mret (List.fold_left orb valids false);
        interp_isValid ValBaseNull :=
            error (Exn.Other "interp_isValid passed a ValBaseNull");
        interp_isValid _ :=
            error (Exn.Other "interp_isValid") }
    where interp_isValid_fields (fields: list (string * Sval)) : result Exn.t (list bool) :=
      { interp_isValid_fields (f :: rest) :=
            let* f_valid := interp_isValid (snd f) in
            let* rest_valid := interp_isValid_fields rest in
            mret (f_valid :: rest_valid);
        interp_isValid_fields nil :=
            mret nil }.

    Definition interp_builtin (this: path) (st: state) (lv: Lval) (name: ident) (args: list Sval) : result Exn.t (state * signal) :=
      if name =? "isValid"
      then let* sv := interp_read st lv in
           let* is_valid := interp_isValid sv in
           match args with
           | nil => mret (st, SReturn (ValBaseBool is_valid))
           | _ => error (Exn.Other "interp_builtin")
           end
      else if name =? "setValid"
           then let* sv := interp_read st lv in
                match sv with
                | ValBaseHeader fields is_valid =>
                    match args with
                    | nil => let* st' := interp_write st lv (ValBaseHeader fields (mret true)) in
                             mret (st', SReturn ValBaseNull)
                    | _ => error (Exn.Other "interp_builtin")
                    end
                | _ => error (Exn.Other "interp_builtin")
                end
           else if name =? "setInvalid"
                then let* sv := interp_read st lv in
                     match sv with
                     | ValBaseHeader fields is_valid =>
                         match args with
                         | nil => let* st' := interp_write st lv (ValBaseHeader fields (mret false)) in
                                  mret (st', SReturn ValBaseNull)
                         | _ => error (Exn.Other "interp_builtin")
                         end
                     | _ => error (Exn.Other "interp_builtin")
                     end
                else if name =? "push_front"
                     then let* sv := interp_read st lv in
                          match sv with
                          | ValBaseStack headers next =>
                              match args with
                              | [ValBaseInteger count] =>
                                  let* _ := if (0 <=? count)%Z then mret tt else error (Exn.Other "interp_builtin") in
                                  let* st' := interp_write st lv (push_front headers next count) in
                                  mret (st', SReturn ValBaseNull)
                              | _ => error (Exn.Other "interp_builtin")
                              end
                          | _ => error (Exn.Other "interp_builtin")
                          end
                     else if name =? "pop_front"
                          then let* sv := interp_read st lv in
                               match sv with
                               | ValBaseStack headers next =>
                                   match args with
                                   | [ValBaseInteger count] =>
                                       let* _ := if (0 <=? count)%Z then mret tt else error (Exn.Other "interp_builtin") in
                                       let* st' := interp_write st lv (pop_front headers next count) in
                                       mret (st', SReturn ValBaseNull)
                                   | _ => error (Exn.Other "interp_builtin")
                                   end
                               | _ => error (Exn.Other "interp_builtin")
                               end
                          else error (Exn.Other "interp_builtin").

    Definition interp_arg (this: path) (st: state) (exp: option (@Expression tags_t)) (dir: direction) : result Exn.t (argument * signal) :=
      match exp, dir with
      | Some expr, Typed.In =>
          let* v := interp_expr_det this st expr in
          let sv := eval_val_to_sval v in
          mret ((Some sv, None), SContinue)
      | None, Typed.Out =>
          mret ((None, None), SContinue)
      | Some expr, Typed.Out =>
          let* '(lv, sig) := interp_lexpr this st expr in
          mret ((None, Some lv), sig)
      | Some expr, Typed.InOut =>
          let* '(lv, sig) := interp_lexpr this st expr in
          let* sv := interp_read st lv in
          let v := interp_sval_val sv in
          let sv' := eval_val_to_sval v in
          mret ((Some sv', Some lv), sig)
      | None, Typed.In => error (Exn.Other "No argument passed for in parameter")
      | None, Typed.InOut => error (Exn.Other "No argument passed for inout parameter")
      | _, Directionless => error (Exn.Other "Directionless parameter passed to interp_arg?")
      end.

    Fixpoint interp_args (this: path) (st: state) (exps: list (option (@Expression tags_t))) (dirs: list direction) : result Exn.t (list argument * signal) :=
      match exps, dirs with
      | nil, nil =>
          mret (nil, SContinue)
      | exp :: exps, dir :: dirs =>
          let* (arg, sig) := interp_arg this st exp dir in
          let* (args, sig') := interp_args this st exps dirs in
          let ret_sig := if is_continue sig then sig' else sig in
          mret (arg :: args, ret_sig)
      | _, _ => error (Exn.Other "interp_args: length mismatch")
      end.

    Fixpoint interp_write_options (st: state) (args: list (option Lval)) (vals: list Sval) : result Exn.t state :=
      match args, vals with
      | nil, nil =>
          mret st
      | arg :: args, val :: vals =>
          let* st' := interp_write_option st arg val in
          interp_write_options st' args vals
      | _, _ => error (Exn.Other "interp_write_options")
      end.

    Definition interp_call_copy_out (args : list (option Lval * direction)) (vals : list Sval) (s: state) : result Exn.t state :=
      interp_write_options s (filter_out args) vals.

    Fixpoint expr_to_string {tags_t: Type} (e: @Expression tags_t) : string :=
      match e with
      | MkExpression _ (ExpName _ loc) _ _ =>
          Exn.loc_to_string loc
      | MkExpression _ (ExpExpressionMember expr name) _ _ =>
          expr_to_string expr ++ "." ++ str name
      | _ => "<expr>"
      end.

    Fixpoint interp_stmt (this: path) (st: state) (fuel: Fuel) (stmt: @Statement tags_t) : result Exn.t (state * signal) :=
      match fuel with
      | NoFuel => error (Exn.Other "interp_func: no fuel")
      | MoreFuel fuel =>
          match stmt with
          | MkStatement tags (StatAssignment lhs rhs) typ =>
              if is_call rhs
              then let* (st', sig_call) := interp_call this st fuel rhs in
                   let* (lv, sig_lhs) := interp_lexpr this st lhs in
                   if not_continue sig_lhs
                   then mret (st, sig_lhs)
                   else match sig_call with
                        | SReturn v =>
                            let sv := eval_val_to_sval v in
                            let* st'' := interp_write st' lv sv in
                            mret (st'', SContinue)
                        | _ =>
                            mret (st', sig_call)
                        end
              else let* v := interp_expr_det this st rhs in
                   let sv := eval_val_to_sval v in 
                   let* (lv, sig) := interp_lexpr this st lhs in
                   let* st' := interp_write st lv sv in
                   mret (if is_continue sig then st' else st, sig)
          | MkStatement tags (StatMethodCall func targs args) typ =>
              let* (st', sig) := interp_call this st fuel (MkExpression dummy_tags (ExpFunctionCall func targs args) TypVoid Directionless) in
              let sig' := force_continue_signal sig in
              mret (st', sig')
          | MkStatement tags (StatDirectApplication typ' func_typ args) typ =>
              let* (st', sig) := interp_call this st fuel
                                             (MkExpression
                                                dummy_tags
                                                (ExpFunctionCall
                                                   (direct_application_expression typ' func_typ)
                                                   nil args) TypVoid Directionless) in
              let sig' := force_continue_signal sig in
              mret (st', sig')
          | MkStatement tags (StatConditional cond tru (Some fls)) typ =>
              let* condsv := interp_expr this st cond in
              match interp_sval_val condsv with
              | ValBaseBool b =>
                  interp_stmt this st fuel (if b then tru else fls)
              | ValBaseNull =>
                  error (Exn.Other "interp_stmt conditional: expected bool, got null")
              | _ =>
                  error (Exn.Other "interp_stmt conditional: expected bool")
              end
          | MkStatement tags (StatConditional cond tru None) typ =>
              let* condsv := interp_expr this st cond in
              match interp_sval_val condsv with
              | ValBaseBool b =>
                  interp_stmt this st fuel (if b then tru else empty_statement)
              | ValBaseNull =>
                  error (Exn.Other "interp_stmt conditional: expected bool, got null")
              | _ =>
                  error (Exn.Other "interp_stmt conditional: expected bool")
              end
          | MkStatement tags (StatBlock block) typ =>
              interp_block this st fuel block
          | MkStatement tags StatExit typ =>
              mret (st, SExit)
          | MkStatement tags (StatReturn None) typ =>
              mret (st, SReturnNull)
          | MkStatement tags (StatReturn (Some e)) typ =>
              let* sv := interp_expr this st e in
              mret (st, SReturn (interp_sval_val sv))
          | MkStatement tags StatEmpty typ =>
              mret (st, SContinue)
          | MkStatement tags (StatSwitch expr cases) typ =>
              let* sv := interp_expr this st expr in
              match interp_sval_val sv with
              | ValBaseEnumField _ s =>
                  let block := match_switch_case s cases in
                  interp_block this st fuel block
              | ValBaseNull => error (Exn.Other "interp_stmt switch: expected enum, got null")
              | _ => error (Exn.Other "interp_stmt switch: expected enum")
              end
          | MkStatement tags (StatVariable typ' name (Some e) loc) typ =>
              if is_call e
              then let* (st', sig) := interp_call this st fuel e in
                   match sig with
                   | SReturn v =>
                       let sv := eval_val_to_sval v in
                       let* st'' := interp_write st' (ValLeftName loc) sv in
                       mret (st'', SContinue)
                   | _ => 
                       mret (st', sig)
                   end
              else let* v := interp_expr_det this st e in
                   let sv := eval_val_to_sval v in 
                   let* st' := interp_write st (ValLeftName loc) sv in
                   mret (st', SContinue)
          | MkStatement tags (StatVariable typ' name None loc) typ =>
              let* rtyp := from_opt (get_real_type ge typ')
                                    (Exn.Other "interp_stmt: error in get_real_type") in
              let* sv := from_opt (uninit_sval_of_typ (mret false) rtyp)
                                  (Exn.Other "uninit_sval_of_typ") in
              let* st' := interp_write st (ValLeftName loc) sv in
              mret (st', SContinue)
          | MkStatement tags (StatConstant typ' name e loc) typ =>
              mret (st, SContinue)
          | MkStatement _ (StatInstantiation _ _ _ _) _ =>
              error (Exn.Other "interp_stmt called on instantiation stmt")
          end
      end
    with interp_block
           (this: path)
           (st: state)
           (fuel: Fuel)
           (block: @Block tags_t) : result Exn.t (state * signal) :=
           match fuel with
           | NoFuel => error (Exn.Other "interp_block: no fuel")
           | MoreFuel fuel =>
               match block with
               | BlockEmpty tags => mret (st, SContinue)
               | BlockCons stmt rest =>
                   let* (st, sig) := interp_stmt this st fuel stmt in
                   let* (st', sig') :=
                     interp_block this st fuel (if is_continue sig then rest else empty_block)
                   in
                   mret (st', if is_continue sig then sig' else sig)
               end
           end 
    with interp_call
           (this: path)
           (st: state)
           (fuel: Fuel)
           (call: @Expression tags_t)
      : result Exn.t (@state tags_t target * signal) :=
           match fuel with
           | MoreFuel fuel =>
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
                            then mret (st, sig)
                            else if not_continue sig'
                                 then mret (st, sig')
                                 else interp_builtin this st lv (str fname) (extract_invals argvals)
                        | _, _ => error (Exn.Other "interp_call")
                        end
                   else let dirs := get_arg_directions func in
                        let* (argvals, sig) := interp_args this st args dirs in
                        let* (obj_path, fd) := from_opt (lookup_func ge this func)
                                                        (Exn.Other ("interp_stmt: lookup_func could not find "
                                                                      ++ Exn.path_to_string this
                                                                      ++ "."
                                                                      ++ expr_to_string func)) in
                        let s2 := if is_some obj_path then set_memory PathMap.empty st else st in
                        let* (s3, outvals, sig') := interp_func (force this obj_path) s2 fuel fd targs (extract_invals argvals) in
                        let s4 := if is_some obj_path then set_memory (get_memory st) s3 else s3 in
                        let* s5 := interp_call_copy_out (List.combine (List.map snd argvals) dirs) outvals s4 in
                        let (ret_s, ret_sig) := if is_continue sig then (s5, sig') else (st, sig) in
                        mret (ret_s, ret_sig)
               | _ => error (Exn.Other "interp_call")
               end
           | NoFuel => error (Exn.Other "interp_call: no fuel")
           end
    with interp_func (obj_path: path) (s: state) (fuel: Fuel) (fn: @fundef tags_t) (typ_args: list (@P4Type tags_t)) (args: list Sval) : result Exn.t (state * list Sval * signal) :=
           match fuel with
           | NoFuel => error (Exn.Other "interp_func: no fuel")
           | MoreFuel fuel =>
               match fn with
               | FInternal params body =>
                   match typ_args with
                   | nil =>
                       let s' := exec_func_copy_in params args s in
                       let* (s'', sig) := interp_block obj_path s' fuel body in
                       let sig' := force_return_signal sig in
                       let* args' := from_opt (exec_func_copy_out params s'')
                                              (Exn.Other "interp_func: error in exec_func_copy_out") in
                       mret (s'', args', sig')
                   | _ :: _ => error (Exn.Other "interp_func: type args")
                   end
               | FTable name keys actions (Some default_action) const_entries =>
                   match typ_args, args with
                   | nil, nil =>
                       let* action_ref := interp_table_match obj_path s name keys const_entries in
                       let* (action, retv) :=
                         match action_ref with
                         | Some (mk_action_ref action_name ctrl_args) =>
                             let* action := from_opt (add_ctrl_args (get_action actions action_name) ctrl_args)
                                                     (Exn.Other "interp_func: error in add_ctrl_args") in
                             let retv := SReturn (table_retv true "" (get_expr_func_name action)) in
                             mret (action, retv)
                         | None =>
                             let action := default_action in
                             let retv := SReturn (table_retv false "" (get_expr_func_name default_action)) in
                             mret (action, retv)
                         end
                       in
                       let* (s', call_sig) := interp_call obj_path s fuel action in
                       match call_sig with
                       | SReturn ValBaseNull => mret (s', nil, retv)
                       | _ => error (Exn.Other "interp_func: did not return null")
                       end
                   | _, _ => error (Exn.Other "interp_func: type args or args provided to a table call")
                   end
               | FTable name keys actions None const_entries =>
                   error (Exn.Other "interp_func: called table with no default action")
               | FExternal class_name name =>
                   let (m, es) := s in
                   let argvs := List.map interp_sval_val args in
                   let* (es', argvs', sig) := interp_extern ge es class_name name obj_path typ_args argvs in
                   let args' := List.map eval_val_to_sval argvs' in
                   mret ((m, es'), args', sig)
               end

           end.

    (* Analogue of exec_module *)
    Definition interp_module (fuel: Fuel) (this: path) (st: extern_state) (args: list Val)
      : result Exn.t (extern_state * list Val * signal) :=
      let* func_inst := from_opt (PathMap.get this (ge_inst ge))
                                 (Exn.Other "object not found in ge_inst") in
      let* func := from_opt (PathMap.get [func_inst.(iclass); "apply"] (ge_func ge))
                            (Exn.Other "apply method for module not found in ge_func") in
      let st' : state := (PathMap.empty, st) in
      let sargs := List.map eval_val_to_sval args in
      let* (st, rets, sig) := interp_func this st' fuel func [] sargs in 
      mret (snd st, List.map interp_sval_val rets, sig).
  End WithGE.

  Definition interp (fuel: Fuel) (prog: @program tags_t) (st: extern_state) (in_port: Z) (pkt: list bool) : result Exn.t (extern_state * Z * (list bool)) :=
    let* ge := gen_ge prog in
    let* type_args := get_main_type_args ge target_main_name in
    interp_prog type_args (interp_module ge fuel) st in_port pkt.

End Interpreter.
