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

End Interpreter.
