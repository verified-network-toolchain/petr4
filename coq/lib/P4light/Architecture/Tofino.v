(* Semantics for the Tofino target. *)
(* It is incomplete. Expand it to fit your needs. *)
Require Import Poulet4.Monads.ExportAll.
Require Import Strings.String.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Program.Program.
Require Import Poulet4.P4light.Syntax.Value.
Require Import Poulet4.P4light.Syntax.ValueUtil.
Require Import Poulet4.P4light.Syntax.Syntax.
Require Poulet4.P4light.Semantics.Extract.
From Poulet4.P4light.Syntax Require Import
     Typed P4Int SyntaxUtil P4Notations.
From Poulet4.P4light.Semantics Require Import Ops.
Require Import VST.zlist.Zlist
        Poulet4.P4light.Architecture.Target.
From Poulet4.Utils Require Import Maps CoqLib Utils P4Arith Hash.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Section Tofino.

Context {tags_t: Type} {inhabitant_tags_t : Inhabitant tags_t}.
Context {Expression: Type}.
Notation ident := string.
Notation path := (list ident).
Notation P4Type := (@P4Type tags_t).
Notation Val := (@ValueBase bool).
Notation ValSet := ValueSet.
Notation table_entry := (@table_entry Expression).
Notation action_ref := (@action_ref Expression).

Global Instance Inhabitant_Val : Inhabitant Val := ValBaseNull.

(* packet_in and packet_out. Most are placeholders. *)

Definition packet_in := list bool.

Definition packet_out := list bool.

(* Register *)

Definition register_static : Type := N (* index width *) * P4Type * Z (* size *).

Definition register := list Val.

Definition new_register (size : Z) (init_val : Val) : list Val :=
  Zrepeat init_val size.

(* Do not unfold initial values during instantiation! *)
#[global] Opaque new_register.

(* RegisterAction *)

Definition reg_action_static : Type := path (* register *).

(* CRCPolynomial *)

Record CRC_polynomial := mk_CRC_polynomial {
  CRCP_width : N;
  CRCP_coeff : list bool;
  CRCP_reversed : bool;
  CRCP_msb : bool;
  CRCP_extended : bool;
  CRCP_init : list bool;
  CRCP_xor : list bool
}.

(* Hash *)

Definition hash_static : Type := N (* width *) * CRC_polynomial.

Inductive object :=
  | ObjTable (entries : list table_entry)
  | ObjRegister (reg : register)
  | ObjPin (pin : packet_in)
  | ObjPout (pout : packet_out).

Definition extern_state := PathMap.t object.

Inductive env_object :=
  | EnvTable
  | EnvRegister (reg_sta : register_static)
  | EnvRegAction (ra_sta : reg_action_static)
  | EnvCRCPolynomial (crcp_sta : CRC_polynomial)
  | EnvHash (hash_sta : hash_static)
  | EnvAbsMet (abs_met_sem : extern_state -> list Val -> extern_state -> list Val -> signal -> Prop)
  | EnvPin
  | EnvPout.

Definition extern_env := PathMap.t env_object.

Definition dummy_tags := @default tags_t _.

Definition dummy_object : object.
Proof. exact (ObjPin []). Qed.

Definition dummy_env_object : env_object.
Proof. exact EnvPin. Qed.

Definition dummy_bool : bool.
Proof. exact false. Qed.

Definition dummy_CRC_polynomial : CRC_polynomial.
Proof. constructor; first [exact 0%N | exact [] | exact false]. Qed.

Definition construct_extern (e : extern_env) (s : extern_state) (class : ident) (targs : list P4Type) (p : path) (args : list (path + Val)) :=
  if String.eqb class "Register" then
    match targs, args with
    | [typ; TypBit iw], [inr (ValBaseBit bits); inr init_val] =>
        let (_, size) := BitArith.from_lbool bits in
        (PathMap.set p (EnvRegister (iw, typ, size)) e,
         PathMap.set p (ObjRegister (new_register size init_val)) s)
    | _, _ => (PathMap.set p dummy_env_object e, PathMap.set p dummy_object s) (* fail *)
    end

  else if String.eqb class "RegisterAction" then
    match targs, args with
    | [_; _; _], [inl reg] =>
        (PathMap.set p (EnvRegAction reg) e, s)
    | _, _ => (PathMap.set p dummy_env_object e, PathMap.set p dummy_object s) (* fail *)
    end

  (* CRCPolynomial and Hash also accept ints (already confirmed in Tofino)
     To implement this, need to save the output type in Hash. *)
  else if String.eqb class "CRCPolynomial" then
    match targs, args with
    | [TypBit w],
          [inr (ValBaseBit coeff);
           inr (ValBaseBool reversed);
           inr (ValBaseBool msb);
           inr (ValBaseBool extended);
           inr (ValBaseBit init);
           inr (ValBaseBit xor)
          ] =>
        if (N.eqb w (N.of_nat (List.length coeff))) &&
           (N.eqb w (N.of_nat (List.length init))) &&
           (N.eqb w (N.of_nat (List.length xor)))
        then
          (PathMap.set p (EnvCRCPolynomial
            (mk_CRC_polynomial w coeff reversed msb extended init xor)) e, s)
        else
          (PathMap.set p dummy_env_object e, PathMap.set p dummy_object s) (* fail *)
    | _, _ => (PathMap.set p dummy_env_object e, PathMap.set p dummy_object s) (* fail *)
    end

  else if String.eqb class "Hash" then
    match targs, args with
    (* This is not very good, because it means to destruct the strings all the way. *)
    | [TypBit w; TypBit pw], [inr (ValBaseEnumField "HashAlgorithm_t" "CUSTOM"); inl poly_path] =>
        let poly :=
          match PathMap.get poly_path e with
          | Some (EnvCRCPolynomial poly) =>
            if N.eqb (CRCP_width poly) pw
            then poly
            else dummy_CRC_polynomial (* fail *)
          | _ => dummy_CRC_polynomial (* fail *)
          end in
        (PathMap.set p (EnvHash (w, poly)) e, s)
    (* For other kinds of HashAlgorithm_t, we only need to fill in corresponding polynomials. *)
    | _, _ => (PathMap.set p dummy_env_object e, PathMap.set p dummy_object s) (* fail *)
    end

  else
    (PathMap.set p dummy_env_object e, PathMap.set p dummy_object s). (* fail *)

Definition extern_set_abstract_method (e : extern_env) (p : path) abs_met_sem :=
  PathMap.set p (EnvAbsMet abs_met_sem) e.

Definition extern_func_sem := extern_env -> extern_state -> path -> list P4Type -> list Val -> extern_state -> list Val -> signal -> Prop.

Inductive extern_func := mk_extern_func_sem {
  ef_class : ident;
  ef_func : ident;
  ef_sem : extern_func_sem
}.

Definition apply_extern_func_sem (func : extern_func) : extern_env -> extern_state -> ident -> ident -> path -> list P4Type -> list Val -> extern_state -> list Val -> signal -> Prop :=
  match func with
  | mk_extern_func_sem class_name func_name sem =>
      fun e s class_name' func_name' =>
          if String.eqb class_name class_name' && String.eqb func_name func_name' then
            sem e s
          else
            fun _ _ _ _ _ _ => False
  end.

Inductive register_read_sem : extern_func_sem :=
  | exec_register_read : forall e s p content typ size index_w indexb index output,
      PathMap.get p e = Some (EnvRegister (index_w, typ, size)) ->
      PathMap.get p s = Some (ObjRegister content) ->
      BitArith.from_lbool indexb = (index_w, index) ->
      (if ((-1 <? index) && (index <? size))
       then output = Znth index content
       else
        match uninit_sval_of_typ None typ with
        | Some output' => sval_to_val read_ndetbit output' output
        | None => False
        end) ->
      register_read_sem e s p nil [ValBaseBit indexb] s [] (SReturn output).

Definition register_read : extern_func := {|
  ef_class := "Register";
  ef_func := "read";
  ef_sem := register_read_sem
|}.

Inductive register_write_sem : extern_func_sem :=
  | exec_register_write : forall e s s' p content typ size index_w indexb index new_value,
      PathMap.get p e = Some (EnvRegister (index_w, typ, size)) ->
      PathMap.get p s = Some (ObjRegister content) ->
      BitArith.from_lbool indexb = (index_w, index) ->
      (if ((-1 <? index) && (index <? size))
       then (PathMap.set p (ObjRegister (upd_Znth index content new_value)) s) = s'
       else s = s') ->
      register_write_sem e s p nil [ValBaseBit indexb; new_value] s' [] SReturnNull.

Definition register_write : extern_func := {|
  ef_class := "Register";
  ef_func := "write";
  ef_sem := register_write_sem
|}.

Inductive regaction_execute_sem : extern_func_sem :=
  | exec_regaction_execute : forall e s p content typ size content' index_w indexb index reg apply_sem s' s'' old_value new_value retv,
      PathMap.get p e = Some (EnvRegAction reg) ->
      PathMap.get (p ++ ["apply"]) e = Some (EnvAbsMet apply_sem) ->
      PathMap.get reg e = Some (EnvRegister (index_w, typ, size)) ->
      PathMap.get reg s = Some (ObjRegister content) ->
      BitArith.from_lbool indexb = (index_w, index) ->
      (if ((-1 <? index) && (index <? size))
       then old_value = Znth index content
       else
        match uninit_sval_of_typ None typ with
        | Some old_value' => sval_to_val read_ndetbit old_value' old_value
        | None => False
        end) ->
      apply_sem s [old_value] s' [new_value; retv] SReturnNull ->
      (if ((-1 <? index) && (index <? size))
       then PathMap.get reg s' = Some (ObjRegister content')
            /\ s'' = PathMap.set reg (ObjRegister (upd_Znth index content' new_value)) s'
       else s'' = s /\ content = content') ->
      regaction_execute_sem e s p nil [ValBaseBit indexb] s'' [] (SReturn retv).

Definition regaction_execute : extern_func := {|
  ef_class := "RegisterAction";
  ef_func := "execute";
  ef_sem := regaction_execute_sem
|}.

Definition extract (typ: Typed.P4Type) (pkt: list bool) : option (Val * signal * list bool) :=
  let (res, pkt') := Extract.extract (tags_t:=tags_t) typ pkt in
  match res with
  | inl v =>
      Some (v, SReturnNull, pkt')
  | inr (Reject err) =>
      let* v := ValueUtil.zero_init_val_of_typ typ in
      Some (v, SReject (Packet.error_to_string err), pkt')
  | inr (TypeError s) =>
      None
  end.

Definition extract2 (typ: Typed.P4Type) (n: nat) (pkt: list bool) : option (Val * signal * list bool) :=
  let (res, pkt') := Extract.var_extract (tags_t:=tags_t) typ n pkt in
  match res with
  | inl v =>
      Some (v, SReturnNull, pkt')
  | inr (Reject err) =>
      let* v := ValueUtil.zero_init_val_of_typ typ in
      Some (v, SReject (Packet.error_to_string err), pkt')
  | inr (TypeError s) =>
      None
  end.

Inductive packet_in_extract_sem : extern_func_sem :=
| exec_packet_in_extract : forall e s p pin typ v sig pin',
      PathMap.get p s = Some (ObjPin pin) ->
      extract typ pin = Some (v, sig, pin') ->
      packet_in_extract_sem e s p [typ] []
            (PathMap.set p (ObjPin pin') s)
          [v] sig
 | exec_packet_in_extract2 : forall e s p pin typ len v sig pin',
      PathMap.get p s = Some (ObjPin pin) ->
      extract2 typ len pin = Some (v, sig, pin') ->
      packet_in_extract_sem e s p [typ] [ValBaseBit (to_lbool 32%N (Z.of_nat len))]
            (PathMap.set p (ObjPin pin') s)
          [v] sig.

Definition packet_in_extract : extern_func := {|
  ef_class := "packet_in";
  ef_func := "extract";
  ef_sem := packet_in_extract_sem
|}.

Definition emit (v : Val) : Packet (list bool) :=
  Extract.emit v;;
  get_state.

Inductive packet_out_emit_sem : extern_func_sem :=
  | exec_packet_out_emit : forall e s p pout typ v pout' x,
      PathMap.get p s = Some (ObjPout pout) ->
      emit v pout = (inl pout', x) ->
      packet_out_emit_sem e s p [typ] [v]
            (PathMap.set p (ObjPout pout') s)
          [] SReturnNull.

Definition packet_out_emit : extern_func := {|
  ef_class := "packet_out";
  ef_func := "emit";
  ef_sem := packet_out_emit_sem
|}.

Definition val_to_bits (v : Val) : option (list bool) :=
  match v with
  | ValBaseBool b => Some [b]
  | ValBaseBit value => Some value
  | ValBaseInt value => Some value
  | ValBaseVarbit _ value => Some value
  | _ => None
  end.

Definition concat_tuple (vs : list Val) : option (list bool) :=
  option_map (@concat bool) (lift_option (map val_to_bits vs)).

(* The following values are likely also accepted as arguments,
   need preprocessing to work:
     ValBaseStruct (tested)
     ValBaseHeader
     ValBaseUnion
     ValBaseStack
     ValBaseSenumField (tested) *)
Definition convert_to_bits (v: Val) : option (list bool) :=
  match v with
  | ValBaseBool _
  | ValBaseBit _
  | ValBaseInt _
  | ValBaseVarbit _ _ => val_to_bits v
  | ValBaseTuple values => concat_tuple values
  | _ => None
  end.

Definition repeat_concat_list {A} (num: nat) (l: list A) : list A :=
  let fix repeat_concat_list' num (l res: list A) :=
    match num with
    | O => res
    | S num' => repeat_concat_list' num' l (app l res)
    end in
  repeat_concat_list' num l [].

Definition extend_hash_output (hash_w: N) (output: list bool) : Val :=
  let output_w := N.of_nat (List.length output) in
  let num_copies := N.div hash_w output_w in
  let num_remainder := Z.of_N (N.modulo hash_w output_w) in
  let lsbs := repeat_concat_list (N.to_nat num_copies) output in
  let msbs := sublist (Z.of_N output_w - num_remainder) (Z.of_N output_w) output in
  ValBaseBit (app msbs lsbs).

Definition lbool_to_N (input: list bool) :=
  Z.to_N (snd (BitArith.from_lbool input)).

Inductive hash_get_sem : extern_func_sem :=
  | exec_hash_get_sem : forall e s p hash_w poly typs v input output,
    PathMap.get p e = Some (EnvHash (hash_w, poly)) ->
    convert_to_bits v = Some input ->
    extend_hash_output hash_w (compute_crc (N.to_nat (CRCP_width poly)) (lbool_to_N (CRCP_coeff poly))
      (lbool_to_N (CRCP_init poly)) (lbool_to_N (CRCP_xor poly))
      (CRCP_reversed poly) (CRCP_reversed poly) input) = output ->
    (* CRCP_msb, CRCP_extended: behavior waiting for response *)
    hash_get_sem e s p typs [v] s [] (SReturn output).

Definition hash_get : extern_func := {|
  ef_class := "Hash";
  ef_func := "get";
  ef_sem := hash_get_sem
|}.

(* This only works when tags_t is a unit type. *)

(* TODO (ef_class hash_get) and (ef_func hash_get) are redendant information here. See how to remove them. *)

Inductive exec_extern : extern_env -> extern_state -> ident (* class *) -> ident (* method *) -> path -> list P4Type -> list Val -> extern_state -> list Val -> signal -> Prop :=
  | exec_extern_register_read : forall e s p targs args s' args' vret,
      apply_extern_func_sem register_read e s (ef_class register_read) (ef_func register_read) p targs args s' args' vret ->
      exec_extern e s (ef_class register_read) (ef_func register_read) p targs args s' args' vret
  | exec_extern_register_write : forall e s p targs args s' args' vret,
      apply_extern_func_sem register_write e s (ef_class register_write) (ef_func register_write) p targs args s' args' vret ->
      exec_extern e s (ef_class register_write) (ef_func register_write) p targs args s' args' vret
  | exec_extern_regaction_execute : forall e s p targs args s' args' vret,
      apply_extern_func_sem regaction_execute e s (ef_class regaction_execute) (ef_func regaction_execute) p targs args s' args' vret ->
      exec_extern e s (ef_class regaction_execute) (ef_func regaction_execute) p targs args s' args' vret
  | exec_extern_hash_get : forall e s p targs args s' args' vret,
      apply_extern_func_sem hash_get e s (ef_class hash_get) (ef_func hash_get) p targs args s' args' vret ->
      exec_extern e s (ef_class hash_get) (ef_func hash_get) p targs args s' args' vret
  | exec_extern_packet_in_extract : forall e s p targs args s' args' vret,
      apply_extern_func_sem packet_in_extract e s (ef_class packet_in_extract) (ef_func packet_in_extract) p targs args s' args' vret ->
      exec_extern e s (ef_class packet_in_extract) (ef_func packet_in_extract) p targs args s' args' vret
  | exec_extern_packet_out_emit : forall e s p targs args s' args' vret,
      apply_extern_func_sem packet_out_emit e s (ef_class packet_out_emit) (ef_func packet_out_emit) p targs args s' args' vret ->
      exec_extern e s (ef_class packet_out_emit) (ef_func packet_out_emit) p targs args s' args' vret.

Inductive ValSetT :=
| VSTSingleton (value: Val)
| VSTUniversal
| VSTMask (value: Val) (mask: Val)
| VSTRange (lo: Val) (hi: Val)
| VSTProd (_: list ValSetT)
| VSTLpm (nbits: N) (value: Val)
| VSTValueSet (size: N) (members: list (list ValSetT)) (sets: list ValSetT).

Fixpoint valset_to_valsett (vs : ValSet) :=
  match vs with
  | ValSetSingleton n => VSTSingleton n
  | ValSetUniversal => VSTUniversal
  | ValSetMask value mask => VSTMask value mask
  | ValSetRange lo hi => VSTRange lo hi
  | ValSetProd sets => VSTProd (List.map valset_to_valsett sets)
  | ValSetLpm nbits value => VSTLpm nbits value
  | ValSetValueSet size members sets =>
      VSTValueSet
        size
        (List.map (List.map valset_to_valsett) members)
        (List.map valset_to_valsett sets)
  end.

Definition extern_get_entries (es : extern_state) (p : path) : list table_entry :=
  match PathMap.get p es with
  | Some (ObjTable entries) => entries
  | _ => nil
  end.

Definition extern_set_entries (es : extern_state) (p : path) (entries : list table_entry) : extern_state :=
  PathMap.set p (ObjTable entries) es.

Definition check_lpm_count (mks: list ident): option nat :=
  match findi (String.eqb "lpm") mks with
  | None => Some (List.length mks)
  | Some (index, _) =>
        let num_lpm := List.length (List.filter (String.eqb "lpm") mks) in
        if (1 <? num_lpm)%nat then None
        else Some index
  end.

Fixpoint assert_int (v: Val): option (N * Z * list bool) :=
  match v with
  | ValBaseBit bits => Some (BitArith.from_lbool bits, bits)
  | ValBaseInt bits => Some (IntArith.from_lbool bits, bits)
  | ValBaseSenumField _ val => assert_int val
  | _ => None
  end.

Fixpoint bits_to_lpm_nbits (acc: N) (b: bool) (v: list bool): option N :=
  match v with
  | [] => Some acc
  | true :: tl => bits_to_lpm_nbits (acc + 1) true tl
  | false :: tl => if b then None else bits_to_lpm_nbits acc b tl
  end.

(* Compute (bits_to_lpm_nbits 0 false (to_lbool 5 (-2))). *)
Definition lpm_rank(lpm_idx: nat) (vs: ValSetT): option N :=
  let lpm_rank' (vs: ValSetT) :=
    match vs with
    | VSTUniversal => Some 0%N
    | VSTLpm nbits _ =>  Some nbits
    | VSTSingleton v => Some (width_of_val v)
    | VSTMask v1 v2 =>
        match assert_int v2 with
        | None => None
        | Some (_, _, v2') => match bits_to_lpm_nbits 0 false v2' with
                              | None => None
                              | Some n => Some n
                              end
        end
    | _ => None
    end
  in match vs with
  | VSTProd l =>
      match nth_error l lpm_idx with
      | Some elem =>
          match lpm_rank' elem with
          | None => None
          | Some rank => Some rank
          end
      | _ => None
      end
  | _ =>
      lpm_rank' vs
  end.

Definition lpm_compare (va1 va2: ((ValSetT * action_ref) * N)): bool :=
  N.leb (snd va2) (snd va1).

Definition sort_lpm (l: list (ValSetT * action_ref)) (lpm_idx: nat): list (ValSetT * action_ref) :=
  let (vl, actL) := List.split l in
  match lift_option (List.map (lpm_rank lpm_idx) vl ) with
  | None => nil
  | Some rank =>
    let entries_rank := List.combine l rank in
    let sorted := mergeSort lpm_compare entries_rank in
    fst (List.split sorted)
  end.

Definition values_match_singleton (key: Val) (val: Val): bool :=
  match Ops.eval_binary_op_eq key val with
  | None => dummy_bool
  | Some b => b
  end.

Fixpoint vmm_help (bits0 bits1 bits2: list bool): bool :=
  match bits2, bits1, bits0 with
  | [], [], [] => true
  | false::tl2, _::tl1, _::tl0 => vmm_help tl0 tl1 tl2
  | true::tl2, hd1::tl1, hd0::tl0 =>
      andb (Bool.eqb hd0 hd1) (vmm_help tl0 tl1 tl2)
  (* should never hit *)
  | _, _, _ => dummy_bool
  end.

Definition values_match_mask (key: Val) (val mask: Val): bool :=
  match assert_int key, assert_int val, assert_int mask with
  | Some (w0, _, bits0), Some (w1, _, bits1), Some (w2, _, bits2) =>
    if negb ((w0 =? w1)%N && (w1 =? w2)%N) then dummy_bool
    else vmm_help bits0 bits1 bits2
  | _, _, _ => dummy_bool
  end.

Lemma values_match_mask_land: forall w key val mask ,
    values_match_mask
      (ValBaseBit (to_lbool w key))
      (ValBaseBit (to_lbool w val))
      (ValBaseBit (to_lbool w mask)) =
      (Z.land key (BitArith.mod_bound w mask) =?
       Z.land val (BitArith.mod_bound w mask)).
Proof.
  intros w key val mask. unfold values_match_mask. simpl.
  rewrite !Zlength_to_lbool, N.eqb_refl. simpl.

Abort.

(* Fixpoint vmm_help_z (v : Z) (bits1 bits2: list bool) :=
  match bits2, bits1 with
  | [], [] => true
  | false::tl2, _::tl1 => vmm_help_z (v / 2) tl1 tl2
  | true::tl2, hd1::tl1 =>
      andb (Bool.eqb (Z.odd v) hd1) (vmm_help_z (v / 2) tl1 tl2)
  | _, _ => dummy_bool
  end. *)

Definition lpm_nbits_to_mask (w1 w2 : N) : list bool :=
(Zrepeat false (Z.of_N (w1 - w2))) ++ (Zrepeat true (Z.of_N w2)).

Definition values_match_lpm (key: Val) (val: Val) (lpm_num_bits: N): bool :=
  match assert_int key, assert_int val with
  | Some (w0, _, bits0), Some (w1, _, bits1) =>
    if negb ((w0 =? w1)%N && (lpm_num_bits <=? w1)%N) then dummy_bool
    else let bits2 := lpm_nbits_to_mask w1 lpm_num_bits in
     vmm_help bits0 bits1 bits2
  | _, _ => dummy_bool
  end.

Definition values_match_range (key: Val) (lo hi: Val): bool :=
  match assert_int key, assert_int lo, assert_int hi with
  | Some (w0, z0, _), Some (w1, z1, _), Some (w2, z2, _) =>
      if negb ((w0 =? w1)%N && (w1 =? w2)%N) then dummy_bool
      else ((z1 <=? z0) && (z0 <=? z2))
  | _, _, _ => dummy_bool
  end.

Definition values_match_set (keys: list Val) (valset: ValSetT): bool :=
  let values_match_set'' (key_valset: Val * ValSetT) :=
    let (key, valset) := key_valset in
    match valset with
    | VSTSingleton v => values_match_singleton key v
    | VSTUniversal => true
    | VSTMask v1 v2 => values_match_mask key v1 v2
    | VSTRange lo hi => values_match_range key lo hi
    | VSTLpm w2 v1 => values_match_lpm key v1 w2
    | _ => dummy_bool
    end in
  let values_match_set' (keys: list Val) (valset: ValSetT) :=
    match valset with
    | VSTProd l =>
        if negb (List.length l =? List.length keys)%nat then dummy_bool
        else fold_andb (List.map values_match_set'' (List.combine keys l))
    | _ => values_match_set'' (List.hd ValBaseNull keys, valset)
    end in
  match valset with
  | VSTValueSet _ _ sets =>
      fold_orb (List.map (values_match_set' keys) sets)
  | _ => values_match_set' keys valset
  end.

Definition extern_matches (key: list (Val * ident)) (entries: list table_entry_valset) : list (bool * action_ref) :=
  let ks := List.map fst key in
  let mks := List.map snd key in
  match check_lpm_count mks with
  | None => []
  | Some lpm_idx =>
    let entries' := List.map (fun p => (valset_to_valsett (fst p), snd p)) entries in
    let entries'' :=
      if (lpm_idx <? List.length mks)%nat
      then sort_lpm entries' lpm_idx
      else entries' in
    List.map (fun s => (values_match_set ks (fst s), snd s)) entries''
  end.


Definition extern_match (key: list (Val * ident)) (entries: list table_entry_valset): option action_ref :=
  let match_res := List.filter fst (extern_matches key entries) in
  match match_res with
  | nil => None
  | sa :: _ => Some (snd sa)
  end.

Definition interp_extern : extern_env -> extern_state -> ident (* class *) -> ident (* method *) -> path -> list (P4Type) -> list Val -> Result.result Exn.t (extern_state * list Val * signal) :=
  (fun _ _ _ _ _ _ _ => Result.Error (Exn.Other "Tofino.interp_extern is not implemented")).

Definition interp_extern_safe :
  forall env st class method this targs args st' retvs sig,
    interp_extern env st class method this targs args = Result.Ok (st', retvs, sig) ->
    exec_extern env st class method this targs args st' retvs sig.
Proof.
  inversion 1.
Qed.

Instance TofinoExternSem : ExternSem := Build_ExternSem
  env_object
  object
  construct_extern
  extern_set_abstract_method
  exec_extern
  interp_extern
  interp_extern_safe
  extern_get_entries
  extern_set_entries
  extern_match.

Inductive exec_prog (type_args : list P4Type) : (path -> extern_state -> list Val -> extern_state -> list Val -> signal -> Prop) ->
    extern_state -> list bool -> extern_state -> list bool -> Prop :=
  | exec_prog_intro : forall (module_sem : _ -> _ -> _ -> _ -> _ -> _ -> Prop) s0 pin s7 pout s1 s2 s3 s4 s5 s6
                        hdr2 ig_md1 ig_intr_md1 ig_intr_md_for_tm1 ig_intr_md_from_prsr1
                        hdr3 ig_md2 ig_intr_md_for_dprsr2 ig_intr_md_for_tm2 ig_intr_md_for_dprsr1
                        hdr4 meta1 eg_md1 eg_intr_md1 eg_intr_md_from_prsr1
                        hdr5 eg_md2 eg_intr_md_for_dprsr2 eg_intr_md_for_oport2 eg_intr_md_for_dprsr eg_intr_md_for_oport1
                        hdr6,
      PathMap.set ["packet_in"] (ObjPin pin) s0 = s1 ->
      module_sem ["pipe"; "ingress_parser"] s1 [] s2 [hdr2; ig_md1; ig_intr_md1; ig_intr_md_for_tm1; ig_intr_md_from_prsr1] SReturnNull ->
      module_sem ["pipe"; "ingress"] s2 [hdr2; ig_md1; ig_intr_md1; ig_intr_md_from_prsr1; ig_intr_md_for_dprsr1; ig_intr_md_for_tm1]
                                     s3 [hdr3; ig_md2; ig_intr_md_for_dprsr2; ig_intr_md_for_tm2] SReturnNull ->
      module_sem ["pipe"; "ingress_deparser"] s3 [hdr3; meta1; ig_intr_md_for_dprsr2; ig_intr_md1] s4 [hdr4] SReturnNull ->
      module_sem ["pipe"; "egress_parser"] s4 [] s5 [hdr4; eg_md1; eg_intr_md1; eg_intr_md_from_prsr1] SReturnNull ->
      module_sem ["pipe"; "egress"] s5 [hdr4; eg_md1; eg_intr_md1; eg_intr_md_from_prsr1; eg_intr_md_for_dprsr; eg_intr_md_for_oport1]
                                    s6 [hdr5; eg_md2; eg_intr_md_for_dprsr2; eg_intr_md_for_oport2] SReturnNull ->
      module_sem ["pipe"; "egress_deparser"] s6 [hdr5; meta1; eg_intr_md_for_dprsr2; eg_intr_md1; eg_intr_md_from_prsr1] s7 [hdr6] SReturnNull ->
      PathMap.get ["packet_out"] s7 = Some (ObjPout pout) ->
      exec_prog type_args module_sem s0 pin s7 pout.

Definition interp_prog (type_args : list P4Type) : (path -> extern_state -> list Val -> Result.result Exn.t (extern_state * list Val * signal)) ->
                         extern_state -> Z -> list bool -> Result.result Exn.t (extern_state * Z * list bool) :=
  (fun _ _ _ _ => Result.Error (Exn.Other "Tofino.interp_prog is not implemented")).

Instance Tofino : Target := Build_Target _ "main" exec_prog interp_prog.

End Tofino.
