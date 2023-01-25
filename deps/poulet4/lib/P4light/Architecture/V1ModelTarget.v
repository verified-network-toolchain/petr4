Require Import Poulet4.Monads.ExportAll.
Require Import Strings.String.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Program.Program.
Require Import Poulet4.P4light.Syntax.Value.
Require Import Poulet4.P4light.Syntax.Syntax.
Require Poulet4.P4light.Semantics.Extract.
From Poulet4.P4light.Syntax Require Import
     Typed P4Int SyntaxUtil P4Notations ValueUtil.
From Poulet4.P4light.Semantics Require Import Ops.
Require Import VST.zlist.Zlist
        Poulet4.P4light.Architecture.Target.
From Poulet4.Utils Require Import Maps CoqLib Utils P4Arith Hash.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Section V1Model.

Context {tags_t: Type} (* {inhabitant_tags_t : Inhabitant tags_t} *).
Context {Expression: Type}.
Notation ident := string.
Notation path := (list ident).
Notation P4Type := (@P4Type tags_t).
Notation Val := (@ValueBase bool).
Notation ValSet := ValueSet.
Notation table_entry := (@table_entry tags_t Expression).
Notation action_ref := (@action_ref Expression).

Global Instance Inhabitant_Val : Inhabitant Val := ValBaseNull.

Definition register_static : Type := N (* width *) * Z (* size *).

Definition register := list Val.

Definition new_register (size : Z) (w : N) : list Val :=
  Zrepeat (ValBaseBit (to_lbool w 0)) size.

Definition packet_in := list bool.

Definition packet_out := list bool.

Inductive env_object :=
  | EnvTable
  | EnvRegister (reg_sta : register_static)
  | EnvPin
  | EnvPout.

Inductive object :=
  | ObjTable (entries : list table_entry)
  | ObjRegister (reg : register)
  | ObjPin (pin : packet_in)
  | ObjPout (pout : packet_out).

Definition extern_env := PathMap.t env_object.

Definition extern_state := PathMap.t object.

(* Definition dummy_tags := @default tags_t _. *)

Definition construct_extern (e : extern_env) (s : extern_state) (class : ident) (targs : list P4Type) (p : path) (args : list (path + Val)) :=
  if String.eqb class "register" then
    match args with
    (* | [ValBaseInteger size] *)
    | [inr (ValBaseBit bits)]
    (* | [ValBaseInt _ size] *) =>
        match targs with
        | [TypBit w] =>
            let (_, size) := BitArith.from_lbool bits in
            (PathMap.set p (EnvRegister (w, size)) e,
             PathMap.set p (ObjRegister (new_register size w)) s)
        | _ => (e, s) (* fail *)
        end
    | _ => (e, s) (* fail *)
    end
  else
    (e, s).

Definition extern_func_sem :=
  extern_env -> extern_state -> path -> list P4Type -> list Val -> extern_state -> list Val -> signal -> Prop.

Definition extern_func_interp :=
  extern_env -> extern_state -> path -> list P4Type -> list Val -> result Exn.t (extern_state * list Val * signal).

Inductive extern_func := mk_extern_func_sem {
  ef_class : ident;
  ef_func : ident;
  ef_sem : extern_func_sem;
  ef_interp : extern_func_interp
}.

Definition apply_extern_func_sem (func : extern_func) : extern_env -> extern_state -> ident -> ident -> path -> list P4Type -> list Val -> extern_state -> list Val -> signal -> Prop :=
  match func with
  | mk_extern_func_sem class_name func_name sem _ =>
      fun e s class_name' func_name' =>
          if String.eqb class_name class_name' && String.eqb func_name func_name' then
            sem e s
          else
            fun _ _ _ _ _ _ => False
  end.

Definition REG_INDEX_WIDTH := 32%N.

Inductive register_read_sem : extern_func_sem :=
  | exec_register_read : forall e s p content w size indexb index output,
      PathMap.get p e = Some (EnvRegister (w, size)) ->
      PathMap.get p s = Some (ObjRegister content) ->
      BitArith.from_lbool indexb = (REG_INDEX_WIDTH, index) ->
      (if ((-1 <? index) && (index <? size))
       then output = Znth index content
       else output = ValBaseBit (to_lbool w 0)) ->
      register_read_sem e s p nil [ValBaseBit indexb] s [output] SReturnNull.

Definition register_read : extern_func := {|
  ef_class := "register";
  ef_func := "read";
  ef_sem := register_read_sem;
  ef_interp := fun _ _ _ _ _ => error (Exn.Other "register_read unimplemented")
|}.

Inductive register_write_sem : extern_func_sem :=
  | exec_register_write : forall e s s' p content w size indexb index valueb,
      PathMap.get p e = Some (EnvRegister (w, size)) ->
      PathMap.get p s = Some (ObjRegister content) ->
      N.of_nat (List.length valueb) = w ->
      BitArith.from_lbool indexb = (REG_INDEX_WIDTH, index) ->
      (if ((-1 <? index) && (index <? size))
       then (PathMap.set p (ObjRegister (upd_Znth index content (ValBaseBit valueb))) s) = s'
       else s = s') ->
      register_write_sem e s p nil [ValBaseBit indexb; ValBaseBit valueb] s' [] SReturnNull.

Definition register_write : extern_func := {|
  ef_class := "register";
  ef_func := "write";
  ef_sem := register_write_sem;
  ef_interp := fun _ _ _ _ _ =>
                 error (Exn.Other "register_write unimplemented")
|}.

Definition extract (typ: Typed.P4Type) (pkt: list bool) : option (Val * signal * list bool) :=
  let (res, pkt') := Extract.extract (tags_t:=tags_t) typ pkt in
  match res with
  | inl v =>
      Some (v, SReturnNull, pkt')
  | inr (Reject err) =>
      Some (ValBaseNull, SReject (Packet.error_to_string err), pkt')
  | inr (TypeError s) =>
      None
  end.

Definition extract2 (typ: Typed.P4Type) (n: nat) (pkt: list bool) : option (Val * signal * list bool) :=
  let (res, pkt') := Extract.var_extract (tags_t:=tags_t) typ n pkt in
  match res with
  | inl v =>
      Some (v, SReturnNull, pkt')
  | inr (Reject err) =>
      Some (ValBaseNull, SReject (Packet.error_to_string err), pkt')
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

Definition packet_in_extract_interp : extern_func_interp :=
  fun env st this targs args =>
    let* typ :=
      match targs with
      | [typ] => mret typ
      | l => let n := List.length l in
             error (Exn.Other ("packet_in_extract_interp: wrong number (" ++ StringUtil.string_of_nat n ++ ") of type arguments"))
      end in
    let* pin_obj :=
      from_opt (PathMap.get this st)
               (Exn.LocNotFoundInState (LGlobal this)) in
    match pin_obj with
    | ObjPin pin =>
        let* (v, sig, pin') := from_opt (extract typ pin)
                                        (Exn.Other "failure in extract") in
        mret (PathMap.set this (ObjPin pin') st,
              [v],
              sig)
    | _ => error (Exn.Other ("packet_in_extract_interp: expected an ObjPin for packet_in at path " ++ Exn.path_to_string this))
    end.

Definition packet_in_extract : extern_func := {|
  ef_class := "packet_in";
  ef_func := "extract";
  ef_sem := packet_in_extract_sem;
  ef_interp := packet_in_extract_interp
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

Definition packet_out_emit_interp : extern_func_interp :=
  fun env st this targs args =>
    let* typ :=
      match targs with
      | [typ] => mret typ
      | _ => let n := List.length targs in
             error (Exn.Other ("packet_out_emit_interp: wrong number (" ++ StringUtil.string_of_nat n ++ ") of type arguments"))
      end in
    let* v :=
      match args with
      | [v] => mret v
      | _ => let n := List.length args in
             error (Exn.Other ("packet_out_emit_interp: wrong number (" ++ StringUtil.string_of_nat n ++ ") of arguments"))
      end in
    let* pout_obj :=
      from_opt (PathMap.get this st)
               (Exn.LocNotFoundInState (LGlobal this)) in
    match pout_obj with
    | ObjPout pout =>
        match emit v pout with
        | (inl pout', _) =>
            mret (PathMap.set this (ObjPout pout') st,
                   [],
                   SReturnNull)
        | _ => error (Exn.Other ("packet_out_emit_interp: failure in emit"))
        end
    | _ => error (Exn.Other ("packet_out_emit_interp: expected an ObjPout for packet_out at path " ++ Exn.path_to_string this))
    end.

Definition packet_out_emit : extern_func := {|
  ef_class := "packet_out";
  ef_func := "emit";
  ef_sem := packet_out_emit_sem;
  ef_interp := packet_out_emit_interp;
|}.

Local Open Scope hex_N_scope.

Definition get_hash_algorithm (algo : string) : option (nat * N * N * N * bool * bool ) :=
  if String.eqb algo "crc32" then
      Some (32%nat,
            0x04C11DB7,
            0xFFFFFFFF,
            0xFFFFFFFF,
            true, true)
  else if String.eqb algo "crc16" then
      Some (16%nat,
            0x8005,
            0,
            0,
            true, true)
       else None.

Local Close Scope hex_N_scope.

Definition val_to_bits (v : Val) : option (list bool) :=
  match v with
  | ValBaseBit value => Some value
  | ValBaseInt value => Some value
  | ValBaseVarbit _ value => Some value
  | _ => None
  end.

Definition concat_tuple (vs : list Val) : option (list bool) :=
  option_map (@concat bool) (lift_option (map val_to_bits vs)).

Definition bound_hash_output (outw: N) (base: list bool)
                             (max: list bool) (output: list bool) : Val :=
  let (w1, base) := BitArith.from_lbool base in
  let (w2, max) := BitArith.from_lbool max in
  let (w3, output) := BitArith.from_lbool output in
  let w4 := N.max (N.max w1 w2) w3 in
    ValBaseBit (to_lbool outw
                (BitArith.plus_mod w4 base
                (BitArith.modulo_mod w4 output max))).
(*Check compute_crc.*)
Inductive hash_sem : extern_func_sem :=
  | exec_hash : forall e s p outw typs hash_name base vs max hashw poly init xor_out refin refout input output,
      get_hash_algorithm hash_name = Some (hashw, poly, init, xor_out, refin, refout) ->
      concat_tuple vs = Some input ->
      bound_hash_output outw base max
        (compute_crc hashw poly init xor_out refin refout input) = output ->
      hash_sem e s p ((TypBit outw)::typs) [ValBaseEnumField "HashAlgorithm" hash_name;
                           ValBaseBit base;
                           ValBaseTuple vs;
                           ValBaseBit max]
        s [output] SReturnNull.

Definition hash : extern_func := {|
  ef_class := "";
  ef_func := "hash";
  ef_sem := hash_sem;
  ef_interp := fun _ _ _ _ _ => error (Exn.Other "hash unimplemented")
|}.

Definition extern_funcs : list extern_func := [
    register_read;
    register_write;
    packet_in_extract;
    packet_out_emit;
    hash
  ].

(* This only works when tags_t is a unit type. *)

Inductive exec_extern : extern_env -> extern_state -> ident (* class *) -> ident (* method *) -> path -> list P4Type -> list Val -> extern_state -> list Val -> signal -> Prop :=
  | exec_extern_register_read : forall e s p targs args s' args' vret,
      apply_extern_func_sem register_read e s (ef_class register_read) (ef_func register_read) p targs args s' args' vret ->
      exec_extern e s (ef_class register_read) (ef_func register_read) p targs args s' args' vret
  | exec_extern_register_write : forall e s p targs args s' args' vret,
      apply_extern_func_sem register_write e s (ef_class register_write) (ef_func register_write) p targs args s' args' vret ->
      exec_extern e s (ef_class register_write) (ef_func register_write) p targs args s' args' vret
  | exec_extern_packet_in_extract : forall e s p targs args s' args' vret,
      apply_extern_func_sem packet_in_extract e s (ef_class packet_in_extract) (ef_func packet_in_extract) p targs args s' args' vret ->
      exec_extern e s (ef_class packet_in_extract) (ef_func packet_in_extract) p targs args s' args' vret
  | exec_extern_packet_out_emit : forall e s p targs args s' args' vret,
      apply_extern_func_sem packet_out_emit e s (ef_class packet_out_emit) (ef_func packet_out_emit) p targs args s' args' vret ->
      exec_extern e s (ef_class packet_out_emit) (ef_func packet_out_emit) p targs args s' args' vret
  | exec_extern_hash : forall e s p targs args s' args' vret,
      apply_extern_func_sem hash e s (ef_class hash) (ef_func hash) p targs args s' args' vret ->
      exec_extern e s (ef_class hash) (ef_func hash) p targs args s' args' vret.

Inductive ValSetT :=
| VSTSingleton (value: Val)
| VSTUniversal
| VSTMask (value: Val) (mask: Val)
| VSTRange (lo: Val) (hi: Val)
| VSTProd (_: list ValSetT)
| VSTLpm (nbits: N) (value: Val)
| VSTValueSet (size: N) (members: list (list (@Match tags_t))) (sets: list ValSetT).

Fixpoint valset_to_valsett (vs : ValSet) :=
  match vs with
  | ValSetSingleton n => VSTSingleton n
  | ValSetUniversal => VSTUniversal
  | ValSetMask value mask => VSTMask value mask
  | ValSetRange lo hi => VSTMask lo hi
  | ValSetProd sets => VSTProd (List.map valset_to_valsett sets)
  | ValSetLpm nbits value => VSTLpm nbits value
  | ValSetValueSet size members sets => VSTValueSet size members (List.map valset_to_valsett sets)
  end.

Definition extern_get_entries (es : extern_state) (p : path) : list table_entry :=
  match PathMap.get p es with
  | Some (ObjTable entries) => entries
  | _ => nil
  end.

Definition extern_set_entries (es : extern_state) (p : path) (entries : list table_entry) : extern_state :=
  PathMap.set p (ObjTable entries) es.

Definition check_lpm_count (mks: list ident): option bool :=
  let num_lpm := List.length (List.filter (String.eqb "lpm") mks) in
  if (1 <? num_lpm)%nat
  then None
  else Some (num_lpm =? 1)%nat.

Fixpoint assert_bit (v: Val): option (list bool) :=
  match v with
  | ValBaseBit bits => Some bits
  | ValBaseSenumField _ val => assert_bit val
  | _ => None
  end.

Fixpoint bits_to_lpm_nbits (acc: N) (b: bool) (v: list bool): option N :=
  match v with
  | [] => Some acc
  | true :: tl => bits_to_lpm_nbits (acc + 1) true tl
  | false :: tl => if b then None else bits_to_lpm_nbits acc b tl
  end.

(* Compute (bits_to_lpm_nbits 0 false (to_lbool 5 (-2))). *)

Fixpoint lpm_set_of_set (vs: ValSetT): option ValSetT :=
  match vs with
  | VSTUniversal
  | VSTLpm _ _ => Some vs
  | VSTProd l => match lift_option (List.map lpm_set_of_set l) with
                  | Some l' => Some (VSTProd l')
                  | None => None
                  end
  | VSTSingleton v => Some (VSTLpm (width_of_val v) v)
  | VSTMask v1 v2 =>
    match assert_bit v2 with
    | None => None
    | Some v2' => match bits_to_lpm_nbits 0 false v2' with
                  | None => None
                  | Some n => Some (VSTLpm n v2)
                  end
    end
  | _ => None
  end.

Fixpoint get_before_uni (l: list (ValSetT * action_ref)):
  (list (ValSetT * action_ref)) * option (ValSetT * action_ref) :=
  match l with
  | nil => (nil, None)
  | (VSTUniversal, act) as x :: rest => (nil, Some x)
  | y :: rest => let (l', o) := get_before_uni rest in (y :: l', o)
  end.

Definition lpm_compare (va1 va2: (ValSetT * action_ref)): bool :=
  match (fst va1), (fst va2) with
  | VSTLpm n1 _, VSTLpm n2 _ => N.leb n2 n1
  | _, _ => false
  end.

Definition sort_lpm (l: list (ValSetT * action_ref)): list (ValSetT * action_ref) :=
  let (vl, actL) := List.split l in
  match lift_option (List.map lpm_set_of_set vl) with
  | None => nil
  | Some entries =>
    let entries' := List.combine entries actL in
    let (entries'', uni) := get_before_uni entries' in
    let sorted := mergeSort lpm_compare entries'' in
    match uni with
    | None => sorted
    | Some a => sorted ++ [a]
    end
  end.

Definition values_match_singleton (vs: list Val) (v: Val): option bool :=
  match vs with
  | [] => None
  | h :: _ => Ops.eval_binary_op_eq h v
  end.

Fixpoint vmm_help (bits0 bits1 bits2: list bool): bool :=
  match bits0, bits1, bits2 with
  | [], [], [] => true
  | _::tl0, _::tl1, false::tl2 => vmm_help tl0 tl1 tl2
  | hd0::tl0, hd1::tl1, true::tl2 => if (implb hd0 hd1) then (vmm_help tl0 tl1 tl2) else false
  (* should never hit *)
  | _, _, _ => false
  end.

Definition values_match_mask (vs: list Val) (v1 v2: Val): option bool :=
  match vs with
  | [] => None
  | v :: _ => match assert_bit v, assert_bit v1, assert_bit v2 with
              | Some bits0, Some bits1, Some bits2 =>
                let w0 := List.length bits0 in
                let w1 := List.length bits1 in
                let w2 := List.length bits2 in
                if negb ((w0 =? w1)%nat && (w1 =? w2)%nat) then None
                else Some (vmm_help bits0 bits1 bits2)
              | _, _, _ => None
              end
  end.

Definition lpm_nbits_to_mask (w1 w2 : N) : list bool :=
  (Zrepeat false (Z.of_N (w1 - w2))) ++ (Zrepeat true (Z.of_N w2)).

Definition values_match_lpm (vs: list Val) (v1: Val) (w2: N): option bool :=
  match vs with
  | [] => None
  | v :: _ => match assert_bit v, assert_bit v1 with
              | Some bits0, Some bits1 =>
                let w0 := List.length bits0 in
                let w1 := List.length bits1 in
                let w1n := N.of_nat w1 in
                if negb ((w0 =? w1)%nat && (w2 <=? w1n)%N) then None
                else let bits2 := lpm_nbits_to_mask w1n w2 in
                  Some (vmm_help bits0 bits1 bits2)
              | _, _ => None
              end
  end.

Fixpoint assert_int (v: Val): option (N * Z) :=
  match v with
  | ValBaseBit bits => Some (BitArith.from_lbool bits)
  | ValBaseInt bits => Some (IntArith.from_lbool bits)
  | ValBaseSenumField _ val => assert_int val
  | _ => None
  end.

Definition values_match_range (vs: list Val) (v1 v2: Val): option bool :=
  match vs with
  | [] => None
  | v :: _ => match assert_int v, assert_int v1, assert_int v2 with
              | Some (w0, z0), Some (w1, z1), Some (w2, z2) =>
                  if negb ((w0 =? w1)%N && (w1 =? w2)%N) then None
                  else Some ((z1 <=? z0) && (z0 <=? z2))
              | _, _, _ => None
              end
  end.

Fixpoint values_match_set (vs: list Val) (s: ValSetT): option bool :=
  let fix values_match_prod (vlist: list Val) (sl: list ValSetT): option bool :=
      match sl with
      | [] => match vlist with
              | [] => Some true
              | _ => None
              end
      | h :: srest => match vlist with
                      | [] => None
                      | v :: _ =>
                        match values_match_set [v] h with
                        | Some false => Some false
                        | Some true => values_match_prod (tl vlist) srest
                        | None => None
                        end
                      end
      end in
  let fix values_match_value_set (vlist: list Val) (sl: list ValSetT): option bool :=
      match sl with
      | [] => Some false
      | h :: srest => match values_match_set vlist h with
                      | Some true => Some true
                      | None => None
                      | Some false => values_match_value_set vlist srest
                      end
      end in
  match s with
  | VSTSingleton v => values_match_singleton vs v
  | VSTUniversal => Some true
  | VSTMask v1 v2 => values_match_mask vs v1 v2
  | VSTProd l => values_match_prod vs l
  | VSTRange lo hi => values_match_range vs lo hi
  | VSTValueSet _ _ sets => values_match_value_set vs sets
  | VSTLpm w2 v1 => values_match_lpm vs v1 w2
  end.

Definition is_some_true (b: option bool): bool :=
  match b with
  | Some true => true
  | _ => false
  end.

Definition filter_lpm_prod (ids: list ident) (vals: list Val)
           (entries: list (ValSetT * action_ref)): list (ValSetT * action_ref) * list Val :=
  match findi (String.eqb "lpm") ids with
  | None => ([], [])
  | Some (index, _) =>
    let f (es: ValSetT * action_ref): option (ValSetT * action_ref) :=
        match es with
        | (VSTProd l, a) => match nth_error l index with
                             | None => None
                             | Some vs => Some (vs, a)
                             end
        | _ => None
        end in
    match lift_option (map f (filter (fun s => is_some_true (values_match_set vals (fst s))) entries)) with
    | None => ([], [])
    | Some entries' => match nth_error vals index with
                       | None => ([], [])
                       | Some ks => (sort_lpm entries', [ks])
                       end
    end
  end.

Definition extern_match (key: list (Val * ident)) (entries: list table_entry_valset): option action_ref :=
  let ks := List.map fst key in
  let mks := List.map snd key in
  match check_lpm_count mks with
  | None => None
  | Some sort_mks =>
    let entries' := List.map (fun p => (valset_to_valsett (fst p), snd p)) entries in
    let (entries'', ks') :=
      if list_eqb String.eqb mks ["lpm"]
      then (sort_lpm entries', ks)
      else if sort_mks
           then filter_lpm_prod mks ks entries'
           else (entries', ks) in
    let l := List.filter (fun s => is_some_true (values_match_set ks' (fst s)))
                         entries'' in
    match l with
    | nil => None
    | sa :: _ => Some (snd sa)
    end
  end.

Definition find_func (funcs: list extern_func) (class func: ident) : option extern_func :=
  List.find (fun ef => ((class =? ef.(ef_class))%string &&
                        (func =? ef.(ef_func))%string))
            funcs.

Definition interp_extern
           (env: extern_env)
           (st: extern_state)
           (class: ident)
           (method: ident)
           (this: path)
           (targs: list P4Type)
           (args: list Val)
  : result Target.Exn.t (extern_state * list Val * signal) :=
  let* func := from_opt (find_func extern_funcs class method)
                        (Exn.Other (class ++ "." ++ method ++ "() not found in extern_funcs")) in
  func.(ef_interp) env st this targs args.

Definition interp_extern_safe :
  forall env st class method this targs args st' retvs sig,
    interp_extern env st class method this targs args = Ok (st', retvs, sig) ->
    exec_extern env st class method this targs args st' retvs sig.
Proof.
Admitted.

Instance V1ModelExternSem : ExternSem := Build_ExternSem
  env_object
  object
  construct_extern
  (fun e _ _ => e) (* extern_set_abstract_method *)
  exec_extern
  interp_extern
  interp_extern_safe
  extern_get_entries
  extern_set_entries
  extern_match.

(* package V1Switch<H, M>(...) *)
Definition get_hdr_and_meta type_args : option (P4Type * P4Type) :=
  match type_args with
  | [hdr; meta] => Some (hdr, meta)
  | _ => None
  end.

Inductive exec_prog
          (arch_type_args : list P4Type)
          (module_sem: path -> extern_state -> list Val -> extern_state -> list Val -> signal -> Prop)
          : extern_state -> list bool -> extern_state -> list bool -> Prop :=
| exec_prog_intro : forall hdr_type meta_type smeta1
                           s0 pin s7 pout s1 s2 s3 s4 s5 s6
                           meta1 standard_metadata1
                           hdr2 meta2 standard_metadata2
                           hdr3 meta3
                           hdr4 meta4 standard_metadata4
                           hdr5 meta5 standard_metadata5
                           hdr6 meta6,
      get_hdr_and_meta arch_type_args = Some (hdr_type, meta_type) ->
      uninit_sval_of_typ (Some false) meta_type = Some smeta1 ->
      sval_to_val read_ndetbit smeta1 meta1 ->
      PathMap.set ["packet_in"] (ObjPin pin) s0 = s1 ->
      module_sem ["main"; "p"] s1 [meta1; standard_metadata1] s2 [hdr2; meta2; standard_metadata2] SReturnNull ->
      module_sem ["main"; "vr"] s2 [hdr2; meta2] s3 [hdr3; meta3] SReturnNull ->
      module_sem ["main"; "ig"] s3 [hdr3; meta3; standard_metadata2] s4 [hdr4; meta4; standard_metadata4] SReturnNull ->
      module_sem ["main"; "eg"] s4 [hdr4; meta4; standard_metadata4] s5 [hdr5; meta5; standard_metadata5] SReturnNull ->
      module_sem ["main"; "ck"] s5 [hdr5; meta5] s6 [hdr6; meta6] SReturnNull ->
      module_sem ["main"; "dep"] s6 [hdr6] s7 nil SReturnNull ->
      PathMap.get ["packet_out"] s7 = Some (ObjPout pout) ->
      exec_prog arch_type_args module_sem s0 pin s7 pout.

Definition expect_result_null (r: result Exn.t (extern_state * list Val * signal)) : result Exn.t (extern_state * list Val) :=
  let* '(st, outs, sig) := r in
  match sig with
  | SExit
  | SReject _
  | SReturn (ValBaseNull) => mret (st, outs)
  | _ => error (Exn.Other "Expected SReturn (ValBaseNull) but got something different")
  end.

Definition set_std_meta_error (std: Val) (err: string) : Val :=
  std.

Definition initialize_val_of_type (typ: P4Type) : result Exn.t Val :=
  let* sv :=
    Result.from_opt (uninit_sval_of_typ (Some false) typ)
                    (Exn.Other "V1Model: uninit_sval_of_typ") in
  mret (interp_sval_to_val sv).

Definition interp_prog
           (arch_type_args : list P4Type)
           (run_module: path -> extern_state -> list Val -> result Exn.t (extern_state * list Val * signal))
           (s0: extern_state)
           (port: Z)
           (pin: list bool)
  : result Exn.t (extern_state * Z * list bool) :=
  let* '(hdr_type, meta_type) :=
    Result.from_opt (get_hdr_and_meta arch_type_args)
                    (Exn.Other "V1Model: get_hdr_and_meta") in
  let* meta1 := initialize_val_of_type meta_type in
  let s1 := PathMap.set ["packet_in"] (ObjPin pin) s0 in
  let standard_metadata1 :=
    ValBaseStruct [
        ("ingress_port", ValBaseBit (repeat false 9));
        ("egress_spec", ValBaseBit (repeat false 9));
        ("egress_port", ValBaseBit (repeat false 9));
        ("instance_type", ValBaseBit (repeat false 32));
        ("packet_length", ValBaseBit (repeat false 32));
        ("enq_timestamp", ValBaseBit (repeat false 32));
        ("enq_qdepth", ValBaseBit (repeat false 19));
        ("deq_timedelta", ValBaseBit (repeat false 32));
        ("deq_qdepth", ValBaseBit (repeat false 19));
        ("ingress_global_timestamp", ValBaseBit (repeat false 48));
        ("egress_global_timestamp", ValBaseBit (repeat false 48));
        ("mcast_grp", ValBaseBit (repeat false 16));
        ("egress_rid", ValBaseBit (repeat false 16));
        ("checksum_error", ValBaseBit [false]);
        ("parser_error", ValBaseError "NoError");
        ("priority", ValBaseBit (repeat false 3))
      ]
  in
  let* (s2, hdr2, meta2, standard_metadata2) :=
    let* ret := run_module ["main"; "p"] s1
                           [meta1;
                            standard_metadata1] in
    match ret with
    | (st', [hdr2; meta2; standard_metadata2], SReturn ValBaseNull) =>
        mret (st', hdr2, meta2, standard_metadata2)
    | (st', [hdr2; meta2; standard_metadata2], SReject err) =>
        let meta' := set_std_meta_error standard_metadata2 err in
        mret (st', hdr2, meta2, standard_metadata2)
    | _ => error (Exn.Other "interp_prog: failure in parser")
    end
  in
  let* (s3, outs3) := expect_result_null (run_module ["main"; "vr"] s2 [hdr2; meta2]) in
  let* (hdr3, meta3) :=
    match outs3 with
    | [hdr3; meta3] => mret (hdr3, meta3)
    | _ => error (Exn.Other "interp_prog: failure in verify checksum")
    end in
  let* (s4, outs4) := expect_result_null (run_module ["main"; "ig"] s3 [hdr3; meta3; standard_metadata2]) in
  let* (hdr4, meta4, standard_metadata4) :=
    match outs4 with
    | [hdr4; meta4; standard_metadata4] => mret (hdr4, meta4, standard_metadata4)
    | _ => error (Exn.Other "interp_prog: failure in ingress")
    end in
  let* (s5, outs5) := expect_result_null (run_module ["main"; "eg"] s4 [hdr4; meta4; standard_metadata4]) in
  let* (hdr5, meta5, standard_metadata5) :=
    match outs5 with
    | [hdr5; meta5; standard_metadata5] => mret (hdr5, meta5, standard_metadata5)
    | _ => error (Exn.Other "interp_prog: failure in egress")
    end in
  let* (s6, outs6) := expect_result_null (run_module ["main"; "ck"] s5 [hdr5; meta5]) in
  let* (hdr6, meta6) :=
    match outs6 with
    | [hdr6; meta6] => mret (hdr6, meta6)
    | _ => error (Exn.Other "interp_prog: failure in checksum")
    end in
  (* initialize packet_out *)
  let s6 := PathMap.set ["packet_out"] (ObjPout []) s6 in
  let* (s7, _) := expect_result_null (run_module ["main"; "dep"] s6 [hdr6; meta6]) in
  let* pkt := from_opt (PathMap.get ["packet_out"] s7)
                       (Exn.Other "interp_prog: failure recovering packet") in
  match pkt with
  | ObjPout pout => mret (s7, 0%Z, pout)
  | _ => error (Exn.Other "interp_prog: failure recovering packet")
  end.

Instance V1Model : Target := Build_Target _ "main" exec_prog interp_prog.

End V1Model.
