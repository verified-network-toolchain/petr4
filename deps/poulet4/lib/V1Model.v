Require Import Strings.String.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Program.Program.

Require Import Poulet4.Typed.
Require Import Poulet4.Syntax.
Require Import Poulet4.Ops.
Require Import Poulet4.P4Int.
Require Import Poulet4.P4Arith.
Require Import Poulet4.Target.
Require Import Poulet4.SyntaxUtil.
Require Import Poulet4.Sublist.
Require Import Poulet4.Maps.
Require Import Poulet4.CoqLib.
Require Import Poulet4.P4Notations.
Import ListNotations.
Open Scope Z_scope.

Section V1Model.

Context {tags_t: Type} {inhabitant_tags_t : Inhabitant tags_t}.
Context {Expression: Type}.
Notation ident := (P4String.t tags_t).
Notation path := (list ident).
Notation P4Type := (@P4Type tags_t).
Notation Val := (@ValueBase tags_t bool).
Notation ValSet := ValueSet.
Notation signal := (@signal tags_t).
Notation table_entry := (@table_entry tags_t Expression).
Notation action_ref := (@action_ref tags_t Expression).

Inductive register := mk_register {
  reg_width : N;
  reg_size : Z;
  reg_content : list Z
}.

Definition new_register (size : Z) (w : N) :=
  mk_register w size (Zrepeat 0 size).

Definition packet_in := list bool.

Definition packet_out := list bool.

Inductive object :=
  | ObjTable (entries : list table_entry)
  | ObjRegister (reg : register)
  | ObjPin (pin : packet_in)
  | ObjPout (pout : packet_out).

Definition extern_state := @PathMap.t tags_t object.

Definition extern_empty : extern_state := PathMap.empty.

Definition dummy_tags := @default tags_t _.

Definition alloc_extern (s : extern_state) (class : ident) (targs : list P4Type) (p : path) (args : list Val) :=
  if P4String.equivb class !"register" then
    match args with
    (* | [ValBaseInteger size] *)
    | [ValBaseBit bits]
    (* | [ValBaseInt _ size] *) =>
        match targs with
        | [TypBit w] =>
            let (_, size) := BitArith.from_lbool bits in
            PathMap.set p (ObjRegister (new_register size w)) s
        | _ => s (* fail *)
        end
    | _ => s (* fail *)
    end
  else
    s.

Definition extern_func_sem := extern_state -> path -> list P4Type -> list Val -> extern_state -> list Val -> signal -> Prop.

Inductive extern_func := mk_extern_func_sem {
  ef_class : ident;
  ef_func : ident;
  ef_sem : extern_func_sem
}.

Definition apply_extern_func_sem (func : extern_func) : extern_state -> ident -> ident -> path -> list P4Type -> list Val -> extern_state -> list Val -> signal -> Prop :=
  match func with
  | mk_extern_func_sem class_name func_name sem =>
      fun s class_name' func_name' =>
          if P4String.equivb class_name class_name' && P4String.equivb func_name func_name' then
            sem s
          else
            fun _ _ _ _ _ _ => False
  end.

Definition REG_INDEX_WIDTH := 32%N.

Inductive register_read_sem : extern_func_sem :=
  | exec_register_read : forall s p reg w index result,
      PathMap.get p s = Some (ObjRegister reg) ->
      reg_width reg = w ->
      -1 < index < reg_size reg ->
      Znth index (reg_content reg) = result ->
      register_read_sem s p nil [ValBaseBit (to_lbool REG_INDEX_WIDTH index)] 
        s [ValBaseBit (to_lbool w result)] SReturnNull.

Definition register_read : extern_func := {|
  ef_class := !"register";
  ef_func := !"read";
  ef_sem := register_read_sem
|}.

Inductive register_write_sem : extern_func_sem :=
  | exec_register_write : forall s p reg w content' index value,
      PathMap.get p s = Some (ObjRegister reg) ->
      reg_width reg = w ->
      -1 < index < reg_size reg ->
      upd_Znth index (reg_content reg) value = content' ->
      register_write_sem s p nil 
            [ValBaseBit (to_lbool REG_INDEX_WIDTH index); ValBaseBit (to_lbool w value)]
            (PathMap.set p (ObjRegister (mk_register w (reg_size reg) content')) s)
            [] SReturnNull.

Definition register_write : extern_func := {|
  ef_class := !"register";
  ef_func := !"write";
  ef_sem := register_write_sem
|}.

Axiom extract : forall (pin : list bool) (typ : P4Type), Val * list bool.
Axiom extract2 : forall (pin : list bool) (typ : P4Type) (len : Z), Val * list bool.

Inductive packet_in_extract_sem : extern_func_sem :=
  | exec_packet_in_extract : forall s p pin typ v pin',
      PathMap.get p s = Some (ObjPin pin) ->
      extract pin typ = (v, pin') ->
      packet_in_extract_sem s p [typ] []
            (PathMap.set p (ObjPin pin') s)
          [v] SReturnNull
  | exec_packet_in_extract2 : forall s p pin typ len v pin',
      PathMap.get p s = Some (ObjPin pin) ->
      extract2 pin typ len = (v, pin') ->
      packet_in_extract_sem s p [typ] [ValBaseBit (to_lbool 32%N len)]
            (PathMap.set p (ObjPin pin') s)
          [v] SReturnNull.

Definition packet_in_extract : extern_func := {|
  ef_class := !"packet_in";
  ef_func := !"extract";
  ef_sem := packet_in_extract_sem
|}.

Axiom emit : forall (pout : list bool) (v : Val), list bool.

Inductive packet_out_emit_sem : extern_func_sem :=
  | exec_packet_out_emit : forall s p pout typ v pout',
      PathMap.get p s = Some (ObjPout pout) ->
      emit pout v = pout' ->
      packet_out_emit_sem s p [typ] [v]
            (PathMap.set p (ObjPout pout') s)
          [] SReturnNull.

Definition packet_out_emit : extern_func := {|
  ef_class := !"packet_out";
  ef_func := !"emit";
  ef_sem := packet_out_emit_sem
|}.

(* This only works when tags_t is a unit type. *)

Inductive exec_extern : extern_state -> ident (* class *) -> ident (* method *) -> path -> list P4Type -> list Val -> extern_state -> list Val -> signal -> Prop :=
  | exec_extern_register_read : forall s p targs args s' args' vret,
      apply_extern_func_sem register_read s (ef_class register_read) (ef_func register_read) p targs args s' args' vret ->
      exec_extern s (ef_class register_read) (ef_func register_read) p targs args s' args' vret
  | exec_extern_register_write : forall s p targs args s' args' vret,
      apply_extern_func_sem register_write s (ef_class register_write) (ef_func register_write) p targs args s' args' vret ->
      exec_extern s (ef_class register_write) (ef_func register_write) p targs args s' args' vret
  | exec_extern_packet_in_extract : forall s p targs args s' args' vret,
      apply_extern_func_sem packet_in_extract s (ef_class packet_in_extract) (ef_func packet_in_extract) p targs args s' args' vret ->
      exec_extern s (ef_class packet_in_extract) (ef_func packet_in_extract) p targs args s' args' vret
  | exec_extern_packet_out_emit : forall s p targs args s' args' vret,
      apply_extern_func_sem packet_out_emit s (ef_class packet_out_emit) (ef_func packet_out_emit) p targs args s' args' vret ->
      exec_extern s (ef_class packet_out_emit) (ef_func packet_out_emit) p targs args s' args' vret.

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

Definition check_lpm_count (mks: list ident): option bool :=
  let num_lpm := List.length (List.filter (P4String.equivb !"lpm") mks) in
  if (1 <? num_lpm)%nat
  then None
  else Some (num_lpm =? 1)%nat.

Fixpoint assert_bit (v: Val): option (list bool) :=
  match v with
  | ValBaseBit bits => Some bits
  | ValBaseSenumField _ _ val => assert_bit val
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
  | ValBaseSenumField _ _ val => assert_int val
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
  match findi (P4String.equivb !"lpm") ids with
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
            if list_eqb (@P4String.equivb tags_t) mks !["lpm"]
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

Instance V1ModelExternSem : ExternSem := Build_ExternSem
  extern_state
  extern_empty
  alloc_extern
  exec_extern
  extern_get_entries
  extern_match.

Inductive exec_prog : (path -> extern_state -> list Val -> extern_state -> list Val -> signal -> Prop) ->
    extern_state -> list bool -> extern_state -> list bool -> Prop :=
  | exec_prog_intro : forall (module_sem : _ -> _ -> _ -> _ -> _ -> _ -> Prop) s0 pin s7 pout s1 s2 s3 s4 s5 s6
      meta1 standard_metadata1 hdr2 meta2 standard_metadata2 hdr3 meta3 hdr4 meta4 standard_metadata4 hdr5 meta5 standard_metadata5 hdr6 meta6,
      PathMap.set !["packet_in"] (ObjPin pin) s0 = s1 ->
      module_sem !["main"; "p"] s1 [meta1; standard_metadata1] s2 [hdr2; meta2; standard_metadata2] SReturnNull ->
      module_sem !["main"; "vr"] s2 [hdr2; meta2] s3 [hdr3; meta3] SReturnNull ->
      module_sem !["main"; "ig"] s3 [hdr3; meta3; standard_metadata2] s4 [hdr4; meta4; standard_metadata4] SReturnNull ->
      module_sem !["main"; "eg"] s4 [hdr4; meta4; standard_metadata4] s5 [hdr5; meta5; standard_metadata5] SReturnNull ->
      module_sem !["main"; "ck"] s5 [hdr5; meta5] s6 [hdr6; meta6] SReturnNull ->
      module_sem !["main"; "dep"] s6 [hdr6] s7 nil SReturnNull ->
      PathMap.get !["packet_out"] s7 = Some (ObjPout pout) ->
      exec_prog module_sem s0 pin s7 pout.

Instance V1Model : Target := Build_Target _ exec_prog.

End V1Model.
