Require Import Strings.String.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Program.Program.
Require Import Typed.
Require Import Poulet4.Syntax.
Require Import P4Int.
Require Import Target.
Require Import Poulet4.SyntaxUtil.
Require Import Sublist.
Require Import Maps.
Require Import CoqLib.
Require Import P4Notations.
Import ListNotations.
Open Scope Z_scope.

Section V1Model.

Context {tags_t: Type} {inhabitant_tags_t : Inhabitant tags_t}.
Context {Expression: Type}.
Notation ident := (P4String.t tags_t).
Notation path := (list ident).
Notation P4Type := (@P4Type tags_t).
Notation Val := (@ValueBase tags_t).
Notation signal := (@signal tags_t).
Notation table_entry := (@table_entry tags_t Expression).
Notation action_ref := (@action_ref tags_t Expression).
Notation ValSet := (@ValueSet tags_t).

Inductive register := mk_register {
  reg_width : nat;
  reg_size : Z;
  reg_content : list Z
}.

Definition new_register (size : Z) (w : nat) :=
  mk_register w size (repeat 0 (Z.to_nat size)).

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
    | [ValBaseBit _ size]
    (* | [ValBaseInt _ size] *) =>
        match targs with
        | [TypBit w] =>
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

Definition REG_INDEX_WIDTH := 32%nat.

Inductive register_read_sem : extern_func_sem :=
  | exec_register_read : forall s p reg w index result,
      PathMap.get p s = Some (ObjRegister reg) ->
      reg_width reg = w ->
      -1 < index < reg_size reg ->
      Znth index (reg_content reg) = result ->
      register_read_sem s p nil [ValBaseBit REG_INDEX_WIDTH index] s [ValBaseBit w result] SReturnNull.

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
      register_write_sem s p nil [ValBaseBit REG_INDEX_WIDTH index; ValBaseBit w value]
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
      packet_in_extract_sem s p [typ] [ValBaseBit 32%nat len]
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

Fixpoint assert_set (v: Val): option ValSet :=
  match v with
  | ValBaseSet s => Some s
  | ValBaseInteger _
  | ValBaseInt _ _
  | ValBaseBit _ _ => Some (ValSetSingleton v)
  | ValBaseSenumField _ _ v => assert_set v
  | _ => None
  end.

Definition eval_p4int (n: @P4Int.t tags_t) : Val :=
  match P4Int.width_signed n with
  | None => ValBaseInteger (P4Int.value n)
  | Some (w, true) => ValBaseInt w (P4Int.value n)
  | Some (w, false) => ValBaseBit w (P4Int.value n)
  end.

Fixpoint simple_eval_expr (expr: @Syntax.Expression tags_t): Val :=
  match expr with
  | MkExpression _ (ExpInt v) _ _ => eval_p4int v
  | MkExpression _ (ExpMask exp1 exp2) _ _ =>
    ValBaseSet (ValSetMask (simple_eval_expr exp1) (simple_eval_expr exp2))
  | MkExpression _ (ExpRange exp1 exp2) _ _ =>
    ValBaseSet (ValSetRange (simple_eval_expr exp1) (simple_eval_expr exp2))
  | _ => ValBaseNull
  end.

Definition set_of_match (ma: @Match tags_t): option ValSet :=
  match ma with
  | MkMatch _ MatchDontCare _ => Some ValSetUniversal
  | MkMatch _ (MatchExpression expr) _ => assert_set (simple_eval_expr expr)
  end.

Fixpoint list_of_matches (matches: list (@Match tags_t)): option (list ValSet) :=
  match matches with
  | nil => Some nil
  | a :: rest => match set_of_match a with
                 | None => None
                 | Some vs => match (list_of_matches rest) with
                              | None => None
                              | Some l => Some (vs :: l)
                              end
                 end
  end.

Definition set_of_matches (entry: table_entry): option (ValSet * action_ref) :=
  match entry with
  | mk_table_entry matches action =>
    match list_of_matches matches with
    | None => None
    | Some [a] => Some (a, action)
    | Some l => Some (ValSetProd l, action)
    end
  end.

Fixpoint allSome {A: Type} (l: list (option A)): option (list A) :=
  match l with
  | nil => Some nil
  | None :: _ => None
  | Some a :: rest => match allSome rest with
                      | None => None
                      | Some r => Some (a :: r)
                      end
  end.

Definition bitstring_slice (n m l: Z): Z :=
  let slice_width := m + 1 - l in
  let shifted := Z.shiftr n l in
  let mask := two_p (slice_width - 1) in
  Z.land shifted mask.

Fixpoint bitwise_neg_of_nat (n: Z) (w: nat): Z :=
  match w with
  | O => n
  | S w1 => let w' := two_power_nat w1 in
            let g := bitstring_slice n (Z.of_nat w1) (Z.of_nat w1) in
            if (g =? 0)
            then bitwise_neg_of_nat (n + w') w1
            else bitwise_neg_of_nat (n - w') w1
  end.

Definition bitwise_neg_of_Z (n w: Z): Z :=
  if (w >? 0)
  then bitwise_neg_of_nat n (Z.to_nat w)
  else n.

Fixpoint bitwise_neg_of_val (v1: Z) (v2: Val): option Val :=
  match v2 with
  | ValBaseBool _ => None
  | ValBaseInteger z => Some (ValBaseInteger (bitwise_neg_of_Z v1 z))
  | ValBaseBit w z => Some (ValBaseBit w (bitwise_neg_of_Z v1 z))
  | ValBaseInt w z => Some (ValBaseInt w (bitwise_neg_of_Z v1 z))
  | ValBaseVarbit max w z => Some (ValBaseVarbit max w (bitwise_neg_of_Z v1 z))
  | ValBaseSenumField a b v =>
    match bitwise_neg_of_val v1 v with
    | Some vv => Some (ValBaseSenumField a b vv)
    | None => None
    end
  | _ => None
  end.

Fixpoint Z_of_val (v: Val): option Z :=
  match v with
  | ValBaseBool b => if b then Some 1 else Some 0
  | ValBaseInteger z
  | ValBaseBit _ z
  | ValBaseInt _ z
  | ValBaseVarbit _ _ z => Some z
  | ValBaseSenumField _ _ v' => Z_of_val v'
  | _ => None
  end.

Fixpoint bits_of_lpmmask_pos (acc: Z) (b: bool) (v: positive): option Z :=
  match v with
  | xH => Some (acc + 1)
  | xI rest => bits_of_lpmmask_pos (acc + 1) true rest
  | xO rest => if b then None else bits_of_lpmmask_pos acc b rest
  end.

Definition bits_of_lpmmask (acc: Z) (b: bool) (v: Z): option Z :=
  match v with
  | Z0 => Some acc
  | Zpos p
  | Zneg p => bits_of_lpmmask_pos acc b p
  end.

Fixpoint lpm_set_of_set (vs: ValSet): option ValSet :=
  let fix lsos (l: list ValSet): option (list ValSet) :=
      match l with
      | nil => Some nil
      | a :: rest => match lpm_set_of_set a with
                     | None => None
                     | Some v => match lsos rest with
                                 | Some vl => Some (v :: vl)
                                 | None => None
                                 end
                     end
      end in
  match vs with
  | ValSetUniversal
  | ValSetLpm _ _ _ => Some vs
  | ValSetProd l => match lsos l with
                    | Some l' => Some (ValSetProd l')
                    | None => None
                    end
  | ValSetSingleton v => match bitwise_neg_of_val 0 v with
                         | None => None
                         | Some val => Some (ValSetLpm v (width_of_val v) val)
                         end
  | ValSetMask v1 v2 =>
    match Z_of_val v2 with
    | None => None
    | Some v2' => match bits_of_lpmmask 0 false v2' with
                  | None => None
                  | Some n => Some (ValSetLpm v1 (Z.to_nat n) v2)
                  end
    end
  | _ => None
  end.

Fixpoint get_before_uni (l: list (ValSet * action_ref)):
  (list (ValSet * action_ref)) * option (ValSet * action_ref) :=
  match l with
  | nil => (nil, None)
  | (ValSetUniversal, act) as x :: rest => (nil, Some x)
  | y :: rest => let (l', o) := get_before_uni rest in (y :: l', o)
  end.

Definition lpm_compare (va1 va2: (ValSet * action_ref)): bool :=
  match (fst va1), (fst va2) with
  | ValSetLpm _ n1 _, ValSetLpm _ n2 _ => Nat.leb n2 n1
  | _, _ => false
  end.

Definition sort_lpm (l: list (ValSet * action_ref)): list (ValSet * action_ref) :=
  let (vl, actL) := List.split l in
  match allSome (List.map lpm_set_of_set vl) with
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
  | h :: _ => match (Z_of_val h), (Z_of_val v) with
              | Some z1, Some z2 => Some (Z.eqb z1 z2)
              | _, _ => None
              end
  end.

Fixpoint assert_bit (v: Val): option (nat * Z) :=
  match v with
  | ValBaseBit w val => Some (w, val)
  | ValBaseSenumField _ _ val => assert_bit val
  | _ => None
  end.

Fixpoint vmm_help (w0 w1 w2: nat) (b0 b1 b2: Z): bool :=
  if negb ((w0 =? w1)%nat && (w1 =? w2)%nat)
  then false
  else match w0 with
       | O => true
       | S n => if (b2 mod 2 =? 0) || (b1 mod 2 =? b0 mod 2)
                then vmm_help n (w1 - 1) (w2 -1) (b0 / 2) (b1 / 2) (b2 / 2)
                else false
       end.

Definition values_match_mask (vs: list Val) (v1 v2: Val): option bool :=
  match vs with
  | [] => None
  | v :: _ => match assert_bit v, assert_bit v1, assert_bit v2 with
              | Some (w0, b0), Some (w1, b1), Some (w2, b2) =>
                Some (vmm_help w0 w1 w2 b0 b1 b2)
              | _, _, _ => None
              end
  end.

Definition values_match_range (vs: list Val) (v1 v2: Val): option bool :=
  match vs with
  | [] => None
  | v :: _ => match Z_of_val v, Z_of_val v1, Z_of_val v2 with
              | Some z, Some z1, Some z2 => Some ((z1 <=? z) && (z <=? z2))
              | _, _, _ => None
              end
  end.

Fixpoint values_match_set (vs: list Val) (s: ValSet): option bool :=
  let fix values_match_prod (vlist: list Val) (sl: list ValSet): option bool :=
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
  let fix values_match_value_set (vlist: list Val) (sl: list ValSet): option bool :=
      match sl with
      | [] => Some false
      | h :: srest => match values_match_set vlist h with
                      | Some true => Some true
                      | None => None
                      | Some false => values_match_value_set vlist srest
                      end
      end in
  match s with
  | ValSetSingleton v => values_match_singleton vs v
  | ValSetUniversal => Some true
  | ValSetMask v1 v2 => values_match_mask vs v1 v2
  | ValSetProd l => values_match_prod vs l
  | ValSetRange lo hi => values_match_range vs lo hi
  | ValSetValueSet _ _ sets => values_match_value_set vs sets
  | ValSetLpm v1 _ v2 => values_match_mask vs v1 v2
  end.

Definition is_some_true (b: option bool): bool :=
  match b with
  | Some true => true
  | _ => false
  end.

Definition filter_lpm_prod (ids: list ident) (vals: list Val)
           (entries: list (ValSet * action_ref)):
  list (ValSet * action_ref) * list Val :=
  match findi (P4String.equivb !"lpm") ids with
  | None => ([], [])
  | Some (index, _) =>
    let f (es: ValSet * action_ref): option (ValSet * action_ref) :=
        match es with
        | (ValSetProd l, a) => match nth_error l index with
                             | None => None
                             | Some vs => Some (vs, a)
                             end
        | _ => None
        end in
    match allSome (map f (filter (fun s => is_some_true (values_match_set vals (fst s))) entries)) with
    | None => ([], [])
    | Some entries' => match nth_error vals index with
                       | None => ([], [])
                       | Some ks => (sort_lpm entries', [ks])
                       end
    end
  end.

Definition extern_match (key: list (Val * ident)) (entries: list table_entry): option action_ref :=
  let ks := List.map fst key in
  let mks := List.map snd key in
  match check_lpm_count mks with
  | None => None
  | Some sort_mks =>
    match allSome (List.map set_of_matches entries) with
    | Some entries' =>
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
    | None => None
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
