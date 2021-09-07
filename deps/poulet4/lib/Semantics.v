Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Program.Program.
Require Import Poulet4.Typed.
Require Import Poulet4.Syntax.
Require Import Poulet4.P4Int.
Require Import Poulet4.P4Arith.
Require Import Poulet4.AList.
Require Import Poulet4.Ops.
Require Import Poulet4.Maps.
Require Export Poulet4.Target.
Require Export Poulet4.SyntaxUtil.
Require Export Poulet4.Sublist.
Require Import Poulet4.P4Notations.
Import ListNotations.

Section Semantics.

Context {tags_t: Type} {inhabitant_tags_t : Inhabitant tags_t}.
Notation Val := (@ValueBase tags_t bool).
Notation Sval := (@ValueBase tags_t (option bool)).
Notation ValSet := (@ValueSet tags_t).
Notation Lval := (@ValueLvalue tags_t).

Notation ident := (P4String.t tags_t).
Notation path := (list ident).
Notation P4Int := (P4Int.t tags_t).
Notation P4String := (P4String.t tags_t).
Notation signal := (@signal tags_t).

Context `{@Target tags_t (@Expression tags_t)}.

Definition mem := @PathMap.t tags_t Sval.

Definition state : Type := mem * extern_state.

Definition set_memory m (s : state) : state :=
  let (_, es) := s in (m, es).

Definition update_memory (f : mem -> mem) (s : state) : state :=
  let (m, es) := s in (f m, es).

Definition get_memory (s : state) : mem :=
  let (m, _) := s in m.

Definition get_external_state (s : state) :=
  let (_, es) := s in es.

Definition loc_to_path (this : path) (loc : Locator) : path :=
  match loc with
  | LGlobal p => p
  | LInstance p => this ++ p
  end.

Inductive fundef :=
  | FInternal
      (params : list (@Locator tags_t * direction))
      (init : @Block tags_t)
      (body : @Block tags_t)
  | FTable
      (name : ident)
      (keys : list (@TableKey tags_t))
      (actions : list (@Expression tags_t))
      (default_action : option (@Expression tags_t))
      (entries : option (list (@table_entry tags_t (@Expression tags_t))))
  | FExternal
      (class : ident)
      (name : ident)
      (* (params : list (ident * direction)) *).

Axiom dummy_fundef : fundef.

Definition genv_func := @PathMap.t tags_t fundef.
Definition genv_typ := @IdentMap.t tags_t (@P4Type tags_t).
Definition genv_senum := @IdentMap.t tags_t Sval.

Record genv := MkGenv {
  ge_func :> genv_func;
  ge_typ :> genv_typ;
  ge_senum :> genv_senum
}.

Definition name_to_type (ge_typ: genv_typ) (typ : @Typed.name tags_t):
  option (@P4Type tags_t) :=
  match typ with
  | BareName id => IdentMap.get id ge_typ
  | QualifiedName _ id => IdentMap.get id ge_typ
  end.

Variable ge : genv.

Definition get_real_type (typ: @P4Type tags_t): option (@P4Type tags_t) :=
  match typ with
  | TypTypeName name => name_to_type ge name
  | _ => Some typ
  end.

Inductive read_ndetbit : option bool -> bool -> Prop :=
  | read_none : forall b, read_ndetbit None b
  | read_some : forall b, read_ndetbit (Some b) b.

Inductive strict_read_ndetbit : option bool -> bool -> Prop :=
  | strict_read_some : forall b, strict_read_ndetbit (Some b) b.

Definition read_detbit (b : bool) (b': option bool) :=
  b' = Some b.

Inductive read_bits {A B} (read_one_bit : A -> B -> Prop) : 
                    list A -> list B -> Prop :=
  | read_nil : read_bits read_one_bit nil nil
  | read_cons : forall b b' tl tl',
                read_one_bit b b' ->
                read_bits read_one_bit tl tl' ->
                read_bits read_one_bit (b :: tl) (b' :: tl').

Inductive exec_val {A B} (read_one_bit : A -> B -> Prop) : 
                   @ValueBase tags_t A -> @ValueBase tags_t B -> Prop :=
  | exec_val_null : exec_val read_one_bit ValBaseNull ValBaseNull
  | exec_val_bool : forall b b',
                    read_one_bit b b' ->
                    exec_val read_one_bit (ValBaseBool b) (ValBaseBool b')
  | exec_val_integer : forall n, 
                       exec_val read_one_bit (ValBaseInteger n) (ValBaseInteger n)
  | exec_val_bit : forall lb lb',
                   read_bits read_one_bit lb lb' ->
                   exec_val read_one_bit (ValBaseBit lb) (ValBaseBit lb')
  | exec_val_int : forall lb lb',
                   read_bits read_one_bit lb lb' ->
                   exec_val read_one_bit (ValBaseInt lb) (ValBaseInt lb')
  | exec_val_varbit : forall max lb lb',
                      read_bits read_one_bit lb lb' ->
                      exec_val read_one_bit (ValBaseVarbit max lb) (ValBaseVarbit max lb')
  | exec_val_string : forall s,
                      exec_val read_one_bit (ValBaseString s) (ValBaseString s)
  | exec_val_tuple : forall lv lv',
                     exec_vals read_one_bit lv lv' ->
                     exec_val read_one_bit (ValBaseTuple lv) (ValBaseTuple lv')
  | exec_val_record : forall kvs kvs',
                      AList.all_values (exec_val read_one_bit) kvs kvs' ->
                      exec_val read_one_bit (ValBaseRecord kvs) (ValBaseRecord kvs')
  | exec_val_error: forall s,
                    exec_val read_one_bit (ValBaseError s) (ValBaseError s)
  | exec_val_matchkind: forall s,
                        exec_val read_one_bit (ValBaseMatchKind s) (ValBaseMatchKind s)
  | exec_val_struct : forall kvs kvs',
                      AList.all_values (exec_val read_one_bit) kvs kvs' ->
                      exec_val read_one_bit (ValBaseStruct kvs) (ValBaseStruct kvs')
  (* Invariant: when validity bit is None, kvs are also None. *)
  | exec_val_header : forall kvs kvs' b b',
                      read_one_bit b b' ->
                      AList.all_values (exec_val read_one_bit) kvs kvs' ->
                      exec_val read_one_bit (ValBaseHeader kvs b) (ValBaseHeader kvs' b')
  | exec_val_union : forall kvs kvs',
                     AList.all_values (exec_val read_one_bit) kvs kvs' ->
                     exec_val read_one_bit (ValBaseStruct kvs) (ValBaseStruct kvs')
  | exec_val_stack : forall lv lv' size next,
                     exec_vals read_one_bit lv lv' ->
                     exec_val read_one_bit (ValBaseStack lv size next) (ValBaseStack lv' size next)
  | exec_val_enum_field : forall typ_name enum_name,
                          exec_val read_one_bit (ValBaseEnumField typ_name enum_name) 
                                                (ValBaseEnumField typ_name enum_name)
  | exec_val_senum_field : forall typ_name enum_name v v',
                           exec_val read_one_bit v v' ->
                           exec_val read_one_bit (ValBaseSenumField typ_name enum_name v) 
                                                 (ValBaseSenumField typ_name enum_name v')
  | exec_val_senum : forall kvs kvs',
                     AList.all_values (exec_val read_one_bit) kvs kvs' ->
                     exec_val read_one_bit (ValBaseSenum kvs) (ValBaseSenum kvs')
(* 
with exec_vset {A B} (read_one_bit : A -> B -> Prop) : 
               @ValueSet tags_t A -> @ValueSet tags_t B -> Prop :=
  | exec_vset_singleton : forall v v',
                          exec_val read_one_bit v v' ->
                          exec_vset read_one_bit (ValSetSingleton v) (ValSetSingleton v')
  | exec_vset_universal : exec_vset read_one_bit ValSetUniversal ValSetUniversal
  | exec_vset_mask : forall v v' m m',
                     exec_val read_one_bit v v' ->
                     exec_val read_one_bit m m' ->
                     exec_vset read_one_bit (ValSetMask v m) (ValSetMask v' m')
  | exec_vset_range : forall lo lo' hi hi',
                      exec_val read_one_bit lo lo' ->
                      exec_val read_one_bit hi hi' ->
                      exec_vset read_one_bit (ValSetRange lo hi) (ValSetRange lo' hi')
  | exec_vset_prod : forall vsets vsets',
                     exec_vsets read_one_bit vsets vsets' ->
                     exec_vset read_one_bit (ValSetProd vsets) (ValSetProd vsets')
  (* problems in syntax and v1model of exec_vset_lpm, omitted for now *)
  | exec_vset_set : forall size size' mem vsets vsets',
                    exec_val read_one_bit size size' ->
                    exec_vsets read_one_bit vsets vsets' ->
                    exec_vset read_one_bit (ValSetValueSet size mem vsets) (ValSetValueSet size' mem vsets')
with exec_vsets {A B} (read_one_bit : A -> B -> Prop) : 
               list (@ValueSet tags_t A) -> list (@ValueSet tags_t B) -> Prop :=
  | exec_vsets_nil : exec_vsets read_one_bit nil nil
  | exec_vsets_cons : forall hd tl hd' tl',
                     exec_vset read_one_bit hd hd' ->
                     exec_vsets read_one_bit tl tl' ->
                     exec_vsets read_one_bit (hd :: tl) (hd' :: tl') *)
with exec_vals {A B} (read_one_bit : A -> B -> Prop) : 
               list (@ValueBase tags_t A) -> list (@ValueBase tags_t B) -> Prop :=
  | exec_vals_nil : exec_vals read_one_bit nil nil
  | exec_vals_cons : forall hd tl hd' tl',
                     exec_val read_one_bit hd hd' ->
                     exec_vals read_one_bit tl tl' ->
                     exec_vals read_one_bit (hd :: tl) (hd' :: tl').

Definition sval_to_val (read_one_bit : option bool -> bool -> Prop) := 
  exec_val read_one_bit.

Definition svals_to_vals (read_one_bit : option bool -> bool -> Prop) :=
  exec_vals read_one_bit.

Definition val_to_sval := 
  exec_val read_detbit.

Definition vals_to_svals := 
  exec_vals read_detbit.

Definition eval_p4int_sval (n: P4Int) : Sval :=
  match P4Int.width_signed n with
  | None => ValBaseInteger (P4Int.value n)
  | Some (w, true) => ValBaseInt (to_loptbool w (P4Int.value n))
  | Some (w, false) => ValBaseBit (to_loptbool w (P4Int.value n))
  end.

Definition eval_p4int_val (n: P4Int) : Val :=
  match P4Int.width_signed n with
  | None => ValBaseInteger (P4Int.value n)
  | Some (w, true) => ValBaseInt (to_lbool w (P4Int.value n))
  | Some (w, false) => ValBaseBit (to_lbool w (P4Int.value n))
  end.

Definition loc_to_sval (this : path) (loc : Locator) (s : state) : option Sval :=
  PathMap.get (loc_to_path this loc) (get_memory s).

Fixpoint array_access_idx_to_z (v : Val) : (option Z) :=
  match v with
  | ValBaseInt bits => Some (snd (BitArith.from_lbool bits))
  | ValBaseBit bits => Some (snd (IntArith.from_lbool bits))
  | ValBaseInteger value => Some value
  (* added in 1.2.2 *)
  | ValBaseSenumField _ _ value => array_access_idx_to_z value
  | _ => None
  end.

Definition bitstring_slice_bits_to_z (v : Val) : option (N * Z) :=
  match v with
  | ValBaseInt bits => Some (IntArith.from_lbool bits)
  | ValBaseBit bits => Some (BitArith.from_lbool bits)
  | _ => None
  end.

(* Ref:When accessing the bits of negative numbers, all functions below will
   use the two's complement representation.
   For instance, -1 will correspond to an infinite stream of true bits.
   https://coq.inria.fr/library/Coq.ZArith.BinIntDef.html *)
Definition bitstring_slice (i : Z) (lo : Z) (hi : Z) : Z :=
  let mask := (Z.pow 2 (hi - lo + 1) - 1)%Z in
  Z.land (Z.shiftr i lo) mask.

Fixpoint uninit_sval_of_typ (hvalid : option bool) (typ : @P4Type tags_t) : option Sval := 
  match typ with
  | TypBool => Some (ValBaseBool None)
  (* | TypString => *)
  | TypInt w => Some (ValBaseInt (Zrepeat None (Z.of_N w)))
  | TypBit w => Some (ValBaseBit (Zrepeat None (Z.of_N w)))
  (* | TypVarBit w => *)
  | TypArray typ size =>
      match uninit_sval_of_typ hvalid typ with
      | Some sv => Some (ValBaseStack (Zrepeat sv (Z.of_N size)) size 0)
      | None => None
      end
  | TypTuple typs
  | TypList typs => 
      match lift_option (List.map (uninit_sval_of_typ hvalid) typs) with
      | Some svs => Some (ValBaseTuple svs)
      | None => None
      end
  (*
  | TypRecord
  | TypSet
  | TypError
  | TypVoid
  | TypHeader hvalid hvalid (if uninit_hvalid then None else some false)
  | TypHeaderUnion
  | TypStruct
  | TypEnum *)
  | _ => None
  end.
(* Type without uninitialized svals:
    TypInteger, TypMatchKind, TypTypeName, TypNewType
    TypControl, TypParser, TypExtern, TypFunction, TypAction, 
    TypTable, TypPackage, TypSpecializedType, TypConstructor
   ValueBase without uninitialized svals:
    ValBaseInteger, ValBaseString, ValBaseError, ValBaseMatchKind
*)
Definition kv_map_func {A B} (f: A -> B) (kv : P4String * A): P4String * B :=
  let (k, v) := kv in (k, f v).

Definition kv_map {A B} (f: A -> B) (kvs : P4String.AList tags_t A): P4String.AList tags_t B :=
  List.map (kv_map_func f) kvs.

Fixpoint uninit_sval_of_sval (hvalid : option bool) (v : Sval): Sval := 
  match v with
  | ValBaseBool _ => ValBaseBool None
  | ValBaseBit bits => ValBaseBit (List.map (fun _ => None) bits)
  | ValBaseInt bits => ValBaseInt (List.map (fun _ => None) bits)
  (* May need change after clarifying the uninit sval of varbit *)
  | ValBaseVarbit max bits => ValBaseVarbit max (List.map (fun _ => None) bits)
  | ValBaseTuple vs => ValBaseTuple (List.map (uninit_sval_of_sval hvalid) vs)
  | ValBaseRecord kvs => ValBaseRecord (kv_map (uninit_sval_of_sval hvalid) kvs)
  | ValBaseStruct kvs => ValBaseStruct (kv_map (uninit_sval_of_sval hvalid) kvs)
  | ValBaseHeader kvs is_valid => ValBaseHeader (kv_map (uninit_sval_of_sval hvalid) kvs) hvalid
  | ValBaseUnion kvs => ValBaseUnion (kv_map (uninit_sval_of_sval hvalid) kvs)
  | ValBaseStack vs size next => ValBaseStack (List.map (uninit_sval_of_sval hvalid) vs) size next
  | ValBaseSenumField typ_name enum_name v =>  ValBaseSenumField typ_name enum_name (uninit_sval_of_sval hvalid v)
  | ValBaseSenum kvs => ValBaseSenum (kv_map (uninit_sval_of_sval hvalid) kvs)
  (* ValBaseNull, ValBaseInteger, ValBaseString, ValBaseError, ValBaseMatchKind, ValBaseEnumField *)
  | _ => v
  end.
(* with uninit_sval_of_svset (uninit_hvalid : bool) (vset: @ValueSet tags_t (option bool)) : 
                          @ValueSet tags_t (option bool) :=
  match vset with
  | ValSetSingleton v => ValSetSingleton (uninit_sval_of_sval uninit_hvalid v)
  | ValSetUniversal => vset
  | ValSetMask v mask => ValSetMask (uninit_sval_of_sval uninit_hvalid v) (uninit_sval_of_sval uninit_hvalid mask)
  | ValSetRange lo hi => ValSetMask (uninit_sval_of_sval uninit_hvalid lo) (uninit_sval_of_sval uninit_hvalid hi)
  | ValSetProd vsets => ValSetProd (List.map (uninit_sval_of_svset uninit_hvalid) vsets)
  | ValSetLpm width nbits v => ValSetLpm (uninit_sval_of_sval uninit_hvalid width) nbits (uninit_sval_of_sval uninit_hvalid v)
  | ValSetValueSet size members vsets => ValSetValueSet (uninit_sval_of_sval uninit_hvalid size) members 
                                                        (List.map (uninit_sval_of_svset uninit_hvalid) vsets)
  end. *)


(* The following reads give unspecified values: 
    1. reading a field from a header that is currently invalid.
    2. reading a field from a header that is currently valid, but the field has not been initialized 
       since the header was last made valid. 
   Guaranteed by setting all fields to noninitialized when the header is made invalid (declaration & setInvalid)
   and setting only the valid bit and given fields when the header is made valid (initialization & setValid) *)
Inductive get_member : Sval -> P4String -> Sval -> Prop :=
  | get_member_struct : forall fields member v,
                        AList.get fields member = Some v ->
                        get_member (ValBaseStruct fields) member v
  | get_member_record : forall fields member v,
                        AList.get fields member = Some v ->
                        get_member (ValBaseRecord fields) member v
  | get_member_union : forall fields member v,
                       AList.get fields member = Some v ->
                       get_member (ValBaseUnion fields) member v
  | get_member_header : forall fields b member v,
                        AList.get fields member = Some v ->
                        get_member (ValBaseHeader fields b) member v
  | get_member_stack_size : forall headers size next,
                            get_member (ValBaseStack headers size next) !"size" 
                              (ValBaseBit (to_loptbool 32 (Z.of_N size)))
  | get_member_stack_last_index : forall headers size next sv,
                                  (if (next =? 0)%N 
                                    then uninit_sval_of_typ None (TypBit 32) = Some sv 
                                    else sv = (ValBaseBit (to_loptbool 32 (Z.of_N (next - 1))))) ->
                                  get_member (ValBaseStack headers size next) !"lastIndex" sv.

(* Note that expressions don't need decl_path. *)
Inductive exec_expr (read_one_bit : option bool -> bool -> Prop)
                    : path -> (* temp_env -> *) state -> (@Expression tags_t) -> Sval ->
                      (* trace -> *) (* temp_env -> *) (* state -> *) (* signal -> *) Prop :=
  | exec_expr_bool : forall b this st tag typ dir,
                     exec_expr read_one_bit this st
                     (MkExpression tag (ExpBool b) typ dir)
                     (ValBaseBool (Some b))
  | exec_expr_int : forall i isv this st tag typ dir,
                    isv = eval_p4int_sval i ->
                    exec_expr read_one_bit this st
                    (MkExpression tag (ExpInt i) typ dir)
                    isv
  | exec_expr_string : forall s this st tag typ dir,
                       exec_expr read_one_bit this st
                       (MkExpression tag (ExpString s) typ dir)
                       (ValBaseString s)
  | exec_expr_name: forall name loc sv this st tag typ dir,
                    loc_to_sval this loc st = Some sv ->
                    exec_expr read_one_bit this st
                    (MkExpression tag (ExpName name loc) typ dir)
                    sv
  | exec_expr_array_access: forall array headers size next idx idxsv idxv idxz header default_header this st tag typ dir,
                            exec_expr read_one_bit this st idx idxsv ->
                            sval_to_val read_one_bit idxsv idxv ->
                            array_access_idx_to_z idxv = Some idxz ->
                            exec_expr read_one_bit this st array (ValBaseStack headers size next) ->
                            uninit_sval_of_typ None typ = Some default_header ->
                            Znth_def idxz headers default_header = header ->
                            exec_expr read_one_bit this st
                            (MkExpression tag (ExpArrayAccess array idx) typ dir)
                            header
  | exec_expr_bitstring_access : forall bits bitssv bitsv bitsz wn lo loz hi hiz this st tag typ dir,
                                 exec_expr read_one_bit this st bits bitssv ->
                                 sval_to_val read_one_bit bitssv bitsv ->
                                 bitstring_slice_bits_to_z bitsv = Some (wn, bitsz) ->
                                 Z.of_N lo = loz ->
                                 Z.of_N hi = hiz ->
                                 loz <= hiz < (Z.of_N wn) ->
                                 exec_expr read_one_bit this st
                                 (MkExpression tag (ExpBitStringAccess bits lo hi) typ dir)
                                 (ValBaseBit (to_loptbool (hi - lo + 1)%N 
                                              (bitstring_slice bitsz loz hiz)))
  | exec_expr_list : forall es vs this st tag typ dir,
                     exec_exprs read_one_bit this st es vs ->
                     exec_expr read_one_bit this st
                     (MkExpression tag (ExpList es) typ dir)
                     (ValBaseTuple vs)
  | exec_expr_record : forall kvs kvs' this st tag typ dir,
                       AList.all_values (exec_expr read_one_bit this st) kvs kvs' ->
                       exec_expr read_one_bit this st
                       (MkExpression tag (ExpRecord kvs) typ dir)
                       (ValBaseRecord kvs')
  | exec_expr_unary_op : forall op arg argsv argv v sv this st tag typ dir,
                         exec_expr read_one_bit this st arg argsv ->
                         sval_to_val read_one_bit argsv argv ->
                         Ops.eval_unary_op op argv = Some v ->
                         val_to_sval v sv ->
                         exec_expr read_one_bit this st
                         (MkExpression tag (ExpUnaryOp op arg) typ dir)
                         sv
  | exec_expr_binary_op : forall op larg largsv largv rarg rargsv rargv v sv this st tag typ dir,
                          exec_expr read_one_bit this st larg largsv ->
                          exec_expr read_one_bit this st rarg rargsv ->
                          sval_to_val read_one_bit largsv largv ->
                          sval_to_val read_one_bit rargsv rargv ->
                          Ops.eval_binary_op op largv rargv = Some v ->
                          val_to_sval v sv ->
                          exec_expr read_one_bit this st
                          (MkExpression tag (ExpBinaryOp op (larg, rarg)) typ dir)
                          sv
  | exec_expr_cast : forall newtyp expr oldsv oldv newv newsv this st tag typ dir real_typ,
  (* We assume that get_real_type contains the real type corresponding to a
     type name so that we can use get the real type from it. *)
                     exec_expr read_one_bit this st expr oldsv ->
                     sval_to_val read_one_bit oldsv oldv ->
                     get_real_type newtyp = Some real_typ ->
                     Ops.eval_cast real_typ oldv = Some newv ->
                     val_to_sval newv newsv ->
                     exec_expr read_one_bit this st
                     (MkExpression tag (ExpCast newtyp expr) typ dir)
                     newsv
  (* No unspecified value possible from this expression *)
  | exec_expr_enum_member : forall tname member ename members this st tag typ dir,
                            name_to_type ge tname = Some (TypEnum ename None members) ->
                            List.In member members ->
                            exec_expr read_one_bit this st
                            (MkExpression tag (ExpTypeMember tname member) typ dir)
                            (ValBaseEnumField ename member)
  (* We need rethink about how to handle senum lookup. *)
  | exec_expr_senum_member : forall tname member ename etyp members fields sv this st tag typ dir,
                             name_to_type ge tname = Some (TypEnum ename (Some etyp) members) ->
                             IdentMap.get ename (ge_senum ge) = Some (ValBaseSenum fields) ->
                             AList.get fields member = Some sv ->
                             exec_expr read_one_bit this st
                             (MkExpression tag (ExpTypeMember tname member) typ dir)
                             (ValBaseSenumField ename member sv)
  | exec_expr_error_member : forall err this st tag typ dir,
                             exec_expr read_one_bit this st
                             (MkExpression tag (ExpErrorMember err) typ dir)
                             (ValBaseError err)
  | exec_expr_other_member : forall expr member sv sv' this st tag typ dir,
                             exec_expr read_one_bit this st expr sv ->
                             get_member sv member sv' ->
                             exec_expr read_one_bit this st
                             (MkExpression tag (ExpExpressionMember expr member) typ dir) sv'
  (* TODO:
     ValBaseHeader: setValid, setInvalid, isValid are supposed to be handled in exec_builtin
     ValBaseUnion: isValid is supposed to be handled in exec_builtin
     ValBaseStack: next, last, pop_front, push_front are supposed to be handled in exec_builtin *)
  | exec_expr_ternary : forall cond tru fls b sv sv' this st tag typ dir,
                        exec_expr read_one_bit this st cond sv ->
                        sval_to_val read_one_bit sv (ValBaseBool b) -> 
                        exec_expr read_one_bit this st (if b then tru else fls) sv' ->
                        exec_expr read_one_bit this st
                        (MkExpression tag (ExpTernary cond tru fls) typ dir)
                        sv'
  | exec_expr_dont_care : forall this st tag typ dir,
                          exec_expr read_one_bit this st
                          (MkExpression tag ExpDontCare typ dir)
                          ValBaseNull
with exec_exprs (read_one_bit : option bool -> bool -> Prop) : 
                path -> state -> list (@Expression tags_t) -> list Sval -> Prop :=
  | exec_exprs_nil : forall this st,
                     exec_exprs read_one_bit this st nil nil
  | exec_exprs_cons : forall this st expr es sv svs,
                      exec_expr read_one_bit this st expr sv ->
                      exec_exprs read_one_bit this st es svs ->
                      exec_exprs read_one_bit this st (expr :: es) (sv :: svs).

Inductive exec_expr_det (read_one_bit : option bool -> bool -> Prop) :
                        path -> (* temp_env -> *) state -> (@Expression tags_t) -> Val ->
                        (* trace -> *) (* temp_env -> *) (* state -> *) (* signal -> *) Prop :=
  | exec_expr_det_intro : forall this st expr sv v,
                          exec_expr read_one_bit this st expr sv ->
                          sval_to_val read_one_bit sv v ->
                          exec_expr_det read_one_bit this st expr v.

Inductive exec_exprs_det (read_one_bit : option bool -> bool -> Prop) : 
                         path -> (* temp_env -> *) state -> list (@Expression tags_t) -> list Val ->
                        (* trace -> *) (* temp_env -> *) (* state -> *) (* signal -> *) Prop :=
  | exec_exprs_det_intro : forall this st exprs svs vs,
                           exec_exprs read_one_bit this st exprs svs ->
                           svals_to_vals read_one_bit svs vs ->
                           exec_exprs_det read_one_bit this st exprs vs.

Inductive exec_expr_set (read_one_bit : option bool -> bool -> Prop)
                        : path -> (* temp_env -> *) state -> (@Expression tags_t) -> ValSet ->
                          (* trace -> *) (* temp_env -> *) (* state -> *) (* signal -> *) Prop :=
  | exec_expr_set_mask : forall expr exprv mask maskv this st tag typ dir,
                         exec_expr_det read_one_bit this st expr exprv ->
                         exec_expr_det read_one_bit this st mask maskv ->
                         exec_expr_set read_one_bit this st
                         (MkExpression tag (ExpMask expr mask) typ dir)
                         (ValSetMask exprv maskv)
  | exec_expr_set_range : forall lo lov hi hiv this st tag typ dir,
                          exec_expr_det read_one_bit this st lo lov ->
                          exec_expr_det read_one_bit this st hi hiv ->
                          exec_expr_set read_one_bit this st
                          (MkExpression tag (ExpRange lo hi) typ dir)
                          (ValSetRange lov hiv)
  | exec_expr_set_cast : forall newtyp expr oldv newv this st tag typ dir real_typ,
                         exec_expr_det read_one_bit this st expr oldv ->
                         get_real_type newtyp = Some real_typ ->
                         Ops.eval_cast_set real_typ oldv = Some newv ->
                         exec_expr_set read_one_bit this st
                         (MkExpression tag (ExpCast newtyp expr) typ dir)
                         newv.

(* A generic function for evaluating pure expressions. *)
Fixpoint eval_expr_gen (hook : Expression -> option Val) (expr : @Expression tags_t) : option Val :=
  match hook expr with
  | Some val => Some val
  | None =>
      match expr with
      | MkExpression _ expr _ _ =>
          match expr with
          | ExpInt i => Some (eval_p4int_val i)
          | ExpUnaryOp op arg =>
              match eval_expr_gen hook arg with
              | Some argv => Ops.eval_unary_op op argv
              | None => None
              end
          | ExpBinaryOp op (larg, rarg) =>
              match eval_expr_gen hook larg, eval_expr_gen hook rarg with
              | Some largv, Some rargv => Ops.eval_binary_op op largv rargv
              | _, _ => None
              end
          | ExpCast newtyp arg =>
              match eval_expr_gen hook arg, get_real_type newtyp with
              | Some argv, Some real_typ => Ops.eval_cast real_typ argv
              | _, _ => None
              end
          | ExpExpressionMember expr name =>
              match eval_expr_gen hook expr with
              | Some (ValBaseStruct fields) =>
                  AList.get fields name
              | Some (ValBaseHeader fields true) =>
                  AList.get fields name
              | _ => None
              end
          | _ => None
          end
      end
  end.

Definition eval_expr_gen_sound_1_statement read_one_bit st this hook expr v :=
  forall (H_hook : forall expr v, hook expr = Some v -> 
          exec_expr_det read_one_bit this st expr v),
  eval_expr_gen hook expr = Some v ->
  exec_expr_det read_one_bit this st expr v.

(* Lemma eval_expr_gen_sound_1 : forall read_one_bit st this hook expr v,
  eval_expr_gen_sound_1_statement read_one_bit st this hook expr v
with eval_expr_gen_sound_1_preT : forall read_one_bit st this hook tags expr typ dir v,
  eval_expr_gen_sound_1_statement read_one_bit st this hook (MkExpression tags expr typ dir) v.
Proof.
  - intros. destruct expr; apply eval_expr_gen_sound_1_preT.
  - unfold eval_expr_gen_sound_1_statement; intros.
    unfold eval_expr_gen in H0; fold eval_expr_gen in H0.
    destruct (hook (MkExpression tags expr typ dir)) as [v' | ] eqn:?.
    1 : apply H_hook. congruence.
    destruct expr; inversion H0.
    + repeat constructor.
    + destruct (eval_expr_gen _ _) eqn:? in H2; only 2 : inversion H2.
      econstructor; only 1 : eapply eval_expr_gen_sound_1; eassumption.
    + destruct args as [larg rarg].
      destruct (eval_expr_gen _ _) eqn:? in H2;
        only 1 : destruct (eval_expr_gen _ _) eqn:? in H2;
        only 2-3 : inversion H2.
      econstructor; only 1-2 : eapply eval_expr_gen_sound_1; eassumption.
    + destruct (eval_expr_gen _ _) eqn:? in H2; only 2 : inversion H2.
      destruct (get_real_type typ0) eqn:?; only 2 : inversion H2.
      econstructor; only 1 : eapply eval_expr_gen_sound_1; eassumption.
    + destruct (eval_expr_gen _ _) as [[] | ] eqn:? in H2; only 1-12, 15-20 : inversion H2.
      * econstructor; only 2 : econstructor; only 1 : eapply eval_expr_gen_sound_1; eassumption.
      * destruct is_valid; only 2 : discriminate.
        econstructor; only 1 : (eapply eval_expr_gen_sound_1; eassumption).
        constructor; constructor; assumption.
Qed. *)

Definition eval_expr_gen_sound_statement read_one_bit st this hook expr v :=
  forall (H_hook : forall expr v, hook expr = Some v -> 
          forall v', exec_expr_det read_one_bit this st expr v' -> 
          v' = v),
  eval_expr_gen hook expr = Some v ->
  forall v', exec_expr_det read_one_bit this st expr v' ->
    v' = v.

(* Lemma eval_expr_gen_sound : forall read_one_bit st this hook expr v,
  eval_expr_gen_sound_statement read_one_bit st this hook expr v
with eval_expr_gen_sound_preT : forall read_one_bit st this hook tags expr typ dir v,
  eval_expr_gen_sound_statement read_one_bit st this hook (MkExpression tags expr typ dir) v.
Proof.
  - intros. destruct expr; apply eval_expr_gen_sound_preT.
  - unfold eval_expr_gen_sound_statement; intros.
    unfold eval_expr_gen in H0; fold eval_expr_gen in H0.
    destruct (hook (MkExpression tags expr typ dir)) as [v'' | ] eqn:?.
    1 : eapply H_hook; only 2 : eassumption; congruence.
    destruct expr; inversion H0.
    + inversion H1; subst. reflexivity.
    + destruct (eval_expr_gen _ _) eqn:? in H3; only 2 : inversion H3.
      inversion H1; subst.
      assert (argv = v0) by (eapply eval_expr_gen_sound; eassumption).
      congruence.
    + destruct args as [larg rarg].
      destruct (eval_expr_gen _ _) eqn:? in H3;
        only 1 : destruct (eval_expr_gen _ _) eqn:? in H3;
        only 2-3 : inversion H3.
      inversion H1; subst.
      assert (largv = v0) by (eapply eval_expr_gen_sound; eassumption).
      assert (rargv = v1) by (eapply eval_expr_gen_sound; eassumption).
      congruence.
    + destruct (eval_expr_gen _ _) eqn:? in H3; only 2 : inversion H3.
      inversion H1; subst.
      assert (oldv = v0) by (eapply eval_expr_gen_sound; eassumption).
      destruct (get_real_type typ0) eqn:?; only 2 : inversion H3.
      congruence.
    + destruct (eval_expr_gen _ _) as [[] | ] eqn:H_eval_expr_gen in H3; only 1-12, 15-20 : inversion H3.
      * eapply eval_expr_gen_sound with (st := st) in H_eval_expr_gen; only 2 : eassumption.
        inversion H1; subst;
          lazymatch goal with
          | H : exec_expr _ _ expr _ |- _ =>
              apply H_eval_expr_gen in H;
              inversion H; subst
          end;
          lazymatch goal with
          | H : get_member _ _ _ _ |- _ =>
              inversion H; subst
          end.
        congruence.
      * eapply eval_expr_gen_sound with (st := st) in H_eval_expr_gen; only 2 : eassumption.
        inversion H1; subst;
          lazymatch goal with
          | H : exec_expr _ _ expr _ |- _ =>
              apply H_eval_expr_gen in H;
              inversion H; subst
          end;
          lazymatch goal with
          | H : get_member _ _ _ _ |- _ =>
              inversion H; subst
          end.
        destruct is_valid; only 2 : inversion H3.
        inversion H9; subst.
        congruence.
Qed. *)

(* We might want to prove this lemma in future. *)
(* Lemma eval_expr_gen_complete : forall st this expr v,
  exec_expr this st expr v ->
  eval_expr_gen (fun _ loc => loc_to_sval this loc st) expr = Some v. *)

Definition is_in (dir : direction) : bool :=
  match dir with
  | In | InOut => true
  | _ => false
  end.

Definition is_out (dir : direction) : bool :=
  match dir with
  | Out | InOut => true
  | _ => false
  end.

Definition is_pure_out (dir : direction) : bool :=
  match dir with
  | Out => true
  | _ => false
  end.

Definition filter_in {A} (params : list (A * direction)) : list A :=
  let f param :=
    if is_in (snd param) then [fst param] else [] in
  flat_map f params.

Definition filter_out {A} (params : list (A * direction)) : list A :=
  let f param :=
    if is_out (snd param) then [fst param] else [] in
  flat_map f params.

Definition filter_pure_out {A} (params : list (A * direction)) : list A :=
  let f param :=
    if is_pure_out (snd param) then [fst param] else [] in
  flat_map f params.

(* NOTE: We may need to modify for the call convention for overloaded functions. *)
Definition bind_parameters (params : list (path * direction)) (args : list Sval) (s s' : state) :=
  s' = update_memory (PathMap.sets (filter_in params) args) s.

(* NOTE: We may need to modify for the call convention for overloaded functions. *)
(* Definition extract_parameters (params : list (path * direction)) (args : list Val) (s : state) :=
  map Some args = PathMap.gets (filter_out params) (get_memory s). *)

Definition extract_parameters (paths : list path) (s : state) : option (list Sval) :=
  lift_option (PathMap.gets paths (get_memory s)).

Definition not_continue (s : signal) : bool :=
  match s with
  | SContinue => false
  | _ => true
  end.

Definition is_continue (s : signal) : bool :=
  match s with
  | SContinue => true
  | _ => false
  end.

Definition force_return_signal (sig : signal) : signal :=
  match sig with
  | SContinue => SReturnNull
  | _ => sig
  end. 

Definition force_continue_signal (sig : signal) : signal :=
  match sig with
  | SReturn _ => SContinue
  | _ => sig
  end.

Definition not_return (sig : signal) : bool :=
  match sig with
  | SReturn _ => false
  | _ => true
  end.

Definition is_return (sig : signal) : bool :=
  match sig with
  | SReturn _ => true
  | _ => false
  end.

Inductive get_return_val : signal -> Val -> Prop :=
  | get_return_val_intro : forall v, get_return_val (SReturn v) v.

Inductive get_return_sval : signal -> Sval -> Prop :=
  | get_return_sval_intro : forall v sv, 
                           val_to_sval v sv ->
                           get_return_sval (SReturn v) sv.


Fixpoint get_action (actions : list (@Expression tags_t)) (name : ident) : option (@Expression tags_t) :=
  match actions with
  | [] => None
  | action :: actions' =>
      match action with
      | MkExpression _ (ExpFunctionCall (MkExpression _ f _ _) _ _) _ _ =>
          match f with
          | ExpName (BareName fname) _ | ExpName (QualifiedName _ fname) _ =>
              if P4String.equivb name fname then
                  Some (action)
              else
                  get_action actions' name
          | _ => get_action actions' name
          end
      | _ => get_action actions' name
      end
  end.

Axiom dummy_type : @P4Type tags_t.
Definition dummy_tags := @default tags_t _.

Definition add_ctrl_args (oaction : option (@Expression tags_t)) 
                         (ctrl_args : list (option (@Expression tags_t))) : option (@Expression tags_t) :=
  match oaction with
  | Some action =>
      match action with
      | MkExpression _ (ExpFunctionCall f type_args args) _ dir =>
          Some (MkExpression dummy_tags (ExpFunctionCall f type_args (args ++ ctrl_args)) TypVoid dir)
      | _ => None
      end
  | None => None
  end.

Definition table_key_key (key : @TableKey tags_t) : (@Expression tags_t) :=
  match key with
  | MkTableKey _ e _ => e
  end.

Definition table_key_matchkind (key : @TableKey tags_t) : ident :=
  match key with
  | MkTableKey _ _ match_kind => match_kind
  end.

Definition get_entries (s : state) (table : path) (const_entries : option (list table_entry)) : (list table_entry) :=
  match const_entries with
  | Some entries => entries
  | None => extern_get_entries (get_external_state s) table
  end.

Inductive exec_match (read_one_bit : option bool -> bool -> Prop) : 
                     path -> state -> @Match tags_t -> ValSet -> Prop :=
  | exec_match_dont_care : forall this st tag typ,
                           exec_match read_one_bit this st (MkMatch tag MatchDontCare typ) ValSetUniversal
  | exec_match_expr : forall this st expr vs tag typ,
                      exec_expr_set read_one_bit this st expr vs ->
                      exec_match read_one_bit this st (MkMatch tag (MatchExpression expr) typ) vs.
  
Inductive exec_matches (read_one_bit : option bool -> bool -> Prop) :
                       path -> state -> list (@Match tags_t) -> list ValSet -> Prop :=
  | exec_matches_nil : forall this st,
                       exec_matches read_one_bit this st nil nil
  | exec_matches_cons : forall this st m ms sv svs,
                       exec_match read_one_bit this st m sv ->
                       exec_matches read_one_bit this st ms svs ->
                       exec_matches read_one_bit this st (m :: ms) (sv :: svs).

Inductive exec_table_entry (read_one_bit : option bool -> bool -> Prop) :
                           path -> state -> table_entry -> 
                           (@table_entry_valset tags_t (@Expression tags_t)) -> Prop :=
  | exec_table_entry_intro : forall this st ms svs action entryvs,
                             exec_matches read_one_bit this st ms svs ->
                             (if (List.length svs =? 1)%nat
                              then entryvs = (List.hd ValSetUniversal svs, action) 
                              else entryvs = (ValSetProd svs, action)) ->
                             exec_table_entry read_one_bit this st (mk_table_entry ms action) entryvs.
  
Inductive exec_table_entries (read_one_bit : option bool -> bool -> Prop) :
                             path -> state -> list table_entry -> 
                             list (@table_entry_valset tags_t (@Expression tags_t)) -> Prop :=
  | exec_table_entries_nil : forall this st,
                       exec_table_entries read_one_bit this st nil nil
  | exec_table_entries_cons : forall this st te tes tev tevs,
                       exec_table_entry read_one_bit this st te tev ->
                       exec_table_entries read_one_bit this st tes tevs ->
                       exec_table_entries read_one_bit this st (te :: tes) (tev :: tevs).

Inductive exec_table_match (read_one_bit : option bool -> bool -> Prop) :
                           path -> state -> ident -> option (list table_entry) -> option action_ref -> Prop :=
  | exec_table_match_intro : forall this_path name keys keyvals const_entries entryvs s matched_action,
      let entries := get_entries s (this_path ++ [name]) const_entries in
      let match_kinds := map table_key_matchkind keys in
      exec_exprs_det read_one_bit this_path s (map table_key_key keys) keyvals ->
      exec_table_entries read_one_bit this_path s entries entryvs ->
      extern_match (combine keyvals match_kinds) entryvs = matched_action ->
      exec_table_match read_one_bit this_path s name const_entries matched_action.


Definition is_some {A} (input: option A) : bool :=
  match input with
  | None => false
  | _ => true
  end.

Inductive inst_mem_val :=
  | IMVal (v : Val)
  (* Instances, including parsers, controls, and external objects. *)
  | IMInst (class : ident) (p : path).

Definition inst_mem := @PathMap.t tags_t inst_mem_val.

Definition lookup_func (this_path : path) (inst_m : inst_mem) (func : @Expression tags_t) : option (path * fundef) :=
  let ge := ge_func ge in
  (* We should think about using option monad in this function. *)
  match func with
  (* function/action *)
  | MkExpression _ (ExpName _ loc) _ _ =>
      match loc with
      | LGlobal p => option_map (fun fd => (nil, fd)) (PathMap.get p ge)
      | LInstance p =>
          match PathMap.get this_path inst_m with
          | Some (IMInst class_name _) =>
              option_map (fun fd => (this_path, fd)) (PathMap.get ([class_name] ++ p) ge)
          | _ => None
          end
      end
  (* apply/extern *)
  | MkExpression _ (ExpExpressionMember expr name) _ _ =>
      if P4String.equivb name !"apply" then
        match expr with
        (* Instances should only be referred with bare names. *)
        | MkExpression _ (ExpName _ loc) _ _ =>
            match loc with
            | LGlobal p => None (* TODO We need to confirm this branch is impposible. *)
            | LInstance p =>
                match PathMap.get (this_path ++ p) inst_m with
                | Some (IMInst class_name inst_path) =>
                    option_map (fun fd => (inst_path, fd)) (PathMap.get [class_name] ge)
                | _ => None
                end
            end
        | _ => None
        end
      (* If the method name is not apply, it is an external method. *)
      else
        match expr with
        (* Instances should only be referred with bare names. *)
        | MkExpression _ (ExpName _ loc) _ _ =>
            match loc with
            | LGlobal p => None (* TODO We need to confirm this branch is impposible. *)
            | LInstance p =>
                match PathMap.get (this_path ++ p) inst_m with
                | Some (IMInst class_name inst_path) =>
                    match PathMap.get [class_name; name] ge with
                    | Some fd => Some (inst_path, fd)
                    | None => None
                    end
                | _ => None
                end
            end
        | _ => None
        end
  | _ => None
  end.

Inductive exec_lexpr (read_one_bit : option bool -> bool -> Prop) :
                     path -> state -> (@Expression tags_t) -> Lval -> signal -> Prop :=
  | exec_lexpr_name : forall name loc this st tag typ dir,
                      exec_lexpr read_one_bit this st
                      (MkExpression tag (ExpName name loc) typ dir)
                      (MkValueLvalue (ValLeftName name loc) typ) SContinue
  | exec_lexpr_member : forall expr lv name this st tag typ dir sig,
                        P4String.equivb !"next" name = false ->
                        exec_lexpr read_one_bit this st expr lv sig ->
                        exec_lexpr read_one_bit this st
                        (MkExpression tag (ExpExpressionMember expr name) typ dir)
                        (MkValueLvalue (ValLeftMember lv name) typ) sig
  (* next < 0 is impossible by syntax. *)
  | exec_lexpr_member_next : forall expr lv headers size next this st tag typ dir sig ret_sig,
                             exec_lexpr read_one_bit this st expr lv sig ->
                             exec_expr read_one_bit this st expr (ValBaseStack headers size next) ->
                             (if (next <? size)%N then ret_sig = sig else ret_sig = (SReject StackOutOfBounds_str)) ->
                             exec_lexpr read_one_bit this st
                             (MkExpression tag (ExpExpressionMember expr !"next") typ dir)
                             (MkValueLvalue (ValLeftArrayAccess lv next) typ) ret_sig
  (* ATTN: lo and hi interchanged here *)
  | exec_lexpr_bitstring_access : forall bits lv lo hi wn bitsv bitsz this st tag typ dir sig,
                                   exec_lexpr read_one_bit this st bits lv sig ->
                                   exec_expr_det read_one_bit this st bits bitsv ->
                                   bitstring_slice_bits_to_z bitsv = Some (wn, bitsz) ->
                                   (lo <= hi < wn)%N ->
                                   exec_lexpr read_one_bit this st
                                   (MkExpression tag (ExpBitStringAccess bits lo hi) typ dir)
                                   (MkValueLvalue (ValLeftBitAccess lv hi lo) typ) sig
  (* Make negative idxz equal to size to stay out of bound as a nat idx.
     Write to out-of-bound indices l-values is handled in exec_write *)
  | exec_lexpr_array_access : forall array lv idx idxv idxz idxn headers next this st tag typ dir sig,
                               exec_lexpr read_one_bit this st array lv sig ->
                               exec_expr_det read_one_bit this st idx idxv ->
                               array_access_idx_to_z idxv = Some idxz ->
                               (if (idxz >=? 0) 
                                then idxn = Z.to_N idxz
                                else exec_expr read_one_bit this st array (ValBaseStack headers idxn next)) ->
                               exec_lexpr read_one_bit this st
                               (MkExpression tag (ExpArrayAccess array idx) typ dir)
                               (MkValueLvalue (ValLeftArrayAccess lv idxn) typ) sig.

Definition locator_equivb (loc1 loc2 : @Locator tags_t) : bool :=
  match loc1, loc2 with
  | LInstance p1, LInstance p2 => path_equivb p1 p2
  | LGlobal p1, LGlobal p2 => path_equivb p1 p2
  | _, _ => false
  end.

Fixpoint lval_equivb (lv1 lv2 : Lval) : bool :=
  match lv1, lv2 with
  | MkValueLvalue (ValLeftName _ loc1) _, MkValueLvalue (ValLeftName _ loc2) _ =>
      locator_equivb loc1 loc2
  | MkValueLvalue (ValLeftMember lv1 member1) _, MkValueLvalue (ValLeftMember lv2 member2) _ =>
      lval_equivb lv1 lv2 && P4String.equivb member1 member2
  | MkValueLvalue (ValLeftBitAccess lv1 msb1 lsb1) _, MkValueLvalue (ValLeftBitAccess lv2 msb2 lsb2) _ =>
      lval_equivb lv1 lv2 && N.eqb msb1 msb2 && N.eqb lsb1 lsb2
  | MkValueLvalue (ValLeftArrayAccess lv1 idx1) _, MkValueLvalue (ValLeftArrayAccess lv2 idx2) _ =>
      lval_equivb lv1 lv2 && N.eqb idx1 idx2
  | _, _ => false
  end.

Definition update_val_by_loc (this : path) (s : state) (loc : Locator) (sv : Sval): state :=
  let p := loc_to_path this loc in
  update_memory (PathMap.set p sv) s.

Inductive exec_read (this : path) : state -> Lval -> Sval -> Prop :=
  | exec_read_name : forall name loc st sv typ,
                       loc_to_sval this loc st = Some sv ->
                       exec_read this st (MkValueLvalue (ValLeftName name loc) typ) sv
  | exec_read_by_member : forall lv name st sv typ,
                         exec_read_member this st lv name typ sv ->
                         exec_read this st (MkValueLvalue (ValLeftMember lv name) typ) sv
  (* | exec_read_bit_access
     | exec_read_array_access *)

(* (ValLeftMember (ValBaseStack headers size) !"next") is guaranteed avoided
   by conversions in exec_lexpr to (ValLeftArrayAccess (ValBaseStack headers size) index). 
   Also, value here if derived from lvalue in the caller, so !"last" does not exist.  *)
with exec_read_member (this : path) : state -> Lval -> P4String -> P4Type -> Sval -> Prop :=
  | exec_read_member_header : forall is_valid fields st lv name typ sv,
                          exec_read this st lv (ValBaseHeader fields is_valid) ->
                          AList.get fields name = Some sv ->
                          exec_read_member this st lv name typ sv
  | exec_read_member_struct : forall fields st lv name typ sv,
                          exec_read this st lv (ValBaseStruct fields) ->
                          AList.get fields name = Some sv ->
                          exec_read_member this st lv name typ sv
  | exec_read_member_union: forall fields st lv name typ sv,
                        exec_read this st lv (ValBaseUnion fields) ->
                        AList.get fields name = Some sv ->
                        exec_read_member this st lv name typ sv.

(* TODO: write to the field of an invalid header in a union makes the possibly existing valid header
    take undefined value. It should be guaranteed there is at most one valid header in a union. *)
(* If any of these kinds of writes are performed:
    1. a write to a field in a currently invalid header, either a regular header or an element of 
       a header stack with an index that is in range, and that header is not part of a header_union
    2. a write to a field in an element of a header stack, where the index is out of range
   then that write must not change any state that is currently defined in the system...
   Guaranteed by not writing to invalid and unspecified-validity headers *)
Inductive write_header_field: Sval -> P4String -> Sval -> Sval -> Prop :=
  | write_header_field_valid : forall fields fname fv fields',
                               AList.set fields fname fv = Some fields' ->
                               write_header_field (ValBaseHeader fields (Some true)) fname fv
                               (ValBaseHeader fields' (Some true))
  | write_header_field_invalid : forall fields fname fv,
                                 write_header_field (ValBaseHeader fields (Some false)) fname fv
                                 (ValBaseHeader fields (Some false))
  (* Since valid = None only occurs for out-of-bound header stack access, and for that case 
     writing to lval is prevented by update_stack_header, this relation should never be hit. *)
  | write_header_field_undef : forall fields fname fv,
                                 write_header_field (ValBaseHeader fields None) fname fv
                                 (ValBaseHeader fields None).

(* More formally, if u is an expression whose type is a header union U with fields ranged over 
   by hi, then the following operations can be used to manipulate u:
   1. u.hi.setValid(): sets the valid bit for header hi to true and sets the valid bit 
                       for all other headers to false, which implies that reading these 
                       headers will return an unspecified value.
   2. u.hi.setInvalid(): if the valid bit for any member header of u is true then sets 
                         it to false, which implies that reading any member header of u 
                         will return an unspecified value.
   We can understand an assignment to a union u.hi = e as equivalent to 
   u.hi.setValid(); u.hi = e; if e is valid and
   u.hi.setInvalid(); otherwise.
   Consider a situation where a header_union u1 has member headers u1.h1 and u1.h2, and at a given 
   point in the program's execution u1.h1 is valid and u1.h2 is invalid. If a write is attempted 
   to a field of the invalid member header u1.h2, then any or all of the fields of the valid member 
   header u1.h1 may change as a result. Such a write must not change the validity of any member 
   headers of u1, nor any other state that is currently defined in the system.
   Guaranteed by:
   1. Typechecker ensures that fname must exist in the fields.
   2. Updating with an invalid header makes fields in all the headers unspecified (validity unchanged).
*)
Fixpoint update_union_member (fields: P4String.AList tags_t Sval) (fname: P4String)
                             (hfields: P4String.AList tags_t Sval) (is_valid: option bool) :
                             option (P4String.AList tags_t Sval) :=
  match fields with
  | [] => Some []
  | (fname', ValBaseHeader hfields' is_valid') :: tl =>
    match update_union_member tl fname hfields is_valid with
    | None => None
    | Some tl' =>
      match is_valid with
      | Some true => if P4String.equivb fname fname'
                     then Some ((fname, ValBaseHeader hfields (Some true)) :: tl')
                     else Some ((fname', ValBaseHeader hfields' (Some false)) :: tl')
      | Some false => if P4String.equivb fname fname'
                      then Some ((fname', ValBaseHeader hfields' (Some false)) :: tl')
                      else Some ((fname', ValBaseHeader (kv_map (uninit_sval_of_sval (Some false)) hfields') is_valid') :: tl')
      (* Since valid = None only occurs for out-of-bound header stack access, and hfields
         should be result of exec_expr, it should have been determinized at this point. *)
      | _ => None
      end
    end
  | _ :: _ => None
  end.

(* (ValLeftMember (ValBaseStack headers size) !"next") is guaranteed avoided
   by conversions in exec_lexpr to (ValLeftArrayAccess (ValBaseStack headers size) index).
   Also, value here if derived from lvalue in the caller, so !"last" does not exist. *)
Inductive update_member : Sval -> P4String -> Sval -> Sval -> Prop :=
  | update_member_header : forall fields is_valid fname fv sv,
                           write_header_field (ValBaseHeader fields is_valid) fname fv sv ->
                           update_member (ValBaseHeader fields is_valid) fname fv sv
  | update_member_struct : forall fields' fields fname fv,
                           AList.set fields fname fv = Some fields' ->
                           update_member (ValBaseStruct fields) fname fv (ValBaseStruct fields')
  | update_member_union : forall hfields (is_valid: bool) fields fields' is_valid fname,
                          update_union_member fields fname hfields is_valid = Some fields' ->
                          update_member (ValBaseUnion fields) fname (ValBaseHeader hfields is_valid)
                          (ValBaseUnion fields').

Definition update_stack_header (headers: list Sval) (idx: N) (v: Sval) : list Sval :=
  let fix update_stack_header' headers idx' v :=
    match headers, idx' with
    | header :: tl, O => v :: tl
    | header :: tl, S n => header :: (update_stack_header' tl n v)
    | [], _ => []
    end
  in update_stack_header' headers (N.to_nat idx) v.

Definition update_bitstring (bits : list (option bool)) (lsb : N) (msb : N) 
                          (nbits : list (option bool)) : list (option bool) :=
  let fix update_bitstring' (bits : list (option bool)) (lsb : nat) (msb : nat) 
                            (nbits : list (option bool)) :=
    match bits, lsb, msb, nbits with
    | hd :: tl, S lsb', S msb', _ => hd :: (update_bitstring' tl lsb' msb' nbits)
    | _ :: tl, O, S msb', nhd :: ntl => nhd :: (update_bitstring' tl lsb msb' ntl)
    | _, _, _, _ => bits
  end in update_bitstring' bits (N.to_nat lsb) (N.to_nat (msb + 1)) nbits.

(* Writing and updating happens all be in sval, so it requires converting the rhs val to sval beforehand *)
(* If any of these kinds of writes are performed:
    2.variant. a write to an element of a header stack, where the index is out of range
   then that write must not change any state that is currently defined in the system...
   Guaranteed by update_stack_header, if idx >= size, state is unchanged. *)
Inductive exec_write (this : path) : state -> Lval -> Sval -> state -> Prop :=
  | exec_write_name : forall name loc st rhs typ st',
                         update_val_by_loc this st loc rhs = st' ->
                         exec_write this st (MkValueLvalue (ValLeftName name loc) typ) rhs st'
  | exec_write_member : forall lv fname sv sv' st rhs typ st',
                           exec_read this st lv sv ->
                           update_member sv fname rhs sv' ->
                           exec_write this st lv sv' st' ->
                           exec_write this st (MkValueLvalue (ValLeftMember lv fname) typ) rhs st'
  | exec_write_bit_access_bit : forall lv bits nbits bits' lsb msb st typ st',
                                   exec_read this st lv (ValBaseBit bits) ->
                                   (lsb <= msb < Z.to_N (Zlength bits))%N ->
                                   update_bitstring bits lsb msb nbits = bits' ->
                                   exec_write this st lv (ValBaseBit bits') st' ->
                                   exec_write this st (MkValueLvalue (ValLeftBitAccess lv msb lsb) typ)
                                   (ValBaseBit nbits) st'
   | exec_write_bit_access_int : forall lv bits bits' lsb msb nbits st typ st',
                                   exec_read this st lv (ValBaseInt bits) ->
                                   (lsb <= msb < Z.to_N (Zlength bits))%N ->
                                   update_bitstring bits lsb msb nbits = bits' ->
                                   exec_write this st lv (ValBaseInt bits') st' ->
                                   exec_write this st (MkValueLvalue (ValLeftBitAccess lv msb lsb) typ)
                                   (ValBaseBit nbits) st'
  (* By update_stack_header, if idx >= size, state currently defined is unchanged. *)
  | exec_write_array_access : forall lv headers size next (idx: N) headers' st rhs typ st',
                                 exec_read this st lv (ValBaseStack headers size next) ->
                                 update_stack_header headers idx rhs = headers' ->
                                 exec_write this st lv (ValBaseStack headers' size next) st' ->
                                 exec_write this st (MkValueLvalue (ValLeftArrayAccess lv idx) typ) rhs st'.

Definition argument : Type := (option Sval) * (option Lval).

Definition get_arg_directions (func : @Expression tags_t) : list direction :=
  match func with
  | MkExpression _ _ (TypFunction (MkFunctionType _ params _ _)) _ =>
      map get_param_dir params
  | MkExpression _ _ (TypAction data_params ctrl_params) _ =>
      map get_param_dir data_params ++ map (fun _ => In) ctrl_params
  | _ => nil (* impossible *)
  end.

(* given expression and direction, evaluate to argument. *)
(* in -> (Some _, None) *)
(* out -> (None, Some _) *)
(* inout -> (Some _, Some _) *)
(* out parameters are, with a few exceptions listed below, uninitialized and are treated as l-values
   (See Section 6.6) within the body of the method or function...
   Direction out parameters are always initialized at the beginning of execution of the portion of 
   the program that has the out parameters, e.g. control, parser, action, function, etc. This 
   initialization is not performed for parameters with any direction that is not out.
      1. If a direction out parameter is of type header or header_union, it is set to “invalid”.
      2. If a direction out parameter is of type header stack, all elements of the header stack 
         are set to “invalid”, and its nextIndex field is initialized to 0 (see Section 8.17).
      3. If a direction out parameter is a compound type, e.g. a struct or tuple, other than 
         one of the types listed above, then apply these rules recursively to its members.
      4. If a direction out parameter has any other type, e.g. bit<W>, an implementation need 
         not initialize it to any predictable value.
*)
Inductive exec_arg (read_one_bit : option bool -> bool -> Prop) : 
                   path -> state -> option (@Expression tags_t) -> direction -> argument -> signal -> Prop :=
  | exec_arg_in : forall this st expr v sv,
                  exec_expr_det read_one_bit this st expr v ->
                  val_to_sval v sv ->
                  exec_arg read_one_bit this st (Some expr) In (Some sv, None) SContinue
  | exec_arg_out_dontcare : forall this st,
                            exec_arg read_one_bit this st None Out (None, None) SContinue
  | exec_arg_out : forall this st expr lv sig,
                   exec_lexpr read_one_bit this st expr lv sig ->
                   exec_arg read_one_bit this st (Some expr) Out (None, Some lv) sig
  | exec_arg_inout : forall this st expr lv sv v sv' sig,
                     exec_lexpr read_one_bit this st expr lv sig ->
                     exec_read this st lv sv ->
                     (* determinize sval similar to in parameters; why not exec_expr_det? *)
                     sval_to_val read_one_bit sv v ->
                     val_to_sval v sv' ->
                     exec_arg read_one_bit this st (Some expr) InOut (Some sv', Some lv) sig.

(* exec_arg on a list *)
Inductive exec_args (read_one_bit : option bool -> bool -> Prop) :
                    path -> state -> list (option (@Expression tags_t)) -> list direction -> list argument -> signal -> Prop :=
| exec_args_nil: forall p s,
                 exec_args read_one_bit p s nil nil nil SContinue
| exec_args_cons : forall p s exp exps dir dirs arg args sig sig' ret_sig,
                   exec_arg read_one_bit p s exp dir arg sig ->
                   exec_args read_one_bit p s exps dirs args sig' ->
                   (if is_continue sig then ret_sig = sig' else ret_sig = sig) ->
                   exec_args read_one_bit p s (exp :: exps) (dir :: dirs) (arg :: args) ret_sig.
(* After SimplExpr, sig here in fact can only be SReject.
   Todo: the current behavior is after getting a non-continue signal, all args are still evaluated.
         SimplExpr makes execution stops at the non-continue signal. Even though exec_args won't
         affect state, it is still good to make the two behavior consistent. *)
(* | exec_args_cons_other : forall p s exp exps dir dirs arg args sig sig',
                         exec_arg p s exp dir arg sig ->
                         not_continue sig = true ->
                         exec_args p s exps dirs args sig' ->
                         exec_args p s (exp :: exps) (dir :: dirs) (arg :: args) sig. *)

Inductive exec_write_option : path -> state -> option Lval -> Sval -> state -> Prop :=
| exec_write_option_some : forall p s lval sv s',
                           exec_write p s lval sv s' ->
                           exec_write_option p s (Some lval) sv s'
| exec_write_option_none : forall p s sv,
                           exec_write_option p s None sv s.

Inductive exec_writes_option : path -> state -> list (option Lval) -> list Sval -> state -> Prop :=
| exec_writes_option_nil : forall p s,
                           exec_writes_option p s nil nil s
| exec_writes_option_cons : forall p s1 s2 s3 lv lvs sv svs,
                            exec_write_option p s1 lv sv s2 ->
                            exec_writes_option p s2 lvs svs s3 ->
                            exec_writes_option p s1 (lv :: lvs) (sv :: svs) s3.

Definition extract_invals (args : list argument) : list Sval :=
  let f arg :=
    match arg with
    | (Some v, _) => [v]
    | (None, _) => []
    end in
  flat_map f args.

Definition extract_outlvals (dirs : list direction) (args : list argument) : list (option Lval) :=
  let f dirarg :=
    match dirarg with
    | (Out, (_, olv)) => [olv]
    | (InOut, (_, olv)) => [olv]
    | _ => []
    end in
  flat_map f (combine dirs args).

Definition direct_application_expression (typ : P4Type) : @Expression tags_t :=
  let name := get_type_name typ in
  MkExpression dummy_tags (ExpName (BareName name) (LInstance [name])) dummy_type (* TODO place the actual function type *)
  Directionless.

Definition empty_statement := (MkStatement dummy_tags StatEmpty StmUnit).
Definition empty_block := (BlockEmpty dummy_tags).

Fixpoint match_switch_case (member: P4String) (cases : list StatementSwitchCase) : Block :=
  let fix find_next_action cases :=
    match cases with
    | [] => empty_block
    | StatSwCaseAction _ _ code :: _ => code
    | _ :: tl => find_next_action tl
    end in
  match cases with
  | [] => empty_block
  | StatSwCaseAction _ (StatSwLabName _ label) code :: tl =>
    if P4String.equivb label member then code
    else match_switch_case member tl
  | StatSwCaseFallThrough _ (StatSwLabName _ label) :: tl =>
    if P4String.equivb label member then find_next_action tl
    else match_switch_case member tl
  | StatSwCaseAction _ (StatSwLabDefault _) code :: _ => code
  | StatSwCaseFallThrough _ (StatSwLabDefault _) :: _ => empty_block
  end.

Definition table_retv (b : bool) (ename member : P4String) : Val :=
  ValBaseStruct
  [(!"hit", ValBaseBool b);
   (!"miss", ValBaseBool (negb b));
   (!"action_run", ValBaseEnumField ename member)].

Definition name_only (name : Typed.name) : ident :=
  match name with
  | BareName name => name
  | QualifiedName _ name => name
  end.

Definition get_expr_name (expr : @Expression tags_t) : ident :=
  match expr with
  | MkExpression _ (ExpName name _) _ _  =>
      name_only name
  | _ => !""
  end.

Definition get_expr_func_name (expr : @Expression tags_t) : ident :=
  match expr with
  | MkExpression _ (ExpFunctionCall func _ _) _ _  =>
      get_expr_name func
  | _ => !""
  end.

(* ValBaseHeader: setValid, setInvalid, isValid are supposed to be handled in exec_builtin *)
(* The expression h.minSizeInBits() is defined for any value h that has a header type. 
   The expression is equal to the sum of the sizes of all of header h's fields in bits, 
   counting all varbit fields as length 0. An expression h.minSizeInBits() is a compile-time 
   constant with type int.
   The expression h.minSizeInBytes() is similar to h.minSizeInBits(), except that it returns 
   the total size of all of the header's fields in bytes, rounding up to the next whole number 
   of bytes if the header's size is not a multiple of 8 bits long. h.minSizeInBytes() is 
   equal to (h.minSizeInBits() + 7) >> 3. *)
(* ValBaseUnion: isValid is supposed to be handled in exec_builtin *)
(* u.isValid() returns true if any member of the header union u is valid, otherwise it returns false. *)
(* ValBaseStack: next, last, pop_front, push_front are supposed to be handled in exec_builtin *)
(* Calling the isValid() method on an element of a header stack, where the index is out of range, 
   returns an undefined boolean value, i.e., it is either true or false, but the specification 
   does not require one or the other, nor that a consistent value is returned across multiple such calls.*)
(* If any of these kinds of writes are performed:
   ... a method call of setValid() or setInvalid() on an element of a header stack, where the index is out of range
   then that write must not change any state that is currently defined in the system, neither in header 
   fields nor anywhere else. In particular, if an invalid header is involved in the write, it must remain invalid. *)
Inductive exec_builtin : path -> state -> Lval -> ident -> list Sval -> state -> signal -> Prop :=
  (* this_path s lv fname args s' sig *) (* TODO *)
  .


Inductive exec_stmt (read_one_bit : option bool -> bool -> Prop) :
                    path -> inst_mem -> state -> (@Statement tags_t) -> state -> signal -> Prop :=
  | exec_stmt_assign : forall lhs lv rhs v sv this_path inst_m st tags typ st' sig,
                        exec_expr_det read_one_bit this_path st rhs v ->
                        exec_lexpr read_one_bit this_path st lhs lv sig ->
                        val_to_sval v sv -> 
                        (if is_continue sig then exec_write this_path st lv sv st' else st' = st) ->
                        exec_stmt read_one_bit this_path inst_m st
                        (MkStatement tags (StatAssignment lhs rhs) typ) st' sig
  | exec_stmt_assign_func_call : forall lhs lv rhs sv this_path inst_m st tags typ st' st'' sig sig' ret_sig,
                                 exec_call read_one_bit this_path inst_m st rhs st' sig' ->
                                 exec_lexpr read_one_bit this_path st lhs lv sig ->
                                 (if not_continue sig then st'' = st /\ ret_sig = sig
                                  else if not_return sig' then st'' = st' /\ ret_sig = sig'
                                  else get_return_sval sig' sv /\ exec_write this_path st' lv sv st'' /\ ret_sig = SContinue) ->
                                 exec_stmt read_one_bit this_path inst_m st
                                 (MkStatement tags (StatAssignment lhs rhs) typ) st'' ret_sig
  | exec_stmt_method_call : forall this_path inst_m st tags func args typ st' sig sig',
                            exec_call read_one_bit this_path inst_m st
                              (MkExpression dummy_tags (ExpFunctionCall func nil args) TypVoid Directionless)
                              st' sig ->
                            force_continue_signal sig = sig' ->
                            exec_stmt read_one_bit this_path inst_m st
                            (MkStatement tags (StatMethodCall func nil args) typ) st' sig'
  | exec_stmt_direct_application : forall this_path inst_m st tags typ' args typ st' sig sig',
                                   exec_call read_one_bit this_path inst_m st
                                      (MkExpression dummy_tags
                                        (ExpFunctionCall (direct_application_expression typ') nil (map Some args)) TypVoid Directionless)
                                      st' sig ->
                                   force_continue_signal sig = sig' ->
                                   exec_stmt read_one_bit this_path inst_m st
                                   (MkStatement tags (StatDirectApplication typ' args) typ) st' sig'
  | exec_stmt_conditional_some_fls : forall cond tru fls b this_path inst_m st tags typ st' sig,
                                     exec_expr_det read_one_bit this_path st cond (ValBaseBool b) ->
                                     exec_stmt read_one_bit this_path inst_m st (if b then tru else fls) st' sig ->
                                     exec_stmt read_one_bit this_path inst_m st
                                     (MkStatement tags (StatConditional cond tru (Some fls)) typ) st' sig
  | exec_stmt_conditional_none_fls : forall cond tru b this_path inst_m st tags typ st' sig,
                                     exec_expr_det read_one_bit this_path st cond (ValBaseBool b) ->
                                     exec_stmt read_one_bit this_path inst_m st (if b then tru else empty_statement) st' sig ->
                                     exec_stmt read_one_bit this_path inst_m st
                                     (MkStatement tags (StatConditional cond tru None) typ) st SContinue
  | exec_stmt_block : forall block this_path inst_m st tags typ st' sig,
                      exec_block read_one_bit this_path inst_m st block st' sig ->
                      exec_stmt read_one_bit this_path inst_m st
                      (MkStatement tags (StatBlock block) typ) st' sig
  | exec_stmt_exit : forall this_path inst_m (st: state) tags typ st,
                     exec_stmt read_one_bit this_path inst_m st
                     (MkStatement tags StatExit typ) st SExit
  | exec_stmt_return_none : forall this_path inst_m (st: state) tags typ st,
                            exec_stmt read_one_bit this_path inst_m st
                            (MkStatement tags (StatReturn None) typ) st SReturnNull
  | exec_stmt_return_some : forall e v this_path inst_m (st: state) tags typ st,
                            exec_expr_det read_one_bit this_path st e v ->
                            exec_stmt read_one_bit this_path inst_m st
                            (MkStatement tags (StatReturn (Some e)) typ) st (SReturn v)
  | exec_stmt_empty : forall this_path inst_m (st: state) tags typ st,
                      exec_stmt read_one_bit this_path inst_m st
                      (MkStatement tags StatEmpty typ) st SContinue
  | exec_stmt_switch: forall e b ename member cases block typ dir this_path inst_m (st st': state) st'' tags tags' typ' st st' sig,
                      exec_call read_one_bit this_path inst_m st e st' (SReturn (table_retv b ename member)) ->
                      match_switch_case member cases = block ->
                      exec_block read_one_bit this_path inst_m st' block st'' sig ->
                      exec_stmt read_one_bit this_path inst_m st
                      (MkStatement tags (StatSwitch (MkExpression tags' (ExpExpressionMember e !"action_run") typ dir) cases) typ') st'' sig
  | exec_stmt_variable : forall typ' name e v sv loc this_path inst_m st tags typ st',
                         exec_expr_det read_one_bit this_path st e v ->
                         val_to_sval v sv ->
                         exec_write this_path st (MkValueLvalue (ValLeftName (BareName name) loc) typ') sv st' ->
                         exec_stmt read_one_bit this_path inst_m st
                         (MkStatement tags (StatVariable typ' name (Some e) loc) typ) st' SContinue
  | exec_stmt_variable_func_call : forall typ' name e sv loc this_path inst_m st tags typ st' st'' sig,
                                   exec_call read_one_bit this_path inst_m st e st' sig ->
                                   (if not_return sig then st'' = st'
                                   else get_return_sval sig sv 
                                        /\ exec_write this_path st' (MkValueLvalue (ValLeftName (BareName name) loc) typ') sv st'') ->
                                   exec_stmt read_one_bit this_path inst_m st
                                   (MkStatement tags (StatVariable typ' name (Some e) loc) typ) st'' (force_continue_signal sig)
  | exec_stmt_variable_undef : forall typ' name loc sv this_path inst_m st tags typ st',
                               uninit_sval_of_typ (Some false) typ' = Some sv ->
                               exec_write this_path st (MkValueLvalue (ValLeftName (BareName name) loc) typ') sv st' ->
                               exec_stmt read_one_bit this_path inst_m st
                               (MkStatement tags (StatVariable typ' name None loc) typ) st' SContinue
  | exec_stmt_constant: forall typ' name v sv loc this_path inst_m st tags typ st',
                        val_to_sval v sv ->
                        exec_write this_path st (MkValueLvalue (ValLeftName (BareName name) loc) typ') sv st' ->
                        exec_stmt read_one_bit this_path inst_m st
                        (MkStatement tags (StatConstant typ' name v loc) typ) st' SContinue
  (* StatInstantiation not considered yet *)

with exec_block (read_one_bit : option bool -> bool -> Prop) :
                path -> inst_mem -> state -> (@Block tags_t) -> state -> signal -> Prop :=
  | exec_block_nil : forall this_path inst_m st tags,
                     exec_block read_one_bit this_path inst_m st (BlockEmpty tags) st SContinue
  | exec_block_cons : forall stmt rest this_path inst_m st st' st'' sig sig',
                      (* This style is for avoiding backtracking *)
                      exec_stmt read_one_bit this_path inst_m st stmt st' sig ->
                      exec_block read_one_bit this_path inst_m st' 
                          (if is_continue sig then rest else empty_block) st'' sig' ->
                      exec_block read_one_bit this_path inst_m st (BlockCons stmt rest) st'' 
                          (if is_continue sig then sig' else sig)

with exec_call (read_one_bit : option bool -> bool -> Prop) :
               path -> inst_mem -> state -> (@Expression tags_t) -> state -> signal -> Prop :=
  | exec_call_builtin : forall this_path inst_m s tags tag' lhs fname tparams params typ' args typ dir argvals s' sig sig' sig'' lv,
      let dirs := map get_param_dir params in
      exec_lexpr read_one_bit this_path s lhs lv sig ->
      exec_args read_one_bit this_path s args dirs argvals sig' ->
      (if not_continue sig then s' = s /\ sig'' = sig 
       else if not_continue sig' then s' = s /\ sig'' = sig'
       else exec_builtin this_path s lv fname (extract_invals argvals) s' sig'') ->
      exec_call read_one_bit this_path inst_m s (MkExpression tags (ExpFunctionCall
          (MkExpression tag' (ExpExpressionMember lhs fname) (TypFunction (MkFunctionType tparams params FunBuiltin typ')) dir)
          nil args) typ dir) s' sig''

  (* eval the call expression:
       1. eval arguments;
       2. lookup the function to call;
       3. call the function by exec_funcall;
       4. write back out parameters.
  *)
  | exec_call_func : forall this_path inst_m s tags func targs args typ dir argvals obj_path fd outvals s' s'' sig sig' ret_s ret_sig,
      let dirs := get_arg_directions func in
      exec_args read_one_bit this_path s args dirs argvals sig ->
      lookup_func this_path inst_m func = Some (obj_path, fd) ->
      exec_func read_one_bit obj_path inst_m s fd targs (extract_invals argvals) s' outvals sig' ->
      exec_writes_option this_path s' (extract_outlvals dirs argvals) outvals s'' ->
      (if is_continue sig then ret_s = s'' /\ ret_sig = sig' else ret_s = s /\ ret_sig = sig) ->
      exec_call read_one_bit this_path inst_m s (MkExpression tags (ExpFunctionCall func targs args) typ dir)
      ret_s ret_sig
  (* The only example of non-continue signals during exec_args (after SimplExpr) is hd.extract(hdrs.next). *)
  (* | exec_call_other : forall this_path inst_m s tags func args typ dir argvals sig,
      let dirs := get_arg_directions func in
      exec_args this_path s args dirs argvals sig ->
      not_continue sig = true ->
      exec_call this_path inst_m s (MkExpression tags (ExpFunctionCall func nil args) typ dir) s sig *)

(* Only in/inout arguments in the first list Val and only out/inout arguments in the second list Val. *)
with exec_func (read_one_bit : option bool -> bool -> Prop) :
               path -> inst_mem -> state -> fundef -> list P4Type -> list Sval -> state -> list Sval -> signal -> Prop :=
  | exec_func_internal : forall obj_path inst_m s params init body args s''' args' s' s'' sig sig' sig'',
      bind_parameters (map (map_fst (fun param => loc_to_path obj_path param)) params) args s s' ->
      exec_block read_one_bit obj_path inst_m s' init  s'' sig ->
      is_continue sig = true ->
      exec_block read_one_bit obj_path inst_m s'' body s''' sig' ->
      force_return_signal sig' = sig'' ->
      extract_parameters (filter_out (map (map_fst (fun param => loc_to_path obj_path param)) params)) s''' = Some args'->
      exec_func read_one_bit obj_path inst_m s (FInternal params init body) nil args s''' args' sig''

  | exec_func_table_match : forall obj_path name inst_m keys actions actionref action_name retv ctrl_args action default_action const_entries s s',
      exec_table_match read_one_bit obj_path s name const_entries actionref ->
      (if is_some actionref
       then actionref = (Some (mk_action_ref action_name ctrl_args)) 
            /\ add_ctrl_args (get_action actions action_name) ctrl_args = Some action
            /\ retv = (SReturn (table_retv true !"" (get_expr_func_name action)))
       else action = default_action
            /\ retv = (SReturn (table_retv false !"" (get_expr_func_name default_action)))) ->
      exec_call read_one_bit obj_path inst_m s action s' SReturnNull ->
      exec_func read_one_bit obj_path inst_m s (FTable name keys actions (Some default_action) const_entries)
        nil nil s' nil retv

  (* This will not happen in the latest spec. *)
  (* | exec_func_table_noaction : forall obj_path name inst_m keys actions const_entries s,
      exec_table_match obj_path s name const_entries SReturnNull ->
      exec_func obj_path inst_m s (FTable name keys actions None const_entries) nil s nil None *)

  (* Todo: check in/inout/out & uninitialized args *)
  | exec_func_external : forall obj_path inst_m class_name name (* params *) m es es' targs args argvs argvs' args' sig,
      svals_to_vals read_one_bit args argvs ->
      exec_extern es class_name name obj_path targs argvs es' argvs' sig ->
      vals_to_svals argvs' args' ->
      exec_func read_one_bit obj_path inst_m (m, es) (FExternal class_name name (* params *)) targs args (m, es') args' sig.

(* Return the declaration whose name is [name]. *)
Fixpoint get_decl (rev_decls : list (@Declaration tags_t)) (name : ident) : (@Declaration tags_t) :=
  match rev_decls with
  | decl :: rev_decls' =>
      match decl with
      | DeclParser _ name' _ _ _ _ _
      | DeclControl _ name' _ _ _ _ _
      | DeclExternObject _ name' _ _
      | DeclPackageType _ name' _ _ =>
          if P4String.equivb name name' then
            decl
          else
            get_decl rev_decls' name
      | _ => get_decl rev_decls' name
      end
  | [] => DeclError dummy_tags nil (* Abuse DeclError to report not found. *)
  end.

Definition is_decl_extern_obj (decl : @Declaration tags_t) : bool :=
  match decl with
  | DeclExternObject _ _ _ _ => true
  | _ => false
  end.

Definition get_constructor_param_names (decl : @Declaration tags_t) : list ident :=
  match decl with
  | DeclParser _ _ _ _ constructor_params _ _
  | DeclControl _ _ _ _ constructor_params _ _
  | DeclPackageType _ _ _ constructor_params =>
      fold_right
          (fun param =>
            match param with
            | MkParameter _ _ _ _ name => cons name
            end
          )
          nil
          constructor_params
  | _ => nil
  end.

Axiom dummy_ident : ident.
Axiom dummy_val : Val.
Axiom dummy_inst_mem_val : inst_mem_val.

Definition get_type_name (typ : @P4Type tags_t) : ident :=
  match typ with
  | TypSpecializedType (TypTypeName (BareName type_name)) _ => type_name
  | TypTypeName (BareName type_name) => type_name
  | _ => dummy_ident
  end.

Definition get_type_params (typ : @P4Type tags_t) : list (@P4Type tags_t) :=
  match typ with
  | TypSpecializedType _ params => params
  | _ => nil
  end.

Definition ienv := @IdentMap.t tags_t inst_mem_val.

(* A trick to define mutually recursive functions. *)
Section instantiate_class_body.

Variable instantiate_class_body_rev_decls : forall (e : ienv) (class_name : ident) (p : path) (m : inst_mem)
      (s : extern_state), path * inst_mem * extern_state.

Section instantiate_expr'.

Variable instantiate_expr' : forall (rev_decls : list (@Declaration tags_t)) (e : ienv) (expr : @Expression tags_t)
      (p : path) (m : inst_mem) (s : extern_state), inst_mem_val * inst_mem * extern_state.

Definition extract_val (val : inst_mem_val) :=
  match val with
  | IMVal val => val
  | IMInst _ _ => dummy_val
  end.

Definition instantiate'' (rev_decls : list (@Declaration tags_t)) (e : ienv) (typ : @P4Type tags_t)
      (args : list (@Expression tags_t)) (p : path) (m : inst_mem) (s : extern_state) : inst_mem_val * inst_mem * extern_state :=
  let class_name := get_type_name typ in
  let decl := get_decl rev_decls class_name in
  (* params := nil if decl is an external object, but params is only used to name the instances. *)
  let params := get_constructor_param_names decl in
  let instantiate_arg (acc : list inst_mem_val * inst_mem * extern_state * list ident) arg :=
    let '(args, m, s, params) := acc in
    let '(arg, m, s) := instantiate_expr' rev_decls e arg (p ++ [hd dummy_ident params]) m s in
    (* O(n^2) time complexity here. *)
    (args ++ [arg], m, s, tl params) in
  let '(args, m, s) := fst (fold_left instantiate_arg args (nil, m, s, params)) in
  if is_decl_extern_obj decl then
    let m := PathMap.set p (IMInst class_name p) m in
    let type_params := get_type_params typ in
    let s := alloc_extern s class_name type_params p (map extract_val args) in
    (IMInst class_name p, m, s)
  else
    let e := IdentMap.sets params args e in
    let '(_, m, s) := instantiate_class_body_rev_decls e class_name p m s in
    (IMInst class_name p, m, s).

End instantiate_expr'.

Definition get_val_ienv (e : ienv) (name : Typed.name) : option Val :=
  match name with
  | BareName name =>
      match IdentMap.get name e with
      | Some (IMVal v) => Some v
      | _ => None
      end
  | _ => None
  end.

Definition eval_expr_ienv_hook (e : ienv) (expr : @Expression tags_t) : option Val :=
  match expr with
  | MkExpression _ (ExpName name _) _ _ => get_val_ienv e name
  | _ => None
  end.

(* The evaluation of value expressions during instantiation is based on eval_expr_gen. *)
(* And we convert the inst_mem into a mem (for efficiency, maybe need lazy evaluation in this conversion). *)

Fixpoint instantiate_expr' (rev_decls : list (@Declaration tags_t)) (e : ienv) (expr : @Expression tags_t) (p : path)
      (m : inst_mem) (s : extern_state) {struct expr} : inst_mem_val * inst_mem * extern_state :=
  let instantiate' := instantiate'' instantiate_expr' in
  match expr with
  | MkExpression _ (ExpName (BareName name) _) _ _ =>
      let inst := force dummy_inst_mem_val (IdentMap.get name e) in
      (inst, PathMap.set p inst m, s)
  | MkExpression _ (ExpNamelessInstantiation typ args) _ _ =>
      instantiate' rev_decls e typ args p m s
  | _ =>
      match eval_expr_gen (eval_expr_ienv_hook e) expr with
      | Some v => (IMVal v, m, s)
      | None => (dummy_inst_mem_val, m, s)
      end
  end.

Definition instantiate' :=
  instantiate'' instantiate_expr'.

Definition instantiate_decl' (rev_decls : list (@Declaration tags_t)) (e : ienv) (decl : @Declaration tags_t)
      (p : path) (m : inst_mem) (s : extern_state) : ienv * inst_mem * extern_state :=
  match decl with
  | DeclInstantiation _ typ args name _ =>
      let '(inst, m, s) := instantiate' rev_decls e typ args (p ++ [name]) m s in
      (IdentMap.set name inst e, m, s)
  | _ => (e, m, s)
  end.

Definition instantiate_decls' (rev_decls : list (@Declaration tags_t)) (e : ienv) (decls : list (@Declaration tags_t))
      (p : path) (m : inst_mem) (s : extern_state) : inst_mem * extern_state :=
  let instantiate_decl'' (ems : ienv * inst_mem * extern_state) (decl : @Declaration tags_t) : ienv * inst_mem * extern_state :=
    let '(e, m, s) := ems in instantiate_decl' rev_decls e decl p m s in
  let '(_, m, s) := fold_left instantiate_decl'' decls (e, m, s) in
  (m, s).

End instantiate_class_body.

Fixpoint get_direct_applications_stmt (stmt : @Statement tags_t) : list (@Declaration tags_t) :=
  match stmt with
  | MkStatement _ (StatDirectApplication typ _) _  =>
      [DeclInstantiation dummy_tags typ nil (get_type_name typ) None]
  | MkStatement _ (StatBlock block) _ => get_direct_applications_blk block
  | _ => []
  end
with get_direct_applications_blk (block : @Block tags_t) : list (@Declaration tags_t) :=
  match block with
  | BlockEmpty _ => []
  | BlockCons stmt block =>
      get_direct_applications_stmt stmt ++ get_direct_applications_blk block
  end.

Definition get_direct_applications_ps (ps : @ParserState tags_t) : list (@Declaration tags_t) :=
  concat (map get_direct_applications_stmt (get_parser_state_statements ps)).

(* TODO we need to evaluate constants in instantiation. *)

Definition packet_in_instance : inst_mem_val := (IMInst !"packet_in" !["packet_in"]).

Definition is_packet_in (param : @P4Parameter tags_t) : bool :=
  match param with
  | MkParameter _ _ typ _ _ =>
      match typ with
      | TypTypeName (BareName name) =>
          P4String.equivb name !"packet_in"
      | _ => false
      end
  end.

Definition packet_out_instance : inst_mem_val := (IMInst !"packet_out" !["packet_out"]).

Definition is_packet_out (param : @P4Parameter tags_t) : bool :=
  match param with
  | MkParameter _ _ typ _ _ =>
      match typ with
      | TypTypeName (BareName name) =>
          P4String.equivb name !"packet_out"
      | _ => false
      end
  end.

Definition inline_packet_in_packet_out (p : path) (m : inst_mem) (param : @P4Parameter tags_t) : inst_mem :=
  if is_packet_in param then
    PathMap.set (p ++ [get_param_name param]) packet_in_instance m
  else if is_packet_out param then
    PathMap.set (p ++ [get_param_name param]) packet_out_instance m
  else
    m.

Fixpoint instantiate_class_body (rev_decls : list (@Declaration tags_t)) (e : ienv) (class_name : ident) (p : path)
      (m : inst_mem) (s : extern_state) {struct rev_decls} : path * inst_mem * extern_state :=
  match rev_decls with
  | decl :: rev_decls' =>
      let instantiate_decls := instantiate_decls' (instantiate_class_body rev_decls') in
      match decl with
      | DeclParser _ class_name' _ params _ locals states =>
          if P4String.equivb class_name class_name' then
            let m := fold_left (inline_packet_in_packet_out p) params m in
            let locals := concat (map get_direct_applications_ps states) in
            let (m, s) := instantiate_decls rev_decls' e locals p m s in
            let m := PathMap.set p (IMInst class_name p) m in
            (p, m, s)
          else
            instantiate_class_body rev_decls' e class_name p m s
      | DeclControl _ class_name' _ params _ locals apply =>
          if P4String.equivb class_name class_name' then
            let m := fold_left (inline_packet_in_packet_out p) params m in
            let locals := locals ++ get_direct_applications_blk apply in
            let (m, s) := instantiate_decls rev_decls' e locals p m s in
            let m := PathMap.set p (IMInst class_name p) m in
            (p, m, s)
          else
            instantiate_class_body rev_decls' e class_name p m s
      | _ => instantiate_class_body rev_decls' e class_name p m s
      end
  | nil => (nil, m, s)
  end.

Definition instantiate_expr (rev_decls : list (@Declaration tags_t)) :=
  instantiate_expr' (instantiate_class_body rev_decls) rev_decls.

Definition instantiate (rev_decls : list (@Declaration tags_t)) :=
  instantiate' (instantiate_class_body rev_decls) rev_decls.

Definition instantiate_decl (rev_decls : list (@Declaration tags_t)) :=
  instantiate_decl' (instantiate_class_body rev_decls) rev_decls.

Definition instantiate_decls (rev_decls : list (@Declaration tags_t)) :=
  instantiate_decls' (instantiate_class_body rev_decls) rev_decls.

Fixpoint instantiate_global_decls' (decls : list (@Declaration tags_t)) (rev_decls : list (@Declaration tags_t))
      (e : ienv) (m : inst_mem) (s : extern_state) : inst_mem * extern_state :=
  match decls with
  | [] => (m, s)
  | decl :: decls' =>
      let '(e, m, s) := instantiate_decl rev_decls e decl nil m s in
      instantiate_global_decls' decls' (decl :: rev_decls) e m s
  end.

Definition instantiate_global_decls (decls : list (@Declaration tags_t)) :
      forall (m : inst_mem) (s: extern_state), inst_mem * extern_state :=
  instantiate_global_decls' decls nil IdentMap.empty.

Definition instantiate_prog (prog : @program tags_t) : inst_mem * extern_state :=
  match prog with
  | Program decls =>
      instantiate_global_decls decls PathMap.empty extern_empty
  end.

Definition BlockNil := BlockEmpty dummy_tags.

Definition BlockSingleton (stmt : @Statement tags_t) : @Block tags_t :=
  BlockCons stmt BlockNil.

Fixpoint process_locals (locals : list (@Declaration tags_t)) : @Block tags_t :=
  match locals with
  | [] => BlockNil
  | decl :: locals' =>
      let block' := process_locals locals' in
      match decl with
      | DeclVariable tags typ name init =>
          let stmt := MkStatement tags (StatVariable typ name init (LInstance [name])) StmUnit in
          BlockCons stmt block'
      | _ => block'
      end
  end.

Definition empty_func_type : @P4Type tags_t :=
  TypFunction (MkFunctionType nil nil FunParser TypVoid).

Definition load_parser_transition (p : path) (trans : @ParserTransition tags_t) : @Block tags_t :=
  match trans with
  | ParserDirect tags next =>
      let method := MkExpression dummy_tags (ExpName (BareName next) (LInstance [next])) empty_func_type Directionless in
      let stmt := MkStatement tags (StatMethodCall method nil nil) StmUnit in
      BlockSingleton stmt
  | ParserSelect _ _ _ => BlockNil (* TODO *)
  end.

Definition block_of_list_statement (stmts : list (@Statement tags_t)) : @Block tags_t :=
  list_statement_to_block dummy_tags stmts.

Definition load_parser_state (p : path) (ge : genv_func) (state : @ParserState tags_t) : genv_func :=
  match state with
  | MkParserState _ name body trans =>
      let body := block_app (block_of_list_statement body) (load_parser_transition p trans) in
      PathMap.set (p ++ [name]) (FInternal nil BlockNil body) ge
  end.

Definition reject_state :=
  let verify := (MkExpression dummy_tags (ExpName (BareName !"verify") (LGlobal !["verify"])) dummy_type Directionless) in
  let false_expr := (MkExpression dummy_tags (ExpBool false) TypBool Directionless) in
  let stmt := (MkStatement dummy_tags (StatMethodCall verify nil [Some false_expr]) StmUnit) in
  FInternal nil BlockNil (BlockSingleton stmt).

Definition is_directional (dir : direction) : bool :=
  match dir with
  | Directionless => false
  | _ => true
  end.

Definition action_param_to_p4param (param : @Locator tags_t * direction) : P4Parameter :=
  let (name, dir) := param in
  let dir :=
    match dir with
    | Directionless => In
    | _ => dir
    end in
  MkParameter false dir dummy_type None !"".

Definition unwrap_action_ref (p : path) (ge : genv_func) (ref : TableActionRef) : Expression :=
  match ref with
  | MkTableActionRef _ ref _ =>
      match ref with
      | MkTablePreActionRef name args =>
          let loc :=
            match name with
            | BareName id =>
                match PathMap.get (p ++ [id]) ge with
                | Some _ => LInstance [id]
                | None => LGlobal [id]
                end
            | QualifiedName p id => LGlobal (p ++ [id])
            end in
          let typ :=
            let ofd :=
              match loc with
              | LInstance p' => PathMap.get (p ++ p') ge
              | LGlobal p' => PathMap.get p' ge
              end in
            match ofd with
            | Some (FInternal params _ _) =>
                TypFunction (MkFunctionType nil (map action_param_to_p4param params) FunAction TypVoid)
            | _ => dummy_type (* impossible *)
            end in
          let func := MkExpression dummy_tags (ExpName name loc) typ Directionless in
          MkExpression dummy_tags (ExpFunctionCall func nil args) dummy_type Directionless
      end
  end.

Definition unwrap_action_ref2 (ref : TableActionRef) : (@action_ref tags_t Expression) :=
  match ref with
  | MkTableActionRef _ ref _ =>
      match ref with
      | MkTablePreActionRef name args =>
          let id :=
            match name with
            | BareName id => id
            | QualifiedName _ id => id
            end in
          mk_action_ref id args
      end
  end.

Definition unwrap_table_entry (entry : TableEntry) : table_entry :=
  match entry with
  | MkTableEntry _ matches action =>
      mk_table_entry matches (unwrap_action_ref2 action)
  end.

(* out parameters are, with a few exceptions listed below, uninitialized and are treated 
   as l-values (See Section 6.6) within the body of the method or function.…..
   Direction out parameters are always initialized at the beginning of execution of the portion 
   of the program that has the out parameters, e.g. control, parser, action, function, etc. 
   This initialization is not performed for parameters with any direction that is not out.
      1. If a direction out parameter is of type header or header_union, it is set to “invalid”.
      2. If a direction out parameter is of type header stack, all elements of the header stack
         are set to “invalid”, and its nextIndex field is initialized to 0 (see Section 8.17).
      3. If a direction out parameter is a compound type, e.g. a struct or tuple, other than
         one of the types listed above, then apply these rules recursively to its members.
      4. If a direction out parameter has any other type, e.g. bit<W>, an implementation need
         not initialize it to any predictable value.
*)
Fixpoint uninit_out_parames (params: list (ident * P4Type)) : Block :=
  match params with
  | [] => BlockNil
  | param :: params' =>
      let block := uninit_out_parames params' in
      let (name, typ) := param in
      let stmt := MkStatement dummy_tags (StatVariable typ name None (LInstance [name])) StmUnit in
      BlockCons stmt block
  end.

Fixpoint load_decl (p : path) (ge : genv_func) (decl : @Declaration tags_t) : genv_func :=
  match decl with
  | DeclParser _ name type_params params constructor_params locals states =>
      let params := map get_param_name_dir params in
      let params := map (map_fst (fun param => LInstance [param])) params in
      let params := List.filter (compose is_directional snd) params in
      let ge := fold_left (load_decl (p ++ [name])) locals ge in
      let init := process_locals locals in
      let ge := fold_left (load_parser_state (p ++ [name])) states ge in
      let ge := PathMap.set (p ++ !["accept"]) (FInternal nil BlockNil BlockNil) ge in
      let ge := PathMap.set (p ++ !["reject"]) (FInternal nil BlockNil BlockNil) ge in
      let method := MkExpression dummy_tags (ExpName (BareName !"begin") (LInstance !["begin"]))
                    empty_func_type Directionless in
      let stmt := MkStatement dummy_tags (StatMethodCall method nil nil) StmUnit in
      PathMap.set (p ++ [name]) (FInternal params init (BlockSingleton stmt)) ge
  | DeclControl _ name type_params params _ locals apply =>
      let params := map get_param_name_dir params in
      let params := map (map_fst (fun param => LInstance [param])) params in
      let params := List.filter (compose is_directional snd) params in
      let ge := fold_left (load_decl (p ++ [name])) locals ge in
      let init := process_locals locals in
      PathMap.set (p ++ [name]) (FInternal params init apply) ge
  | DeclFunction _ _ name type_params params body =>
      let out_params := filter_pure_out (map (fun p => (get_param_name_typ p, get_param_dir p)) params) in
      let init := uninit_out_parames out_params in
      let params := map get_param_name_dir params in
      let params := map (map_fst (fun param => LGlobal [name; param])) params in
      PathMap.set (p ++ [name]) (FInternal params init body) ge
  | DeclExternFunction _ _ name _ _ =>
      PathMap.set (p ++ [name]) (FExternal !"" name) ge
  | DeclExternObject _ name _ methods =>
      let add_method_prototype ge' method :=
        match method with
        | ProtoMethod _ _ mname _ _ =>
            PathMap.set (p ++ [name; mname]) (FExternal name mname) ge'
        | _ => ge
        end
      in fold_left add_method_prototype methods ge
  | DeclAction _ name params ctrl_params body =>
      let out_params := filter_pure_out (map (fun p => (get_param_name_typ p, get_param_dir p)) params) in
      let init := uninit_out_parames out_params in
      let params := map get_param_name_dir params in
      let ctrl_params := map (fun name => (name, In)) (map get_param_name ctrl_params) in
      let combined_params :=
        if path_equivb p [] then
          map (map_fst (fun param => LGlobal [name; param])) (params ++ ctrl_params)
        else
          map (map_fst (fun param => LInstance [name; param])) (params ++ ctrl_params) in
      PathMap.set (p ++ [name]) (FInternal combined_params init body) ge
  | DeclTable _ name keys actions entries default_action _ _ =>
      let table :=
        FTable name keys (map (unwrap_action_ref p ge) actions) (option_map (unwrap_action_ref p ge) default_action)
            (option_map (map unwrap_table_entry) entries) in
      PathMap.set (p ++ [name]) table ge
  | _ => ge
  end.

Definition load_prog (prog : @program tags_t) : genv_func :=
  match prog with
  | Program decls => fold_left (load_decl nil) decls PathMap.empty
  end.

Definition conv_decl_field (fild: DeclarationField):
    (P4String.t tags_t * @P4Type tags_t) :=
  match fild with | MkDeclarationField tags typ name => (name, typ) end.

Definition conv_decl_fields (l: list DeclarationField): P4String.AList tags_t P4Type :=
  fold_right (fun fild l' => cons (conv_decl_field fild) l') nil l.

Definition get_decl_typ_name (decl: @Declaration tags_t): option P4String :=
  match decl with
  | DeclHeader _ name _
  | DeclHeaderUnion _ name _
  | DeclStruct _ name _
  | DeclControlType _ name _ _
  | DeclParserType _ name _ _
  | DeclPackageType _ name _ _
  | DeclTypeDef _ name _
  | DeclNewType _ name _ => Some name
  | _ => None
  end.

(* TODO: Do we need to consider duplicated type names? *)
Fixpoint add_to_genv_typ (ge_typ: genv_typ)
         (decl: @Declaration tags_t): option genv_typ :=
  match decl with
  | DeclHeader tags name fields =>
    Some (IdentMap.set name (TypHeader (conv_decl_fields fields)) ge_typ)
  | DeclHeaderUnion tags name fields =>
    Some (IdentMap.set name (TypHeaderUnion (conv_decl_fields fields)) ge_typ)
  | DeclStruct tags name fields =>
    Some (IdentMap.set name (TypStruct (conv_decl_fields fields)) ge_typ)
  | DeclControlType tags name type_params params =>
    Some (IdentMap.set name (TypControl (MkControlType type_params params)) ge_typ)
  | DeclParserType tags name type_params params =>
    Some (IdentMap.set name (TypParser (MkControlType type_params params)) ge_typ)
  (* TODO: DeclPackageType and TypPackage are inconsistency *)
  | DeclPackageType tags name type_params params =>
    Some (IdentMap.set name (TypPackage type_params nil params) ge_typ)
  (* TODO: Do we need to consider the difference between DeclTypeDef
     and DeclNewType?*)
  | DeclTypeDef tags name (inl typ)
  | DeclNewType tags name (inl typ) =>
    match typ with
    | TypTypeName name2 => match name_to_type ge_typ name2 with
                           | Some typ2 => Some (IdentMap.set name typ2 ge_typ)
                           | None => None
                           end
    | _ => Some (IdentMap.set name typ ge_typ)
    end
  | DeclTypeDef tags name (inr decl2)
  | DeclNewType tags name (inr decl2) =>
    match add_to_genv_typ ge_typ decl2 with
    | Some ge_typ2 => match get_decl_typ_name decl2 with
                      | Some name2 =>
                        match IdentMap.get name2 ge_typ2 with
                        | Some typ2 => Some (IdentMap.set name typ2 ge_typ2)
                        | None => None
                        end
                      | None => None
                      end
    | None => None
    end
  | _ => None
  end.

Fixpoint add_decls_to_ge_typ (oge_typ: option genv_typ)
         (l: list (@Declaration tags_t)): option genv_typ :=
  match l with
  | nil => oge_typ
  | decl :: rest =>
    match oge_typ with
    | Some ge_typ => add_decls_to_ge_typ (add_to_genv_typ ge_typ decl) rest
    | None => None
    end
  end.

Definition gen_ge_typ (prog : @program tags_t) : option genv_typ :=
  match prog with
  | Program l =>
    add_decls_to_ge_typ (Some IdentMap.empty) l
  end.

(* TODO this is a dummy function. This should be implemented at the same time as instantiation-time evaluation. *)
Definition gen_ge_senum (prog : @program tags_t) : genv_senum :=
  match prog with
  | Program l => IdentMap.empty
  end.

Definition gen_ge (prog : @program tags_t) : genv :=
  let ge_func := load_prog prog in
  let ge_typ := force IdentMap.empty (gen_ge_typ prog) in
  let ge_senum := gen_ge_senum prog in
  MkGenv ge_func ge_typ ge_senum.

End Semantics.
