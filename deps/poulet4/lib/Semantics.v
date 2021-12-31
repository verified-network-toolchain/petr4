Require Import Coq.Strings.String Coq.Bool.Bool
        Coq.ZArith.BinInt Coq.ZArith.ZArith
        Coq.Lists.List Coq.Program.Program
        Coq.ssr.ssrbool
        Poulet4.Typed Poulet4.Syntax.
Require Export Poulet4.Value Poulet4.ValueUtil.
Require Import Poulet4.P4String Poulet4.P4Int Poulet4.P4Arith
        Poulet4.AList Poulet4.Ops Poulet4.Maps.
Require Export Poulet4.Target Poulet4.SyntaxUtil VST.zlist.Zlist.
Require Import Poulet4.P4Notations.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.

Section Semantics.

Context {tags_t: Type} {inhabitant_tags_t : Inhabitant tags_t}.
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).
Notation ValSet := (@ValueSet tags_t).
Notation Lval := (@ValueLvalue tags_t).

Notation ident := string.
Notation path := (list ident).
Notation P4Int := (P4Int.t tags_t).

Context {target : @Target tags_t (@Expression tags_t)}.

Definition mem := PathMap.t Sval.

Definition state : Type := mem * extern_state.

Definition set_memory m (s : state) : state :=
  let (_, es) := s in (m, es).

Definition update_memory (f : mem -> mem) (s : state) : state :=
  let (m, es) := s in (f m, es).

Definition get_memory (s : state) : mem :=
  let (m, _) := s in m.

Definition get_external_state (s : state) :=
  let (_, es) := s in es.

Definition clear_list (p: list (@P4String.t tags_t)): list string :=
  map (@str tags_t) p.

Definition loc_to_path (this : path) (loc : Locator) : path :=
  match loc with
  | LGlobal p => p
  | LInstance p => this ++ p
  end.

Definition get_loc_path (loc : Locator) : path :=
  match loc with
  | LGlobal p => p
  | LInstance p => p
  end.

Variant fundef :=
  | FInternal
      (params : list (path * direction))
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

Definition genv_func := PathMap.t fundef.
Definition genv_typ := IdentMap.t (@P4Type tags_t).
Definition genv_senum := IdentMap.t (StringAList Sval).

Inductive inst_ref :=
  | mk_inst_ref (class : string) (p : path).

Definition genv_inst := PathMap.t inst_ref.
Definition genv_const := PathMap.t Val.

Record genv := MkGenv {
  ge_func :> genv_func;
  ge_typ :> genv_typ;
  ge_senum :> genv_senum;
  ge_inst :> genv_inst;
  ge_const :> genv_const;
  ge_ext :> extern_env
}.

Section WithGenv.

Variable ge : genv.

Fixpoint get_real_type (typ: @P4Type tags_t): option (@P4Type tags_t) :=
  let fix get_real_types (typs: list (@P4Type tags_t)):
    option (list (@P4Type tags_t)) :=
    match typs with
    | [] => Some []
    | a :: rest => match get_real_type a with
                   | None => None
                   | Some reala => match get_real_types rest with
                                   | Some realrest => Some (reala :: realrest)
                                   | None => None
                                   end
                   end
    end in
  let fix get_real_alist (fields: P4String.AList tags_t P4Type):
    option (P4String.AList tags_t P4Type) :=
    match fields with
    | [] => Some []
    | (a, t) :: rest =>
        match get_real_type t with
        | None => None
        | Some realt => match get_real_alist rest with
                        | Some realrest => Some ((a, realt) :: realrest)
                        | None => None
                        end
        end
    end in
  let get_real_param (param: P4Parameter): option P4Parameter :=
    match param with
    | MkParameter opt dir typ argid var =>
        match get_real_type typ with
        | Some realt => Some (MkParameter opt dir realt argid var)
        | None => None
        end
    end in
  let fix get_real_params (params: list P4Parameter) : option (list P4Parameter) :=
    match params with
    | [] => Some []
    | p :: rest => match get_real_param p with
                   | Some realp => match get_real_params rest with
                                   | Some realrest => Some (realp :: realrest)
                                   | None => None
                                   end
                   | None => None
                   end
    end in
  let get_real_ctrl (ctrl: ControlType): option ControlType :=
    match ctrl with
    | MkControlType type_params params =>
        match get_real_params params with
        | Some realps => Some (MkControlType type_params realps)
        | None => None
        end
    end in
  let get_real_func (fn: FunctionType): option FunctionType :=
    match fn with
    | MkFunctionType type_params params kind ret =>
        match get_real_type ret with
        | None => None
        | Some realret => match get_real_params params with
                          | Some realps => Some (MkFunctionType type_params realps kind realret)
                          | None => None
                          end
        end
    end in
  match typ with
  | TypTypeName name => IdentMap.get (str name) (ge_typ ge)
  | TypArray atyp size => match get_real_type atyp with
                          | Some realtyp => Some (TypArray atyp size)
                          | None => None
                          end
  | TypTuple types => match get_real_types types with
                      | Some realtypes => Some (TypTuple realtypes)
                      | None => None
                      end
  | TypList types => match get_real_types types with
                      | Some realtypes => Some (TypList realtypes)
                      | None => None
                     end
  | TypRecord fields => match get_real_alist fields with
                        | Some realfs => Some (TypRecord realfs)
                        | None => None
                        end
  | TypSet elt_type => match get_real_type elt_type with
                       | Some realt => Some (TypSet realt)
                       | None => None
                       end
  | TypHeader fields => match get_real_alist fields with
                        | Some realfs => Some (TypHeader realfs)
                        | None => None
                        end
  | TypHeaderUnion fields => match get_real_alist fields with
                             | Some realfs => Some (TypHeaderUnion realfs)
                             | None => None
                             end
  | TypStruct fields => match get_real_alist fields with
                        | Some realfs => Some (TypStruct realfs)
                        | None => None
                        end
  | TypEnum name (Some atyp) members => match get_real_type atyp with
                                        | Some realt => Some (TypEnum name (Some realt) members)
                                        | None => None
                                        end
  | TypNewType _ atyp => get_real_type atyp
  | TypControl ctrl => match get_real_ctrl ctrl with
                       | Some realcs => Some (TypControl realcs)
                       | None => None
                       end
  | TypParser ctrl => match get_real_ctrl ctrl with
                      | Some realcs => Some (TypParser realcs)
                      | None => None
                      end
  | TypFunction fn => match get_real_func fn with
                      | Some realfn => Some (TypFunction realfn)
                      | None => None
                      end
  | TypAction data_params ctrl_params =>
      match get_real_params data_params with
      | None => None
      | Some datas => match get_real_params ctrl_params with
                      | None => None
                      | Some ctrls => Some (TypAction datas ctrls)
                      end
      end
  | TypPackage typeps wildcards params =>
      match get_real_params params with
      | None => None
      | Some reals => Some (TypPackage typeps wildcards reals)
      end
  | TypSpecializedType base args =>
      match get_real_type base with
      | None => None
      | Some realb => match get_real_types args with
                      | None => None
                      | Some realargs => Some (TypSpecializedType realb realargs)
                      end
      end
  | TypConstructor typeps wildcards params ret =>
      match get_real_type ret with
      | None => None
      | Some realret => match get_real_params params with
                        | None => None
                        | Some rps => Some (TypConstructor typeps wildcards rps realret)
                        end
      end
  | TypBool => Some TypBool
  | TypString => Some TypString
  | TypInteger => Some TypInteger
  | TypInt w => Some (TypInt w)
  | TypBit w => Some (TypBit w)
  | TypVarBit w => Some (TypVarBit w)
  | TypError => Some TypError
  | TypMatchKind => Some TypMatchKind
  | TypVoid => Some TypVoid
  | TypExtern e => Some (TypExtern e)
  | TypEnum a None b => Some (TypEnum a None b)
  | TypTable a => Some (TypTable a)
  end.

Fixpoint eval_literal (expr: @Expression tags_t) : option Val :=
  let '(MkExpression _ expr _ _) := expr in
  match expr with
  | ExpBool b => Some (ValBaseBool b)
  | ExpInt i =>
    Some (match i.(width_signed) with
          | None => ValBaseInteger i.(value)
          | Some (w, false) => ValBaseBit (to_lbool w i.(value))
          | Some (w, true) => ValBaseInt (to_lbool w i.(value))
          end)
  | ExpString s => Some (ValBaseString (str s))
  | ExpErrorMember t => Some (ValBaseError (str t))
  | ExpList es =>
    let fix eval_literals  (exprs: list (@Expression tags_t)) : option (list Val) :=
        match exprs with
        | expr :: exprs' =>
          match eval_literal expr, eval_literals exprs' with
          | Some v, Some vs => Some (v :: vs)
          | _, _ => None
          end
        | [] => Some []
        end
    in
    option_map ValBaseTuple (eval_literals es)
  | ExpRecord fs =>
    let fix eval_literals  (kvs: @P4String.AList tags_t Expression)
        : option (StringAList Val) :=
        match kvs with
        | (k, e) :: kvs' =>
          match eval_literal e, eval_literals kvs' with
          | Some v, Some vs => Some ((str k, v) :: vs)
          | _, _ => None
          end
        | [] => Some []
        end
    in
    option_map ValBaseStruct (eval_literals fs)
  | _ => None
  end.

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

Definition loc_to_sval (loc : Locator) (s : state) : option Sval :=
  match loc with
  | LInstance p =>
      PathMap.get p (get_memory s)
  | LGlobal p =>
      None
  end.

Fixpoint array_access_idx_to_z (v : Val) : (option Z) :=
  match v with
  | ValBaseInt bits => Some (snd (BitArith.from_lbool bits))
  | ValBaseBit bits => Some (snd (IntArith.from_lbool bits))
  | ValBaseInteger value => Some value
  (* added in v1.2.2 *)
  | ValBaseSenumField _ _ value => array_access_idx_to_z value
  | _ => None
  end.

Definition sval_to_bits_width {A} (v : @ValueBase A) : option (list A * nat) :=
  match v with
  | ValBaseInt bits
  | ValBaseBit bits => Some (bits, List.length bits)
  | _ => None
  end.

Definition bitstring_slice {A} (bits: list A) (lo : nat) (hi : nat) : list A :=
  let fix bitstring_slice' (bits: list A) (lo : nat) (hi : nat) (slice: list A) :=
    match bits, lo, hi with
    | _ ::tl, S lo', S hi' => bitstring_slice' tl lo' hi' slice
    | hd::tl, O, S hi' => bitstring_slice' tl O hi' (hd::slice)
    | hd::tl, O, O => hd::slice
    | _, _, _ => slice
    end
  in List.rev (bitstring_slice' bits lo hi []).

(* The following reads give unspecified values:
    1. reading a field from a header that is currently invalid.
    2. reading a field from a header that is currently valid, but the field has not been initialized
       since the header was last made valid.
  So in order to guarantee these, we must maintain a global invariant that all invalid/undef headers'
  (including invalid members of header unions) contents must be undefined. For example, when setting
  a header to invalid, all the fields should be turned undefined, and when setting a header to valid,
  the fields should remain undefined. *)
Inductive get_member : Sval -> string -> Sval -> Prop :=
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
  | get_member_stack_size : forall headers next,
                            get_member (ValBaseStack headers next) "size"
                              (ValBaseBit (to_loptbool 32%N (Zlength headers)))
  | get_member_stack_last_index : forall headers next sv,
                                  (if (next =? 0)%N
                                    then uninit_sval_of_typ None (TypBit 32%N) = Some sv
                                    else sv = (ValBaseBit (to_loptbool 32%N (Z.of_N (next - 1))))) ->
                                  get_member (ValBaseStack headers next) "lastIndex" sv.

Definition is_directional (dir : direction) : bool :=
  match dir with
  | Directionless => false
  | _ => true
  end.

Definition loc_to_val_const (this : path) (loc : Locator) : option Val :=
  match loc with
  | LInstance p =>
      PathMap.get (this ++ p) (ge_const ge)
  | LGlobal p =>
      PathMap.get p (ge_const ge)
  end.

Definition loc_to_sval_const (this : path) (loc : Locator) : option Sval :=
  option_map eval_val_to_sval (loc_to_val_const this loc).

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
                       (ValBaseString (str s))
  | exec_expr_name_var : forall name loc sv this st tag typ dir,
                         is_directional dir = true ->
                         loc_to_sval loc st = Some sv ->
                         exec_expr read_one_bit this st
                         (MkExpression tag (ExpName name loc) typ dir)
                         sv
  | exec_expr_name_const : forall name loc sv this st tag typ dir,
                           is_directional dir = false ->
                           loc_to_sval_const this loc = Some sv ->
                           exec_expr read_one_bit this st
                           (MkExpression tag (ExpName name loc) typ dir)
                           sv
  | exec_expr_array_access: forall array headers next idx idxsv idxv idxz header default_header this st tag typ rtyp dir,
                            exec_expr read_one_bit this st idx idxsv ->
                            sval_to_val read_one_bit idxsv idxv ->
                            array_access_idx_to_z idxv = Some idxz ->
                            exec_expr read_one_bit this st array (ValBaseStack headers next) ->
                            get_real_type typ = Some rtyp ->
                            uninit_sval_of_typ None rtyp = Some default_header ->
                            Znth (d := default_header) idxz headers = header ->
                            exec_expr read_one_bit this st
                            (MkExpression tag (ExpArrayAccess array idx) typ dir)
                            header
  | exec_expr_bitstring_access : forall bits bitssv bitsbl wn lo lonat hi hinat this st tag typ dir,
                                 exec_expr read_one_bit this st bits bitssv ->
                                 sval_to_bits_width bitssv = Some (bitsbl, wn) ->
                                 N.to_nat lo = lonat ->
                                 N.to_nat hi = hinat ->
                                 (lonat <= hinat < wn)%nat ->
                                 exec_expr read_one_bit this st
                                 (MkExpression tag (ExpBitStringAccess bits lo hi) typ dir)
                                 (ValBaseBit (bitstring_slice bitsbl lonat hinat))
  | exec_expr_list : forall es vs this st tag typ dir,
      Forall2 (exec_expr read_one_bit this st) es vs ->
                     exec_expr read_one_bit this st
                     (MkExpression tag (ExpList es) typ dir)
                     (ValBaseTuple vs)
  | exec_expr_record : forall kvs kvs' this st tag typ dir,
                       AList.all_values (exec_expr read_one_bit this st) (clear_AList_tags kvs) kvs' ->
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
                            IdentMap.get (str tname) (ge_typ ge) = Some (TypEnum ename None members) ->
                            List.In member members ->
                            exec_expr read_one_bit this st
                            (MkExpression tag (ExpTypeMember tname member) typ dir)
                            (ValBaseEnumField (str ename) (str member))
  (* We need rethink about how to handle senum lookup. *)
  | exec_expr_senum_member : forall tname member ename etyp members fields sv this st tag typ dir,
                             IdentMap.get (str tname) (ge_typ ge) = Some (TypEnum ename (Some etyp) members) ->
                             IdentMap.get (str ename) (ge_senum ge) = Some fields ->
                             AList.get fields (str member) = Some sv ->
                             exec_expr read_one_bit this st
                             (MkExpression tag (ExpTypeMember tname member) typ dir)
                             (ValBaseSenumField (str ename) (str member) sv)
  | exec_expr_error_member : forall err this st tag typ dir,
                             exec_expr read_one_bit this st
                             (MkExpression tag (ExpErrorMember err) typ dir)
                             (ValBaseError (str err))
  | exec_expr_other_member : forall expr member sv sv' this st tag typ dir,
                             exec_expr read_one_bit this st expr sv ->
                             get_member sv (str member) sv' ->
                             exec_expr read_one_bit this st
                             (MkExpression tag (ExpExpressionMember expr member) typ dir) sv'
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
                          ValBaseNull.

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
      Forall2 (exec_expr read_one_bit this st) exprs svs ->
                           svals_to_vals read_one_bit svs vs ->
                           exec_exprs_det read_one_bit this st exprs vs.

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
                  AList.get fields (str name)
              | Some (ValBaseHeader fields true) =>
                  AList.get fields (str name)
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

Definition get_return_val (sig : signal) : option Val :=
  match sig with
  | SReturn v => Some v
  | _ => None
  end.

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
              if String.eqb name (str fname) then
                  Some action
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
  | MkTableKey _ _ match_kind => str match_kind
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
  | exec_match_mask : forall expr exprv mask maskv this st tag typ,
                      exec_expr_det read_one_bit this st expr exprv ->
                      exec_expr_det read_one_bit this st mask maskv ->
                      exec_match read_one_bit this st
                      (MkMatch tag (MatchMask expr mask) typ)
                      (ValSetMask exprv maskv)
  | exec_match_range : forall lo lov hi hiv this st tag typ,
                        exec_expr_det read_one_bit this st lo lov ->
                        exec_expr_det read_one_bit this st hi hiv ->
                        exec_match read_one_bit this st
                        (MkMatch tag (MatchRange lo hi) typ)
                        (ValSetRange lov hiv)
  | exec_match_cast : forall newtyp expr oldv newv this st tag typ real_typ,
                      exec_expr_det read_one_bit this st expr oldv ->
                      get_real_type newtyp = Some real_typ ->
                      Ops.eval_cast_set real_typ oldv = Some newv ->
                      exec_match read_one_bit this st
                      (MkMatch tag (MatchCast newtyp expr) typ)
                      newv.

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

Definition is_some : forall {A} (input: option A), bool := @ssrbool.isSome.

(* Look up function definition (fundef) and the path on which the function should be executed.
  Return None if failed.
  Return Some (None, fd) if the function should be executed on the current path. *)
Definition lookup_func (this_path : path) (func : @Expression tags_t) : option (option path * fundef) :=
  let ge_func := ge_func ge in
  let ge_inst := ge_inst ge in
  (* We should think about using option monad in this function. *)
  match func with
  (* function/action/parser transition *)
  | MkExpression _ (ExpName _ loc) _ _ =>
      match loc with
      | LGlobal p => option_map (fun fd => (Some nil, fd)) (PathMap.get p ge_func)
      | LInstance p =>
          match PathMap.get this_path ge_inst with
          | Some (mk_inst_ref class_name _) =>
              option_map (fun fd => (None, fd)) (PathMap.get ([class_name] ++ p) ge_func)
          | _ => None
          end
      end
  (* apply/extern *)
  | MkExpression _ (ExpExpressionMember expr name) _ _ =>
      match expr with
      | MkExpression _ (ExpName _ loc) _ _ =>
          match loc with
          | LGlobal p =>
              match PathMap.get p ge_inst with
              | Some (mk_inst_ref class_name inst_path) =>
                  match PathMap.get [class_name; str name] ge_func with
                  | Some fd => Some (Some inst_path, fd)
                  | None => None
                  end
              | None => None
              end
          | LInstance p =>
              match PathMap.get (this_path ++ p) ge_inst with
              | Some (mk_inst_ref class_name inst_path) =>
                  match PathMap.get [class_name; str name] ge_func with
                  | Some fd => Some (Some inst_path, fd)
                  | None => None
                  end
              | None => None
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
                        String.eqb (P4String.str name) "next" = false ->
                        exec_lexpr read_one_bit this st expr lv sig ->
                        exec_lexpr read_one_bit this st
                        (MkExpression tag (ExpExpressionMember expr name) typ dir)
                        (MkValueLvalue (ValLeftMember lv (str name)) typ) sig
  (* next < 0 is impossible by syntax. *)
  | exec_lexpr_member_next : forall expr lv name headers size next this st tag typ dir sig ret_sig,
                             String.eqb (P4String.str name) "next" = true ->
                             exec_lexpr read_one_bit this st expr lv sig ->
                             exec_expr read_one_bit this st expr (ValBaseStack headers next) ->
                             (if (next <? size)%N then ret_sig = sig else ret_sig = (SReject "StackOutOfBounds")) ->
                             exec_lexpr read_one_bit this st
                             (MkExpression tag (ExpExpressionMember expr name) typ dir)
                             (MkValueLvalue (ValLeftArrayAccess lv next) typ) ret_sig
  (* ATTN: lo and hi interchanged here *)
  | exec_lexpr_bitstring_access : forall bits lv lo hi wn bitsv bitsbl this st tag typ dir sig,
                                   exec_lexpr read_one_bit this st bits lv sig ->
                                   exec_expr_det read_one_bit this st bits bitsv ->
                                   sval_to_bits_width bitsv = Some (bitsbl, wn) ->
                                   (lo <= hi < N.of_nat wn)%N ->
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
                                else exec_expr read_one_bit this st array (ValBaseStack headers next)) ->
                               exec_lexpr read_one_bit this st
                               (MkExpression tag (ExpArrayAccess array idx) typ dir)
                               (MkValueLvalue (ValLeftArrayAccess lv idxn) typ) sig.

Definition update_val_by_loc (s : state) (loc : Locator) (sv : Sval): state :=
  let p := get_loc_path loc in
  update_memory (PathMap.set p sv) s.

(* Nominal fields like "next" are not addressible, so they cannot be fields in lvalues. When evaluating
  lvalues, they are converted to addressible lvalues. So they are not considered in exec_read and
  exec_write. *)

Inductive exec_read : state -> Lval -> Sval -> Prop :=
  | exec_read_name : forall name loc sv st typ,
                     loc_to_sval loc st = Some sv ->
                     exec_read st (MkValueLvalue (ValLeftName name loc) typ) sv
  | exec_read_by_member : forall lv name st sv typ sv',
                          exec_read st lv sv ->
                          get_member sv name sv' ->
                          exec_read st (MkValueLvalue (ValLeftMember lv name) typ) sv'
  (* Since the conditions are already checked in exec_lexpr, they are perhaps not necessary here. *)
  | exec_read_bit_access : forall bitssv bitsbl wn lo lonat hi hinat lv st typ,
                           exec_read st lv bitssv ->
                           sval_to_bits_width bitssv = Some (bitsbl, wn) ->
                           N.to_nat lo = lonat ->
                           N.to_nat hi = hinat ->
                           (lonat <= hinat < wn)%nat ->
                           exec_read st (MkValueLvalue (ValLeftBitAccess lv hi lo) typ)
                             (ValBaseBit (bitstring_slice bitsbl lonat hinat))
  | exec_read_array_access: forall lv headers next default_header header idx st typ rtyp,
                            exec_read st lv (ValBaseStack headers next) ->
                            get_real_type typ = Some rtyp ->
                            uninit_sval_of_typ None rtyp = Some default_header ->
                            Znth (d := default_header) (Z.of_N idx) headers = header ->
                            exec_read st (MkValueLvalue (ValLeftArrayAccess lv idx) typ) header.

(* If any of these kinds of writes are performed:
    1. a write to a field in a currently invalid header, either a regular header or an element of
       a header stack with an index that is in range, and that header is not part of a header_union
    2. a write to a field in an element of a header stack, where the index is out of range
   then that write must not change any state that is currently defined in the system...
   Guaranteed by not writing to invalid and unspecified-validity headers *)
Inductive write_header_field: Sval -> string -> Sval -> Sval -> Prop :=
  | write_header_field_valid : forall fields fname fv fields',
                               AList.set fields fname fv = Some fields' ->
                               write_header_field (ValBaseHeader fields (Some true)) fname fv
                               (ValBaseHeader fields' (Some true))
  | write_header_field_invalid : forall fields fname fv fields',
                                 (* It's safe to use (uninit_sval_of_sval None) here because there's no nested headers. *)
                                 AList.set fields fname (uninit_sval_of_sval None fv) = Some fields' ->
                                 write_header_field (ValBaseHeader fields (Some false)) fname fv
                                 (ValBaseHeader fields' (Some false))
  (* is_valid = None only during an out-of-bounds header stack access. This constructor is only used when
    writing to a[n].x that n is out of bounds. *)
  | write_header_field_undef : forall fields fname fv fields',
                               (* It's safe to use (uninit_sval_of_sval None) here because there's no nested headers. *)
                               AList.set fields fname (uninit_sval_of_sval None fv) = Some fields' ->
                               write_header_field (ValBaseHeader fields None) fname fv
                               (ValBaseHeader fields' None).

(*  Writing to a field of an invalid header in a union makes the possibly existing valid header
    take undefined value. It should be guaranteed there is at most one valid header in a union.
    Guaranteed by:
    1. Writing to the field of an invalid header in a union will first execute write_header_field,
       which does not change such a header.
    2. Writing an invalid header into a union happens in update_union_member, which converts
       all headers to invalid. *)
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

Fixpoint update_union_member (fields: StringAList Sval) (fname: string)
                             (hfields: StringAList Sval) (is_valid: option bool) :
                             option (StringAList Sval) :=
  match fields with
  | [] => Some []
  | (fname', ValBaseHeader hfields' is_valid') :: tl =>
    match update_union_member tl fname hfields is_valid with
    | None => None
    | Some tl' =>
      if String.eqb fname fname' then
        Some ((fname, ValBaseHeader hfields is_valid) :: tl')
      else
        let new_is_valid' :=
          match is_valid with
          | Some true => Some false
          | Some false => is_valid'
          (* is_valid = None should be impossible. A header member of a header union should never have
            None validity bit. is_valid = None only for an out-of-bounds header stack access. *)
          | _ => is_valid'
          end in
        (* It's safe to use (uninit_sval_of_sval None) here because there's no nested headers. *)
        Some ((fname', ValBaseHeader (kv_map (uninit_sval_of_sval None) hfields') new_is_valid') :: tl')
    end
  | _ :: _ => None
  end.

Inductive update_member : Sval -> string -> Sval -> Sval -> Prop :=
  | update_member_struct : forall fields' fields fname fv,
                           AList.set fields fname fv = Some fields' ->
                           update_member (ValBaseStruct fields) fname fv (ValBaseStruct fields')
  | update_member_header : forall fields is_valid fname fv sv,
                           write_header_field (ValBaseHeader fields is_valid) fname fv sv ->
                           update_member (ValBaseHeader fields is_valid) fname fv sv
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

Fixpoint update_bitstring {A} (bits : list A) (lo : nat) (hi : nat)
                              (nbits : list A) : list A :=
  match bits, lo, hi, nbits with
  | hd::tl, S lo', S hi', _ => hd :: (update_bitstring tl lo' hi' nbits)
  | _::tl, O, S hi', nhd::ntl => nhd :: (update_bitstring tl lo hi' ntl)
  | _::tl, O, O, [nhd] => nhd :: tl
  | _, _, _, _ => bits
  end.

(* Writing and updating happens all be in sval, so it requires converting the rhs val to sval beforehand *)
(* If any of these kinds of writes are performed:
    2.variant. a write to an element of a header stack, where the index is out of range
   then that write must not change any state that is currently defined in the system...
   Guaranteed by update_stack_header, if idx >= size, state is unchanged. *)
Inductive exec_write : state -> Lval -> Sval -> state -> Prop :=
  | exec_write_name : forall name loc st rhs typ st',
      update_val_by_loc st loc rhs = st' ->
      exec_write st (MkValueLvalue (ValLeftName name loc) typ) rhs st'
  | exec_write_member : forall lv fname sv sv' st rhs typ st',
      exec_read st lv sv ->
      update_member sv fname rhs sv' ->
      exec_write st lv sv' st' ->
      exec_write st (MkValueLvalue (ValLeftMember lv fname) typ) rhs st'
  | exec_write_bit_access_bit : forall lv bits bits' lo lonat hi hinat st typ st',
                                exec_read st lv (ValBaseBit bits) ->
                                N.to_nat lo = lonat ->
                                N.to_nat hi = hinat ->
                                (lonat <= hinat < List.length bits)%nat ->
                                update_bitstring bits lonat hinat bits = bits' ->
                                exec_write st lv (ValBaseBit bits') st' ->
                                exec_write st (MkValueLvalue (ValLeftBitAccess lv hi lo) typ)
                                  (ValBaseBit bits') st'
   | exec_write_bit_access_int : forall lv bits bits' lo lonat hi hinat st typ st',
                                  exec_read st lv (ValBaseInt bits) ->
                                  N.to_nat lo = lonat ->
                                  N.to_nat hi = hinat ->
                                  (lonat <= hinat < List.length bits)%nat ->
                                  update_bitstring bits lonat hinat bits = bits' ->
                                  exec_write st lv (ValBaseInt bits') st' ->
                                  exec_write st (MkValueLvalue (ValLeftBitAccess lv hi lo) typ)
                                    (ValBaseBit bits') st'
  (* By update_stack_header, if idx >= size, state currently defined is unchanged. *)
  | exec_write_array_access : forall lv headers next (idx: N) headers' st rhs typ st',
                              exec_read st lv (ValBaseStack headers next) ->
                              update_stack_header headers idx rhs = headers' ->
                              exec_write st lv (ValBaseStack headers' next) st' ->
                              exec_write st (MkValueLvalue (ValLeftArrayAccess lv idx) typ) rhs st'.

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
                     exec_read st lv sv ->
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

Inductive exec_write_option : state -> option Lval -> Sval -> state -> Prop :=
| exec_write_option_some : forall s lval sv s',
                           exec_write s lval sv s' ->
                           exec_write_option s (Some lval) sv s'
| exec_write_option_none : forall s sv,
                           exec_write_option s None sv s.

Inductive exec_write_options : state -> list (option Lval) -> list Sval -> state -> Prop :=
| exec_write_options_nil : forall s,
                           exec_write_options s nil nil s
| exec_write_options_cons : forall s1 s2 s3 lv lvs sv svs,
                            exec_write_option s1 lv sv s2 ->
                            exec_write_options s2 lvs svs s3 ->
                            exec_write_options s1 (lv :: lvs) (sv :: svs) s3.

(* NOTE: We may need to modify for the call convention for overloaded functions. *)
Definition exec_func_copy_in (params : list (path * direction)) (args : list Sval) (s : state) : state :=
  update_memory (PathMap.sets (filter_in params) args) s.

(* NOTE: We may need to modify for the call convention for overloaded functions. *)
Definition exec_func_copy_out (params : list (path * direction)) (s : state) : option (list Sval) :=
  lift_option (PathMap.gets (filter_out params) (get_memory s)).

Definition exec_call_copy_out (args : list (option Lval * direction)) (vals : list Sval) (s s' : state) : Prop :=
  exec_write_options s (filter_out args) vals s'.

Definition extract_invals (args : list argument) : list Sval :=
  let f arg :=
    match arg with
    | (Some v, _) => [v]
    | (None, _) => []
    end in
  flat_map f args.

Definition direct_application_expression (typ : P4Type) : @Expression tags_t :=
  let name := get_type_name typ in
  MkExpression dummy_tags (ExpName (BareName name) (LInstance [str name])) dummy_type (* TODO place the actual function type *)
  Directionless.

Definition empty_statement := (MkStatement dummy_tags StatEmpty StmUnit).
Definition empty_block := (BlockEmpty dummy_tags).

Fixpoint match_switch_case (member: string) (cases : list StatementSwitchCase) : Block :=
  let fix find_next_action cases :=
    match cases with
    | [] => empty_block
    | StatSwCaseAction _ _ code :: _ => code
    | _ :: tl => find_next_action tl
    end in
  match cases with
  | [] => empty_block
  | StatSwCaseAction _ (StatSwLabName _ label) code :: tl =>
    if String.eqb (str label) member then code
    else match_switch_case member tl
  | StatSwCaseFallThrough _ (StatSwLabName _ label) :: tl =>
    if String.eqb (str label) member then find_next_action tl
    else match_switch_case member tl
  | StatSwCaseAction _ (StatSwLabDefault _) code :: _ => code
  | StatSwCaseFallThrough _ (StatSwLabDefault _) :: _ => empty_block
  end.

Definition table_retv (b : bool) (ename member : string) : Val :=
  ValBaseStruct
  [("hit", ValBaseBool b);
   ("miss", ValBaseBool (negb b));
   ("action_run", ValBaseEnumField ename member)].

Definition name_only (name : @Typed.name tags_t) : ident :=
  match name with
  | BareName name => str name
  | QualifiedName _ name => str name
  end.

Definition get_expr_name (expr : @Expression tags_t) : ident :=
  match expr with
  | MkExpression _ (ExpName name _) _ _  =>
      name_only name
  | _ => ""
  end.

Definition get_expr_func_name (expr : @Expression tags_t) : ident :=
  match expr with
  | MkExpression _ (ExpFunctionCall func _ _) _ _  =>
      get_expr_name func
  | _ => ""
  end.

(* isValid() is supported by headers and header unions. If u is a header union, u.isValid() returns true
  if any member of the header union u is valid, otherwise it returns false. *)
Inductive exec_isValid (read_one_bit : option bool -> bool -> Prop) : Sval -> bool -> Prop :=
| exec_isValid_header : forall fields valid_bit is_valid,
    read_one_bit valid_bit is_valid ->
    exec_isValid read_one_bit (ValBaseHeader fields valid_bit) is_valid
| exec_isValid_union : forall fields valid_bits,
    Forall2 (exec_isValid read_one_bit) (map snd fields) valid_bits ->
    exec_isValid read_one_bit (ValBaseUnion fields)
      (fold_left orb valid_bits false).

Definition dummy_val {bit} : (@ValueBase bit) := ValBaseNull.
Global Opaque dummy_val.
Global Instance Inhabitant_ValueBase {bit} : Inhabitant (@ValueBase bit) := dummy_val.

Definition push_front (headers : list Sval) (next : N) (count : Z) : Sval :=
  let size := Zlength headers in
  let headers' :=
    if (count <=? size)%Z then
      Zrepeat (uninit_sval_of_sval (Some false) (Znth 0 headers)) count
        ++ sublist 0 (size - count) headers
    else
      Zrepeat (uninit_sval_of_sval (Some false) (Znth 0 headers)) size
  in
  let next' := Z.to_N (Z.of_N next + count) in
  ValBaseStack headers' next'.

Definition pop_front (headers : list Sval) (next : N) (count : Z) : Sval :=
  let size := Zlength headers in
  let headers' :=
    if (count <=? size)%Z then
      sublist count size headers ++ Zrepeat (uninit_sval_of_sval (Some false) (Znth 0 headers)) count
    else
      Zrepeat (uninit_sval_of_sval (Some false) (Znth 0 headers)) size
  in
  let next' := Z.to_N (Z.of_N next - count) in
  ValBaseStack headers' next'.

(* The expression h.minSizeInBits() is defined for any value h that has a header type.
   The expression is equal to the sum of the sizes of all of header h's fields in bits,
   counting all varbit fields as length 0. An expression h.minSizeInBits() is a compile-time
   constant with type int.
   The expression h.minSizeInBytes() is similar to h.minSizeInBits(), except that it returns
   the total size of all of the header's fields in bytes, rounding up to the next whole number
   of bytes if the header's size is not a multiple of 8 bits long. h.minSizeInBytes() is
   equal to (h.minSizeInBits() + 7) >> 3. *)
(* It should be guaranteed there is at most one valid header in a union. *)
(* stack.next must be handled in a preprocessor, as it returns an lvalue. *)
(* ValBaseStack: next, last, pop_front, push_front are supposed to be handled in exec_builtin *)
(* Calling the isValid() method on an element of a header stack, where the index is out of range,
   returns an undefined boolean value, i.e., it is either true or false, but the specification
   does not require one or the other, nor that a consistent value is returned across multiple such calls.*)
(* If any of these kinds of writes are performed:
   ... a method call of setValid() or setInvalid() on an element of a header stack, where the index is out of range
   then that write must not change any state that is currently defined in the system, neither in header
   fields nor anywhere else. In particular, if an invalid header is involved in the write, it must remain invalid. *)

Inductive exec_builtin (read_one_bit : option bool -> bool -> Prop) : path -> state -> Lval -> ident -> list Sval -> state -> signal -> Prop :=
| exec_builtin_isValid : forall p st lv sv is_valid,
    exec_read st lv sv ->
    exec_isValid read_one_bit sv is_valid ->
    exec_builtin read_one_bit p st lv "isValid" [] st (SReturn (ValBaseBool is_valid))
| exec_builtin_setValid : forall p st lv fields is_valid st',
    exec_read st lv (ValBaseHeader fields is_valid) ->
    exec_write st lv (ValBaseHeader fields (Some true)) st' ->
    exec_builtin read_one_bit p st lv "setValid" [] st' (SReturn ValBaseNull)
| exec_builtin_setInalid : forall p st lv fields is_valid st',
    exec_read st lv (ValBaseHeader fields is_valid) ->
    exec_write st lv (ValBaseHeader fields (Some false)) st' ->
    exec_builtin read_one_bit p st lv "setInvalid" [] st' (SReturn ValBaseNull)
| exec_builtin_push_front : forall p st lv headers next count st',
    exec_read st lv (ValBaseStack headers next) ->
    exec_write st lv (push_front headers next count) st' ->
    exec_builtin read_one_bit p st lv "push_front" [ValBaseInteger count] st' (SReturn ValBaseNull)
| exec_builtin_pop_front : forall p st lv headers next count st',
    exec_read st lv (ValBaseStack headers next) ->
    exec_write st lv (pop_front headers next count) st' ->
    exec_builtin read_one_bit p st lv "pop_front" [ValBaseInteger count] st' (SReturn ValBaseNull).

Definition is_builtin_func (expr : @Expression tags_t) : bool :=
  match expr with
  | MkExpression _ _ (TypFunction (MkFunctionType _ _ FunBuiltin _)) _ =>
      true
  | _ => false
  end.

Inductive exec_stmt (read_one_bit : option bool -> bool -> Prop) :
  path -> state -> (@Statement tags_t) -> state -> signal -> Prop :=
| exec_stmt_assign : forall lhs lv rhs v sv this_path st tags typ st' sig,
    exec_expr_det read_one_bit this_path st rhs v ->
    exec_lexpr read_one_bit this_path st lhs lv sig ->
    val_to_sval v sv ->
    (if is_continue sig then exec_write st lv sv st' else st' = st) ->
    exec_stmt read_one_bit this_path st
              (MkStatement tags (StatAssignment lhs rhs) typ) st' sig
| exec_stmt_assign_func_call : forall lhs lv rhs sv this_path
                                 st tags typ st' st'' sig sig' ret_sig,
    exec_call read_one_bit this_path st rhs st' sig' ->
    exec_lexpr read_one_bit this_path st lhs lv sig ->
    (if not_continue sig then st'' = st /\ ret_sig = sig
     else if not_return sig' then st'' = st' /\ ret_sig = sig'
          else get_return_sval sig' sv /\
               exec_write st' lv sv st'' /\ ret_sig = SContinue) ->
    exec_stmt read_one_bit this_path st
              (MkStatement tags (StatAssignment lhs rhs) typ) st'' ret_sig
| exec_stmt_method_call : forall this_path st tags func targs args typ st' sig sig',
    exec_call
      read_one_bit this_path st
      (MkExpression dummy_tags (ExpFunctionCall func targs args) TypVoid Directionless)
              st' sig ->
    force_continue_signal sig = sig' ->
    exec_stmt read_one_bit this_path st
              (MkStatement tags (StatMethodCall func targs args) typ) st' sig'
| exec_stmt_direct_application : forall this_path st tags typ' args typ st' sig sig',
      exec_call read_one_bit this_path st
                (MkExpression
                   dummy_tags
                   (ExpFunctionCall
                      (direct_application_expression typ')
                      nil (map Some args)) TypVoid Directionless)
                st' sig ->
      force_continue_signal sig = sig' ->
      exec_stmt read_one_bit this_path st
                (MkStatement tags (StatDirectApplication typ' args) typ) st' sig'
| exec_stmt_conditional_some_fls : forall cond tru fls b this_path st tags typ st' sig,
    exec_expr_det read_one_bit this_path st cond (ValBaseBool b) ->
    exec_stmt read_one_bit this_path st (if b then tru else fls) st' sig ->
    exec_stmt read_one_bit this_path st
              (MkStatement tags (StatConditional cond tru (Some fls)) typ) st' sig
| exec_stmt_conditional_none_fls : forall cond tru b this_path st tags typ st' sig,
    exec_expr_det read_one_bit this_path st cond (ValBaseBool b) ->
    exec_stmt
      read_one_bit this_path st (if b then tru else empty_statement) st' sig ->
    exec_stmt read_one_bit this_path st
              (MkStatement tags (StatConditional cond tru None) typ) st' sig
  | exec_stmt_block : forall block this_path st tags typ st' sig,
      exec_block read_one_bit this_path st block st' sig ->
      exec_stmt read_one_bit this_path st
                (MkStatement tags (StatBlock block) typ) st' sig
  | exec_stmt_exit : forall this_path (st: state) tags typ st,
      exec_stmt read_one_bit this_path st
                (MkStatement tags StatExit typ) st SExit
  | exec_stmt_return_none : forall this_path (st: state) tags typ st,
      exec_stmt read_one_bit this_path st
                (MkStatement tags (StatReturn None) typ) st SReturnNull
  | exec_stmt_return_some : forall e v this_path (st: state) tags typ st,
      exec_expr_det read_one_bit this_path st e v ->
      exec_stmt read_one_bit this_path st
                (MkStatement tags (StatReturn (Some e)) typ) st (SReturn v)
  | exec_stmt_empty : forall this_path (st: state) tags typ st,
      exec_stmt read_one_bit this_path st
                (MkStatement tags StatEmpty typ) st SContinue
  | exec_stmt_switch : forall tags expr cases typ this_path st st' sig s block,
      exec_expr_det read_one_bit this_path st expr (ValBaseString s) ->
      match_switch_case s cases = block ->
      exec_block read_one_bit this_path st block st' sig ->
      exec_stmt read_one_bit this_path st
                (MkStatement tags (StatSwitch expr cases) typ) st' sig
  | exec_stmt_variable : forall typ' name e v sv loc this_path st tags typ st',
      exec_expr_det read_one_bit this_path st e v ->
      val_to_sval v sv ->
      exec_write st
        (MkValueLvalue (ValLeftName (BareName name) loc) typ') sv st' ->
      exec_stmt
        read_one_bit this_path st
        (MkStatement tags (StatVariable typ' name (Some e) loc) typ) st' SContinue
  | exec_stmt_variable_func_call :
      forall typ' name e sv loc this_path st tags typ st' st'' sig,
        exec_call read_one_bit this_path st e st' sig ->
        (if not_return sig then st'' = st'
         else get_return_sval sig sv /\
              exec_write st'
                (MkValueLvalue (ValLeftName (BareName name) loc) typ') sv st'') ->
        exec_stmt
          read_one_bit this_path st
          (MkStatement tags (StatVariable typ' name (Some e) loc) typ)
          st'' (force_continue_signal sig)
  | exec_stmt_variable_undef : forall typ' rtyp name loc sv this_path st tags typ st',
      get_real_type typ' = Some rtyp ->
      uninit_sval_of_typ (Some false) rtyp = Some sv ->
      exec_write st (MkValueLvalue (ValLeftName (BareName name) loc) typ') sv st' ->
      exec_stmt read_one_bit this_path st
                (MkStatement tags (StatVariable typ' name None loc) typ) st' SContinue
  | exec_stmt_constant: forall typ' name e loc this_path st tags typ,
      (* Constant is ignored at runtime. *)
      exec_stmt read_one_bit this_path st
                (MkStatement tags (StatConstant typ' name e loc) typ) st SContinue
  (* StatInstantiation is unsupported. If supported, it should be considered in instantiation. *)

with exec_block (read_one_bit : option bool -> bool -> Prop) :
                path -> state -> (@Block tags_t) -> state -> signal -> Prop :=
  | exec_block_nil : forall this_path st tags,
                     exec_block read_one_bit this_path st (BlockEmpty tags) st SContinue
  | exec_block_cons : forall stmt rest this_path st st' st'' sig sig',
                      (* This style is for avoiding backtracking *)
                      exec_stmt read_one_bit this_path st stmt st' sig ->
                      exec_block read_one_bit this_path st'
                          (if is_continue sig then rest else empty_block) st'' sig' ->
                      exec_block read_one_bit this_path st (BlockCons stmt rest) st''
                          (if is_continue sig then sig' else sig)

with exec_call (read_one_bit : option bool -> bool -> Prop) :
               path -> state -> (@Expression tags_t) -> state -> signal -> Prop :=
  (* Perhaps we want to allow some built-in fucntions, e.g. isValid(), execute on rvalues. We can do that
    by some preprocessing. *)
  (* The code will be simpler if we avoid expanding the TypFunction part but using an is_builtin function
    to test it. However, that will make repeat econstructor need backtracking. *)
  | exec_call_builtin : forall this_path s tags tags' expr fname tparams params typ' dir' args typ dir argvals s' sig sig' sig'' lv,
      let dirs := map get_param_dir params in
      exec_lexpr read_one_bit this_path s expr lv sig ->
      exec_args read_one_bit this_path s args dirs argvals sig' ->
      (if not_continue sig then s' = s /\ sig'' = sig
       else if not_continue sig' then s' = s /\ sig'' = sig'
       else exec_builtin read_one_bit this_path s lv (str fname) (extract_invals argvals) s' sig'') ->
      (* As far as we know, built-in functions do not have out/inout parameters. So there's not a caller
        copy-out step. Also exec_args should never raise any signal other than continue. *)
      exec_call read_one_bit this_path s (MkExpression tags (ExpFunctionCall
          (MkExpression tags' (ExpExpressionMember expr fname) (TypFunction (MkFunctionType tparams params FunBuiltin typ')) dir')
          nil args) typ dir) s' sig''
  (* eval the call expression:
       1. eval arguments;
       2. lookup the function to call;
       3. call the function by exec_funcall;
       4. write back out parameters.
  *)
  | exec_call_func : forall this_path s1 tags func targs args typ dir argvals obj_path fd outvals s2 s3 s4 s5 sig sig' ret_s ret_sig,
      is_builtin_func func = false ->
      let dirs := get_arg_directions func in
      exec_args read_one_bit this_path s1 args dirs argvals sig ->
      lookup_func this_path func = Some (obj_path, fd) ->
      s2 = (if is_some obj_path then set_memory PathMap.empty s1 else s1) ->
      exec_func read_one_bit (force this_path obj_path) s2 fd targs (extract_invals argvals) s3 outvals sig' ->
      s4 = (if is_some obj_path then set_memory (get_memory s1) s3 else s3) ->
      exec_call_copy_out (combine (map snd argvals) dirs) outvals s4  s5 ->
      (if is_continue sig then ret_s = s5 /\ ret_sig = sig' else ret_s = s1 /\ ret_sig = sig) ->
      exec_call read_one_bit this_path s1 (MkExpression tags (ExpFunctionCall func targs args) typ dir)
      ret_s ret_sig

(* Only in/inout arguments in the first list Val and only out/inout arguments in the second list Val. *)
with exec_func (read_one_bit : option bool -> bool -> Prop) :
               path -> state -> fundef -> list P4Type -> list Sval -> state -> list Sval -> signal -> Prop :=
  | exec_func_internal : forall obj_path s params body args args' s' s'' sig sig',
      exec_func_copy_in params args s = s' ->
      exec_block read_one_bit obj_path s' body s'' sig ->
      force_return_signal sig = sig' ->
      exec_func_copy_out params s'' = Some args'->
      exec_func read_one_bit obj_path s (FInternal params body) nil args s'' args' sig'

  | exec_func_table_match : forall obj_path name keys actions actionref action_name retv ctrl_args action default_action const_entries s s',
      exec_table_match read_one_bit obj_path s name const_entries actionref ->
      (if is_some actionref
       then actionref = (Some (mk_action_ref action_name ctrl_args))
            /\ add_ctrl_args (get_action actions action_name) ctrl_args = Some action
            /\ retv = (SReturn (table_retv true "" (get_expr_func_name action)))
       else action = default_action
            /\ retv = (SReturn (table_retv false "" (get_expr_func_name default_action)))) ->
      exec_call read_one_bit obj_path s action s' SReturnNull ->
      exec_func read_one_bit obj_path s (FTable name keys actions (Some default_action) const_entries)
        nil nil s' nil retv

  (* This will not happen in the latest spec. *)
  (* | exec_func_table_noaction : forall obj_path name keys actions const_entries s,
      exec_table_match obj_path s name const_entries SReturnNull ->
      exec_func obj_path s (FTable name keys actions None const_entries) nil s nil None *)

  (* Todo: check in/inout/out & uninitialized args *)
  | exec_func_external : forall obj_path class_name name (* params *) m es es' targs args argvs argvs' args' sig,
      svals_to_vals read_one_bit args argvs ->
      exec_extern ge es class_name name obj_path targs argvs es' argvs' sig ->
      vals_to_svals argvs' args' ->
      exec_func read_one_bit obj_path (m, es) (FExternal class_name name (* params *)) targs args (m, es') args' sig.

(* Return the declaration whose name is [name]. *)
Fixpoint get_decl (rev_decls : list (@Declaration tags_t)) (name : ident) : (@Declaration tags_t) :=
  match rev_decls with
  | decl :: rev_decls' =>
      match decl with
      | DeclParser _ name' _ _ _ _ _
      | DeclControl _ name' _ _ _ _ _
      | DeclExternObject _ name' _ _
      | DeclPackageType _ name' _ _ =>
          if String.eqb name (str name') then
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
      (clear_list (map get_param_name constructor_params))
  | _ => nil
  end.

Definition dummy_ident : ident := "".
Global Opaque dummy_ident.

Definition get_type_name (typ : @P4Type tags_t) : ident :=
  match typ with
  | TypSpecializedType (TypTypeName type_name) _ => str type_name
  | TypTypeName type_name => str type_name
  | _ => dummy_ident
  end.

Definition get_type_params (typ : @P4Type tags_t) : list (@P4Type tags_t) :=
  match typ with
  | TypSpecializedType _ params => params
  | _ => nil
  end.

Definition BlockNil := BlockEmpty dummy_tags.

Definition BlockSingleton (stmt : @Statement tags_t) : @Block tags_t :=
  BlockCons stmt BlockNil.

(* out parameters are, with a few exceptions listed below, uninitialized and are treated
   as l-values (See Section 6.6) within the body of the method or function...
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

Fixpoint uninit_out_params (params: list (ident * P4Type)) : Block :=
  match params with
  | [] => BlockNil
  | param :: params' =>
      let block := uninit_out_params params' in
      let (name, typ) := param in
      let p4name := P4String.Build_t tags_t inhabitant_tags_t name in
      let stmt := MkStatement dummy_tags (StatVariable typ p4name None (LInstance [str p4name])) StmUnit in
      BlockCons stmt block
  end.

Definition ienv_val : Type := inst_ref + Val.
Definition ienv := IdentMap.t ienv_val.
Axiom dummy_ienv_val : ienv_val.

(* inst_mem is a legacy concept. Now it is actually the pair of genv_inst and genv_const.
  It is the result of instantiation. *)
Definition inst_mem : Type := genv_inst * genv_const * extern_env.

Definition set_inst_mem (p : path) (v : ienv_val) (m : inst_mem) : inst_mem :=
  match v with
  | inl inst => map_fst (map_fst (PathMap.set p inst)) m
  | inr v => map_fst (map_snd (PathMap.set p v)) m
  end.

(* cenv is a class environment, mapping names to closures. Each closure contains
  a class (parser/control) definition and an environment to interpret its free names.
  It's designed in this way to ensure termination. *)
Inductive cenv := mk_cenv : IdentMap.t (cenv * @Declaration tags_t) -> cenv.

Definition unfold_cenv (ce : cenv) :=
  match ce with
  | mk_cenv inner_ce => inner_ce
  end.

Coercion unfold_cenv : cenv >-> IdentMap.t.

Inductive exec_abstract_method : path -> fundef -> extern_state -> list Val -> extern_state -> list Val -> signal -> Prop :=
  | exec_abstract_method_intro : forall p fd es args es' args' sargs sargs' sig m',
      vals_to_svals args sargs ->
      exec_func read_ndetbit p (PathMap.empty, es) fd nil sargs (m', es') sargs' sig ->
      svals_to_vals read_ndetbit sargs' args' ->
      exec_abstract_method p fd es args es' args' sig.

(* The following section defines a group of mutually recursive functions:
  instantiate_expr: instantiate an instance expression (e.g. nameless instantiation)
  instantiate: instantiate an instance given typ and evaluated args
  instantiate_decl: instantiate an instance declaration
  instantiate_class_body: instantiate inner instances given a class definition
*)

Section instantiate_class_body.

Variable instantiate_class_body_ce : forall (e : ienv) (class_name : ident) (p : path) (m : inst_mem)
      (s : extern_state), path * inst_mem * extern_state.

Section instantiate_expr'.

Variable instantiate_expr' : forall (ce : cenv) (e : ienv) (expr : @Expression tags_t)
      (p : path) (m : inst_mem) (s : extern_state), ienv_val * inst_mem * extern_state.

Definition ienv_val_to_sumtype (val : ienv_val) :=
  match val with
  | inl (mk_inst_ref _ p) => inl p
  | inr val => inr val
  end.

Definition dummy_cenv := mk_cenv IdentMap.empty.
Definition dummy_decl := DeclError dummy_tags nil.

Opaque dummy_cenv dummy_decl.

(* Given type (class name and type args) and args (in expressions), instantiate the instantce at p. *)
Definition instantiate'' (ce : cenv) (e : ienv) (typ : @P4Type tags_t)
      (args : list (@Expression tags_t)) (p : path) (m : inst_mem) (s : extern_state) : ienv_val * inst_mem * extern_state :=
  let class_name := get_type_name typ in
  let (_, decl) := force (dummy_cenv, dummy_decl) (IdentMap.get class_name ce) in
  (* params := nil if decl is an external object, but params is only used to name the instances. *)
  let params := get_constructor_param_names decl in
  let instantiate_arg (acc : list ienv_val * inst_mem * extern_state * list ident) arg :=
    let '(args, m, s, params) := acc in
    let '(arg, m, s) := instantiate_expr' ce e arg (match params with hd :: _ => p ++ [hd] | _ => [] end) m s in
    (* O(n^2) time complexity here. *)
    (args ++ [arg], m, s, tl params) in
  let '(args, m, s) := fst (fold_left instantiate_arg args (nil, m, s, params)) in
  if is_decl_extern_obj decl then
    let m := map_fst (map_fst (PathMap.set p (mk_inst_ref class_name p))) m in
    let type_params := get_type_params typ in
    let (ee, s) := construct_extern (snd m) s class_name type_params p (map ienv_val_to_sumtype args) in
    (inl (mk_inst_ref class_name p), (fst m, ee), s)
  else
    let e := IdentMap.sets params args e in
    let '(_, m, s) := instantiate_class_body_ce e class_name p m s in
    (inl (mk_inst_ref class_name p), m, s).

End instantiate_expr'.

Definition get_val_ienv (e : ienv) (name : Typed.name) : option Val :=
  match name with
  | BareName name =>
      match IdentMap.get (@str tags_t name) e with
      | Some (inr v) => Some v
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

(* Evaluate/instantiate the expression expr at p. Copy the result to p if p is not []. *)
Fixpoint instantiate_expr' (ce : cenv) (e : ienv) (expr : @Expression tags_t) (p : path)
      (m : inst_mem) (s : extern_state) {struct expr} : ienv_val * inst_mem * extern_state :=
  let instantiate' := instantiate'' instantiate_expr' in
  match expr with
  | MkExpression _ (ExpName (BareName name) _) _ _ =>
      (* Can inst be a Val, or just an inst_ref? *)
      let inst := force dummy_ienv_val (IdentMap.get (str name) e) in
      let m := if path_eqb p [] then m else set_inst_mem p inst m in
      (inst, m, s)
  | MkExpression _ (ExpNamelessInstantiation typ args) _ _ =>
      instantiate' ce e typ args p m s
  | _ =>
      match eval_expr_gen (eval_expr_ienv_hook e) expr with
      | Some v => (inr v, m, s)
      | None => (dummy_ienv_val, m, s)
      end
  end.

Definition instantiate' :=
  instantiate'' instantiate_expr'.

Fixpoint instantiate_decl' (is_init_block : bool) (ce : cenv) (e : ienv) (decl : @Declaration tags_t)
      (p : path) (m : inst_mem) (s : extern_state) : ienv * inst_mem * extern_state :=
  match decl with
  | DeclInstantiation _ typ args name init =>
      let '(inst, m, s) := instantiate' ce e typ args (p ++ clear_list [name]) m s in
      let instantiate_decl'' (ems : ienv * inst_mem * extern_state) (decl : @Declaration tags_t) : ienv * inst_mem * extern_state :=
        let '(e, m, s) := ems in instantiate_decl' true ce e decl (p ++ clear_list [name]) m s in
      let '(_, m, s) := fold_left instantiate_decl'' init (e, m, s) in
      (IdentMap.set (str name) inst e, m, s)
  | DeclFunction _ _ name type_params params body =>
      if is_init_block then
        let out_params := filter_pure_out (map (fun p => (get_param_name_typ p, get_param_dir p)) params) in
        let iout_params := map (fun p => (str (fst p), snd p)) out_params in
        let init := uninit_out_params iout_params in
        let params := map get_param_name_dir params in
        let params := map (map_fst (fun param => LGlobal (clear_list [name; param]))) params in
        let fd := FInternal (map (map_fst get_loc_path) params) (block_app init body) in
        let ee := extern_set_abstract_method (snd m) (p ++ [str name]) (exec_abstract_method p fd) in
        (e, (fst m, ee), s)
      else
        (e, m, s)
  | _ => (e, m, s)
  end.

Definition instantiate_decls' (ce : cenv) (e : ienv) (decls : list (@Declaration tags_t))
      (p : path) (m : inst_mem) (s : extern_state) : inst_mem * extern_state :=
  let instantiate_decl'' (ems : ienv * inst_mem * extern_state) (decl : @Declaration tags_t) : ienv * inst_mem * extern_state :=
    let '(e, m, s) := ems in instantiate_decl' false ce e decl p m s in
  let '(_, m, s) := fold_left instantiate_decl'' decls (e, m, s) in
  (m, s).

End instantiate_class_body.

(* Currently, we only handle direct application but not StatInstantiation. *)
Fixpoint get_direct_applications_stmt (stmt : @Statement tags_t) : list (@Declaration tags_t) :=
  match stmt with
  | MkStatement _ (StatDirectApplication typ _) _  =>
      [DeclInstantiation dummy_tags typ nil (P4String.Build_t tags_t inhabitant_tags_t (get_type_name typ)) []]
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

Definition packet_in_instance : ienv_val := (inl (mk_inst_ref "packet_in" ["packet_in"])).

Definition is_packet_in (param : @P4Parameter tags_t) : bool :=
  match param with
  | MkParameter _ _ typ _ _ =>
      match typ with
      | TypTypeName name =>
          String.eqb (P4String.str name) "packet_in"
      | _ => false
      end
  end.

Definition packet_out_instance : ienv_val := (inl (mk_inst_ref "packet_out" ["packet_out"])).

Definition is_packet_out (param : @P4Parameter tags_t) : bool :=
  match param with
  | MkParameter _ _ typ _ _ =>
      match typ with
      | TypTypeName name =>
          String.eqb (P4String.str name) "packet_out"
      | _ => false
      end
  end.

Definition inline_packet_in_and_packet_out (p : path) (m : inst_mem) (param : @P4Parameter tags_t) : inst_mem :=
  if is_packet_in param then
    set_inst_mem (p ++ [str (get_param_name param)]) packet_in_instance m
  else if is_packet_out param then
    set_inst_mem (p ++ [str (get_param_name param)]) packet_out_instance m
  else
    m.

Fixpoint instantiate_class_body (ce : cenv) (e : ienv) (class_name : ident) (p : path)
      (m : inst_mem) (s : extern_state) : path * inst_mem * extern_state :=
  match IdentMap.get class_name ce with
  | Some (ce', decl) =>
    let instantiate_decls := instantiate_decls' (instantiate_class_body ce') in
    match decl with
    | DeclParser _ class_name' _ params _ locals states =>
        let m := fold_left (inline_packet_in_and_packet_out p) params m in
        let locals := locals ++ concat (map get_direct_applications_ps states) in
        let (m, s) := instantiate_decls ce' e locals p m s in
        let m := set_inst_mem p (inl (mk_inst_ref class_name p)) m in
        (p, m, s)
    | DeclControl _ class_name' _ params _ locals apply =>
        let m := fold_left (inline_packet_in_and_packet_out p) params m in
        let locals := locals ++ get_direct_applications_blk apply in
        let (m, s) := instantiate_decls ce' e locals p m s in
        let m := set_inst_mem p (inl (mk_inst_ref class_name p)) m in
        (p, m, s)
    | _ => (p, m, s) (* impossible *)
    end
  | None => (p, m, s) (* impossible *)
  end.

Definition instantiate_expr (ce : cenv) :=
  instantiate_expr' (instantiate_class_body ce) ce.

Definition instantiate (ce : cenv) :=
  instantiate' (instantiate_class_body ce) ce.

Definition instantiate_decl (ce : cenv) :=
  instantiate_decl' (instantiate_class_body ce) false ce.

Definition instantiate_decls (ce : cenv) :=
  instantiate_decls' (instantiate_class_body ce) ce.

Fixpoint instantiate_global_decls' (decls : list (@Declaration tags_t)) (ce : cenv)
      (e : ienv) (m : inst_mem) (s : extern_state) {struct decls}: inst_mem * extern_state :=
  match decls with
  | [] => (m, s)
  | decl :: decls' =>
      let '(e, m, s) := instantiate_decl ce e decl nil m s in
      let ce' :=
        match get_decl_class_name decl with
        | Some name =>
            mk_cenv (IdentMap.set (str name) (ce, decl) ce)
        | None => ce
        end in
      instantiate_global_decls' decls' ce' e m s
  end.

Definition instantiate_global_decls (decls : list (@Declaration tags_t)) :
      forall (m : inst_mem) (s: extern_state), inst_mem * extern_state :=
  instantiate_global_decls' decls (mk_cenv IdentMap.empty) IdentMap.empty.

Definition instantiate_prog (prog : @program tags_t) : inst_mem * extern_state :=
  match prog with
  | Program decls =>
      instantiate_global_decls decls (PathMap.empty, PathMap.empty, PathMap.empty) PathMap.empty
  end.

Fixpoint process_locals (locals : list (@Declaration tags_t)) : @Block tags_t :=
  match locals with
  | [] => BlockNil
  | decl :: locals' =>
      let block' := process_locals locals' in
      match decl with
      | DeclVariable tags typ name init =>
          let stmt := MkStatement tags (StatVariable typ name init (LInstance [str name])) StmUnit in
          BlockCons stmt block'
      | _ => block'
      end
  end.

Definition empty_func_type : @P4Type tags_t :=
  TypFunction (MkFunctionType nil nil FunParser TypVoid).

Definition load_parser_transition (p : path) (trans : @ParserTransition tags_t) : @Block tags_t :=
  match trans with
  | ParserDirect tags next =>
      let method := MkExpression dummy_tags (ExpName (BareName next) (LInstance [str next])) empty_func_type Directionless in
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
      PathMap.set (p ++ [str name]) (FInternal nil body) ge
  end.

Definition accept_state :=
  FInternal nil BlockNil.

Definition reject_state :=
  let verify := (MkExpression dummy_tags (ExpName (BareName !"verify") (LGlobal ["verify"])) dummy_type Directionless) in
  let false_expr := (MkExpression dummy_tags (ExpBool false) TypBool Directionless) in
  let stmt := (MkStatement dummy_tags (StatMethodCall verify nil [Some false_expr]) StmUnit) in
  FInternal nil (BlockSingleton stmt).

Definition action_param_to_p4param (param : path * direction) : P4Parameter :=
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
                match PathMap.get (p ++ [str id]) ge with
                | Some _ => LInstance [str id]
                | None => LGlobal [str id]
                end
            | QualifiedName p id => LGlobal (clear_list (p ++ [id]))
            end in
          let typ :=
            let ofd :=
              match loc with
              | LInstance p' => PathMap.get (p ++ p') ge
              | LGlobal p' => PathMap.get p' ge
              end in
            match ofd with
            | Some (FInternal params _) =>
                TypFunction (MkFunctionType nil (map action_param_to_p4param params) FunAction TypVoid)
            | _ => dummy_type (* impossible *)
            end in
          let func := MkExpression dummy_tags (ExpName name loc) typ Directionless in
          MkExpression dummy_tags (ExpFunctionCall func nil args) dummy_type Directionless
      end
  end.

Definition unwrap_action_ref2 (ref : TableActionRef) : (@action_ref (@Expression tags_t)) :=
  match ref with
  | MkTableActionRef _ ref _ =>
      match ref with
      | MkTablePreActionRef name args =>
          let id :=
            match name with
            | BareName id => id
            | QualifiedName _ id => id
            end in
          mk_action_ref (str id) args
      end
  end.

Definition unwrap_table_entry (entry : TableEntry) : table_entry :=
  match entry with
  | MkTableEntry _ matches action =>
      mk_table_entry matches (unwrap_action_ref2 action)
  end.

Fixpoint load_decl (p : path) (ge : genv_func) (decl : @Declaration tags_t) : genv_func :=
  match decl with
  | DeclParser _ name type_params params constructor_params locals states =>
      let params := map get_param_name_dir params in
      let params := map (map_fst (fun param => LInstance [str param])) params in
      let params := List.filter (compose is_directional snd) params in
      let ge := fold_left (load_decl (p ++ [str name])) locals ge in
      let init := process_locals locals in
      let ge := fold_left (load_parser_state (p ++ [str name])) states ge in
      let ge := PathMap.set (p ++ [str name; "accept"]) accept_state ge in
      let ge := PathMap.set (p ++ [str name; "reject"]) reject_state ge in
      let method := MkExpression dummy_tags (ExpName (BareName !"begin") (LInstance ["begin"]))
                    empty_func_type Directionless in
      let stmt := MkStatement dummy_tags (StatMethodCall method nil nil) StmUnit in
      PathMap.set (p ++ [str name; "apply"]) (FInternal (map (map_fst get_loc_path) params) (block_app init (BlockSingleton stmt))) ge
  | DeclControl _ name type_params params _ locals apply =>
      let params := map get_param_name_dir params in
      let params := map (map_fst (fun param => LInstance [str param])) params in
      let params := List.filter (compose is_directional snd) params in
      let ge := fold_left (load_decl (p ++ [str name])) locals ge in
      let init := process_locals locals in
      PathMap.set (p ++ [str name; "apply"]) (FInternal (map (map_fst get_loc_path) params) (block_app init apply)) ge
  | DeclFunction _ _ name type_params params body =>
      let out_params := filter_pure_out (map (fun p => (get_param_name_typ p, get_param_dir p)) params) in
      let iout_params := map (fun p => (str (fst p), snd p)) out_params in
      let init := uninit_out_params iout_params in
      let params := map get_param_name_dir params in
      let params := map (map_fst (fun param => LGlobal (clear_list [name; param]))) params in
      PathMap.set (p ++ [str name]) (FInternal (map (map_fst get_loc_path) params) (block_app init body)) ge
  | DeclExternFunction _ _ name _ _ =>
      PathMap.set (p ++ [str name]) (FExternal "" (str name)) ge
  | DeclExternObject _ name _ methods =>
      let add_method_prototype ge' method :=
        match method with
        | ProtoMethod _ _ mname _ _ =>
            PathMap.set (p ++ [str name; str mname]) (FExternal (str name) (str mname)) ge'
        | _ => ge
        end
      in fold_left add_method_prototype methods ge
  | DeclAction _ name params ctrl_params body =>
      let out_params := filter_pure_out (map (fun p => (get_param_name_typ p, get_param_dir p)) params) in
      let iout_params := map (fun p => (str (fst p), snd p)) out_params in
      let init := uninit_out_params iout_params in
      let params := map get_param_name_dir params in
      let ctrl_params := map (fun name => (name, In)) (map get_param_name ctrl_params) in
      let combined_params :=
        if path_eqb p [] then
          map (map_fst (fun param => LGlobal (clear_list [name; param]))) (params ++ ctrl_params)
        else
          map (map_fst (fun param => LInstance (clear_list [name; param]))) (params ++ ctrl_params) in
      PathMap.set (p ++ [str name]) (FInternal (map (map_fst get_loc_path) combined_params) (block_app init body)) ge
  | DeclTable _ name keys actions entries default_action _ _ =>
      let table :=
        FTable (str name) keys (map (unwrap_action_ref p ge) actions) (option_map (unwrap_action_ref p ge) default_action)
            (option_map (map unwrap_table_entry) entries) in
      PathMap.set (p ++ [str name]) table ge
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

Definition get_decl_typ_name (decl: @Declaration tags_t): option ident :=
  match decl with
  | DeclHeader _ name _
  | DeclHeaderUnion _ name _
  | DeclStruct _ name _
  | DeclControlType _ name _ _
  | DeclParserType _ name _ _
  | DeclPackageType _ name _ _
  | DeclTypeDef _ name _
  | DeclNewType _ name _ => Some (str name)
  | _ => None
  end.

(* TODO: Do we need to consider duplicated type names? *)
Fixpoint add_to_genv_typ (ge_typ: genv_typ)
         (decl: @Declaration tags_t): option genv_typ :=
  match decl with
  | DeclHeader tags name fields =>
    Some (IdentMap.set (str name) (TypHeader (conv_decl_fields fields)) ge_typ)
  | DeclHeaderUnion tags name fields =>
    Some (IdentMap.set (str name) (TypHeaderUnion (conv_decl_fields fields)) ge_typ)
  | DeclStruct tags name fields =>
    Some (IdentMap.set (str name) (TypStruct (conv_decl_fields fields)) ge_typ)
  | DeclControlType tags name type_params params =>
    Some (IdentMap.set (str name) (TypControl (MkControlType type_params params)) ge_typ)
  | DeclParserType tags name type_params params =>
    Some (IdentMap.set (str name) (TypParser (MkControlType type_params params)) ge_typ)
  (* TODO: DeclPackageType and TypPackage are inconsistency *)
  | DeclPackageType tags name type_params params =>
    Some (IdentMap.set (str name) (TypPackage type_params nil params) ge_typ)
  | DeclEnum tags name members =>
    Some (IdentMap.set (str name) (TypEnum name None members) ge_typ)
  (* TODO: Do we need to consider the difference between DeclTypeDef
     and DeclNewType? *)
  | DeclTypeDef tags name (inl typ)
  | DeclNewType tags name (inl typ) =>
    match typ with
    | TypTypeName name2 => match IdentMap.get (str name2) ge_typ with
                           | Some typ2 => Some (IdentMap.set (str name) typ2 ge_typ)
                           | None => None
                           end
    | _ => Some (IdentMap.set (str name) typ ge_typ)
    end
  | DeclTypeDef tags name (inr decl2)
  | DeclNewType tags name (inr decl2) =>
    match add_to_genv_typ ge_typ decl2 with
    | Some ge_typ2 => match get_decl_typ_name decl2 with
                      | Some name2 =>
                        match IdentMap.get name2 ge_typ2 with
                        | Some typ2 => Some (IdentMap.set (str name) typ2 ge_typ2)
                        | None => None
                        end
                      | None => None
                      end
    | None => None
    end
  | _ => Some ge_typ
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

End WithGenv.

Definition gen_ge (prog : @program tags_t) : genv :=
  let ge_func := load_prog prog in
  let ge_typ := force IdentMap.empty (gen_ge_typ prog) in
  let ge_senum := gen_ge_senum prog in
  let partial_ge := MkGenv ge_func ge_typ ge_senum PathMap.empty PathMap.empty PathMap.empty in
  let inst_m := fst (instantiate_prog partial_ge prog) in
  let ge_inst := fst (fst inst_m) in
  let ge_const := snd (fst inst_m) in
  let ge_ext := snd inst_m in
  MkGenv ge_func ge_typ ge_senum ge_inst ge_const ge_ext.

End Semantics.
