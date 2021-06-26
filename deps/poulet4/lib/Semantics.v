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
Require Import Poulet4.Ops.
Require Import Poulet4.Maps.
Require Export Poulet4.Target.
Require Export Poulet4.SyntaxUtil.
Require Export Poulet4.Sublist.
Require Import Poulet4.P4Notations.
Import ListNotations.

Section Semantics.

Context {tags_t: Type} {inhabitant_tags_t : Inhabitant tags_t}.
Notation Val := (@ValueBase tags_t).
Notation Lval := (@ValueLvalue tags_t).

Notation ident := (P4String.t tags_t).
Notation path := (list ident).
Notation P4Int := (P4Int.t tags_t).
Notation P4String := (P4String.t tags_t).
Notation signal := (@signal tags_t).

Context `{@Target tags_t (@Expression tags_t)}.

Definition mem := @PathMap.t tags_t Val.

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
Definition genv_senum := @IdentMap.t tags_t Val.

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

Definition eval_p4int (n: P4Int) : Val :=
  match P4Int.width_signed n with
  | None => ValBaseInteger (P4Int.value n)
  | Some (w, true) => ValBaseInt w (P4Int.value n)
  | Some (w, false) => ValBaseBit w (P4Int.value n)
  end.

Definition loc_to_val (this : path) (loc : Locator) (s : state) : option Val :=
  PathMap.get (loc_to_path this loc) (get_memory s).

Fixpoint array_access_idx_to_z (v : Val) : (option Z) :=
  match v with
  | ValBaseInt _ value
  | ValBaseBit _ value
  | ValBaseInteger value => Some value
  (* added in 1.2.2 *)
  | ValBaseSenumField _ _ value => array_access_idx_to_z value
  | _ => None
  end.

Definition bitstring_slice_bits_to_z (v : Val) : option (nat * Z) :=
  match v with
  | ValBaseInt width value
  | ValBaseBit width value => Some (width, value)
  | _ => None
  end.

(* Ref:When accessing the bits of negative numbers, all functions below will
   use the two's complement representation.
   For instance, -1 will correspond to an infinite stream of true bits.
   https://coq.inria.fr/library/Coq.ZArith.BinIntDef.html *)
  Definition bitstring_slice (i : Z) (lo : N) (hi : N) : Z :=
    let mask := (Z.pow 2 (Z.of_N (hi - lo + 1)) - 1)%Z in
    Z.land (Z.shiftr i (Z.of_N lo)) mask.

Definition Z_to_nat (i : Z) : option nat :=
  if (i >=? 0)%Z then Some (Z.to_nat i) else None.

Inductive is_uninitialized_value : Val -> (@P4Type tags_t) -> Prop :=
  | is_uninitialized_value_intro : forall v t, is_uninitialized_value v t.

(* TODO: reading uninitialized values of a header after it is made valid. *)
Inductive read_header_field: bool -> P4String.AList tags_t Val -> P4String -> P4Type -> Val -> Prop :=
  | read_header_field_intro : forall fields name typ v,
                              AList.get fields name = Some v ->
                              read_header_field true fields name typ v
  | read_header_field_undef : forall fields name typ v,
                              is_uninitialized_value v typ ->
                              read_header_field false fields name typ v.

Inductive get_member : Val -> P4String -> P4Type -> Val -> Prop :=
  | get_member_struct : forall fields member v typ,
                        AList.get fields member = Some v ->
                        get_member (ValBaseStruct fields) member typ v
  | get_member_record : forall fields member v typ,
                        AList.get fields member = Some v ->
                        get_member (ValBaseRecord fields) member typ v
  | get_member_union : forall fields member v typ,
                       AList.get fields member = Some v ->
                       get_member (ValBaseUnion fields) member typ v
  | get_member_header : forall fields b member v typ,
                        read_header_field b fields member typ v ->
                        get_member (ValBaseHeader fields b) member typ v.

(* Note that expressions don't need decl_path. *)
Inductive exec_expr : path -> (* temp_env -> *) state ->
                      (@Expression tags_t) -> Val ->
                      (* trace -> *) (* temp_env -> *) (* state -> *) (* signal -> *) Prop :=
  | exec_expr_bool : forall b this st tag typ dir,
                     exec_expr this st
                     (MkExpression tag (ExpBool b) typ dir)
                     (ValBaseBool b)
  | exec_expr_int : forall i iv this st tag typ dir,
                    iv = eval_p4int i ->
                    exec_expr this st
                    (MkExpression tag (ExpInt i) typ dir)
                    iv
  | exec_expr_string : forall s this st tag typ dir,
                       exec_expr this st
                       (MkExpression tag (ExpString s) typ dir)
                       (ValBaseString s)
  | exec_expr_name: forall name loc v this st tag typ dir,
                    loc_to_val this loc st = Some v ->
                    exec_expr this st
                    (MkExpression tag (ExpName name loc) typ dir)
                    v
  (* Note: same constructor for the two relations below. Need tactics to auto-run. *)
  | exec_expr_array_access: forall array headers size next idx idxv idxz idxn header this st tag typ dir,
                            exec_expr this st array (ValBaseStack headers size next) ->
                            exec_expr this st idx idxv ->
                            array_access_idx_to_z idxv = Some idxz ->
                            (0 <= idxz < (Z.of_nat size))%Z ->
                            Z_to_nat idxz = Some idxn ->
                            List.nth_error headers idxn = Some header ->
                            exec_expr this st
                            (MkExpression tag (ExpArrayAccess array idx) typ dir)
                            header
  | exec_expr_array_access_undef: forall array headers size next idx idxv idxz v this st tag typ dir,
                                  exec_expr this st array (ValBaseStack headers size next) ->
                                  exec_expr this st idx idxv ->
                                  array_access_idx_to_z idxv = Some idxz ->
                                  (idxz < 0)%Z \/ (idxz >= (Z.of_nat size))%Z ->
                                  is_uninitialized_value v typ ->
                                  exec_expr this st
                                  (MkExpression tag (ExpArrayAccess array idx) typ dir)
                                  v
  | exec_expr_bitstring_access : forall bits bitsv bitsz w lo hi this st tag typ dir,
                                 exec_expr this st bits bitsv ->
                                 bitstring_slice_bits_to_z bitsv = Some (w, bitsz) ->
                                 (lo <= hi < (N.of_nat w))%N ->
                                 exec_expr this st
                                 (MkExpression tag (ExpBitStringAccess bits lo hi) typ dir)
                                 (ValBaseBit (N.to_nat (hi - lo + 1)%N) (bitstring_slice bitsz lo hi))
  | exec_expr_list_nil : forall this st tag typ dir,
                         exec_expr this st
                         (MkExpression tag (ExpList nil) typ dir)
                         (ValBaseTuple nil)
  | exec_expr_list_cons : forall expr v es vs this st tag typ dir,
                          exec_expr this st expr v ->
                          exec_expr this st (MkExpression tag (ExpList es) typ dir) (ValBaseTuple vs) ->
                          exec_expr this st
                          (MkExpression tag (ExpList (expr :: es)) typ dir)
                          (ValBaseTuple (v :: vs))
  | exec_expr_record_nil : forall this st tag typ dir,
                           exec_expr this st
                           (MkExpression tag (ExpRecord nil) typ dir)
                           (ValBaseRecord nil)
  | exec_expr_record_cons : forall exprk exprv v es kvs this st tag_expr tag_kv typ dir,
                            exec_expr this st exprv v ->
                            exec_expr this st (MkExpression tag_expr (ExpRecord es) typ dir) (ValBaseRecord kvs) ->
                            exec_expr this st
                            (MkExpression tag_expr (ExpRecord ((MkKeyValue tag_kv exprk exprv) :: es)) typ dir)
                            (ValBaseRecord ((exprk, v) :: kvs))
  | exec_expr_unary_op : forall op arg argv v this st tag typ dir,
                         exec_expr this st arg argv ->
                         Ops.eval_unary_op op argv = Some v ->
                         exec_expr this st
                         (MkExpression tag (ExpUnaryOp op arg) typ dir)
                         v
  | exec_expr_binary_op : forall op larg largv rarg rargv v this st tag typ dir,
                          exec_expr this st larg largv ->
                          exec_expr this st rarg rargv ->
                          Ops.eval_binary_op op largv rargv = Some v ->
                          exec_expr this st
                          (MkExpression tag (ExpBinaryOp op (larg, rarg)) typ dir)
                          v
  | exec_expr_cast : forall newtyp expr oldv newv this st tag typ dir real_typ,
  (* We assume that ge_typ contains the real type corresponding to a
  type name so that we can use get the real type from it. *)
                     exec_expr this st expr oldv ->
                     get_real_type newtyp = Some real_typ ->
                     Ops.eval_cast real_typ oldv = Some newv ->
                     exec_expr this st
                     (MkExpression tag (ExpCast newtyp expr) typ dir)
                     newv
  | exec_expr_enum_member : forall tname member ename members this st tag typ dir,
                            name_to_type ge tname = Some (TypEnum ename None members) ->
                            List.In member members ->
                            exec_expr this st
                            (MkExpression tag (ExpTypeMember tname member) typ dir)
                            (ValBaseEnumField ename member)
  (* We need rethink about how to handle senum lookup. *)
  | exec_expr_senum_member : forall tname member ename etyp members fields v this st tag typ dir,
                             name_to_type ge tname = Some (TypEnum ename (Some etyp) members) ->
                             IdentMap.get ename (ge_senum ge) = Some (ValBaseSenum fields) ->
                             AList.get fields member = Some v ->
                             exec_expr this st
                             (MkExpression tag (ExpTypeMember tname member) typ dir)
                             (ValBaseSenumField ename member v)
  | exec_expr_error_member : forall err this st tag typ dir,
                             exec_expr this st
                             (MkExpression tag (ExpErrorMember err) typ dir)
                             (ValBaseError err)
  | exec_expr_other_member : forall expr member v v' this st tag typ dir,
                             exec_expr this st expr v ->
                             get_member v member typ v' ->
                             exec_expr this st
                              (MkExpression tag (ExpExpressionMember expr member) typ dir) v'
  (* ValBaseHeader: setValid, setInvalid, isValid are supposed to be handled in exec_builtin *)
  (* ValBaseUnion: isValid is supposed to be handled in exec_builtin *)
  (* ValBaseStack: next, last, pop_front, push_front are supposed to be handled in exec_builtin *)
  | exec_expr_stack_member_size : forall expr headers size next this st tag typ dir,
                                  exec_expr this st expr (ValBaseStack headers size next) ->
                                  exec_expr this st
                                  (MkExpression tag (ExpExpressionMember expr !"size") typ dir)
                                  (ValBaseBit 32 (Z.of_nat size))
  | exec_expr_stack_member_last_index : forall expr headers size next this st tag typ dir,
                                        exec_expr this st expr (ValBaseStack headers size next)->
                                        (next <> 0)%nat ->
                                        exec_expr this st
                                        (MkExpression tag (ExpExpressionMember expr !"lastIndex") typ dir)
                                        (ValBaseBit 32 (Z.of_nat (next - 1)))
  | exec_expr_stack_member_last_index_undef : forall expr headers size v this st tag typ dir,
                                              exec_expr this st expr (ValBaseStack headers size 0)->
                                              is_uninitialized_value v (TypBit 32) ->
                                              exec_expr this st
                                              (MkExpression tag (ExpExpressionMember expr !"lastIndex") typ dir)
                                              v
  | exec_expr_ternary : forall cond tru fls b v this st tag typ dir,
                        exec_expr this st cond (ValBaseBool b) ->
                        exec_expr this st (if b then tru else fls) v ->
                        exec_expr this st
                        (MkExpression tag (ExpTernary cond tru fls) typ dir)
                        v
  | exec_expr_dont_care : forall this st tag typ dir,
                          exec_expr this st
                          (MkExpression tag ExpDontCare typ dir)
                          ValBaseNull
  | exec_expr_mask : forall expr exprv mask maskv this st tag typ dir,
                     exec_expr this st expr exprv ->
                     exec_expr this st mask maskv ->
                     exec_expr this st
                     (MkExpression tag (ExpMask expr mask) typ dir)
                     (ValBaseSet (ValSetMask exprv maskv))
  | exec_expr_range : forall lo lov hi hiv this st tag typ dir,
                      exec_expr this st lo lov ->
                      exec_expr this st hi hiv ->
                      exec_expr this st
                      (MkExpression tag (ExpRange lo hi) typ dir)
                      (ValBaseSet (ValSetRange lov hiv)).

Inductive exec_exprs : path -> state -> list (@Expression tags_t) -> list Val -> Prop :=
  | exec_exprs_nil : forall this st,
                     exec_exprs this st nil nil
  | exec_exprs_cons : forall this st expr es v vs,
                      exec_expr this st expr v ->
                      exec_exprs this st es vs ->
                      exec_exprs this st (expr :: es) (v :: vs).

(* A generic function for evaluating pure expressions. *)
Fixpoint eval_expr_gen (hook : Expression -> option Val) (expr : @Expression tags_t) : option Val :=
  match hook expr with
  | Some val => Some val
  | None =>
      match expr with
      | MkExpression _ expr _ _ =>
          match expr with
          | ExpInt i => Some (eval_p4int i)
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

Definition eval_expr_gen_sound_1_statement st this hook expr v :=
  forall (H_hook : forall expr v, hook expr = Some v -> exec_expr this st expr v),
  eval_expr_gen hook expr = Some v ->
  exec_expr this st expr v.

Lemma eval_expr_gen_sound_1 : forall st this hook expr v,
  eval_expr_gen_sound_1_statement st this hook expr v
with eval_expr_gen_sound_1_preT : forall st this hook tags expr typ dir v,
  eval_expr_gen_sound_1_statement st this hook (MkExpression tags expr typ dir) v.
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
Qed.

Definition eval_expr_gen_sound_statement st this hook expr v :=
  forall (H_hook : forall expr v, hook expr = Some v -> forall v', exec_expr this st expr v' -> v' = v),
  eval_expr_gen hook expr = Some v ->
  forall v', exec_expr this st expr v' ->
    v' = v.

Lemma eval_expr_gen_sound : forall st this hook expr v,
  eval_expr_gen_sound_statement st this hook expr v
with eval_expr_gen_sound_preT : forall st this hook tags expr typ dir v,
  eval_expr_gen_sound_statement st this hook (MkExpression tags expr typ dir) v.
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
Qed.

(* We might want to prove this lemma in future. *)
(* Lemma eval_expr_gen_complete : forall st this expr v,
  exec_expr this st expr v ->
  eval_expr_gen (fun _ loc => loc_to_val this loc st) expr = Some v. *)

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

Definition filter_in {A} (params : list (A * direction)) : list A :=
  let f param :=
    if is_in (snd param) then [fst param] else [] in
  flat_map f params.

Definition filter_out {A} (params : list (A * direction)) : list A :=
  let f param :=
    if is_out (snd param) then [fst param] else [] in
  flat_map f params.

(* NOTE: We may need to modify for the call convention for overloaded functions. *)
Definition bind_parameters (params : list (path * direction)) (args : list Val) (s s' : state) :=
  s' = update_memory (PathMap.sets (filter_in params) args) s.

(* NOTE: We may need to modify for the call convention for overloaded functions. *)
(* Definition extract_parameters (params : list (path * direction)) (args : list Val) (s : state) :=
  map Some args = PathMap.gets (filter_out params) (get_memory s). *)


Fixpoint extract_parameters (paths : list path) (s : state) : option (list Val) :=
  let st := get_memory s in
  match paths with
  | hd :: tl =>
    match extract_parameters tl s with
    | None => None
    | Some tl' =>
      match PathMap.get hd st with
      | Some v => Some (v :: tl')
      | None => None
      end
    end
  | [] => Some []
  end.

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

Definition add_ctrl_args (oaction : option (@Expression tags_t)) (ctrl_args : list (option (@Expression tags_t))) : option (@Expression tags_t) :=
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

Inductive exec_table_match : path -> state -> ident -> option (list table_entry) -> option action_ref -> Prop :=
  | exec_table_match_intro : forall this_path name keys keyvals const_entries s matched_action,
      let entries := get_entries s (this_path ++ [name]) const_entries in
      let match_kinds := map table_key_matchkind keys in
      exec_exprs this_path s (map table_key_key keys) keyvals ->
      extern_match (combine keyvals match_kinds) entries = matched_action ->
      exec_table_match this_path s name const_entries matched_action.

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

Inductive exec_lexpr : path -> state -> (@Expression tags_t) -> Lval -> signal -> Prop :=
  | exec_lexpr_name : forall name loc this st tag typ dir,
                      exec_lexpr this st
                      (MkExpression tag (ExpName name loc) typ dir)
                      (MkValueLvalue (ValLeftName name loc) typ) SContinue
  | exec_lexpr_member : forall expr lv name this st tag typ dir sig,
                        P4String.equivb !"next" name = false ->
                        exec_lexpr this st expr lv sig ->
                        exec_lexpr this st
                        (MkExpression tag (ExpExpressionMember expr name) typ dir)
                        (MkValueLvalue (ValLeftMember lv name) typ) sig
  (* next < 0 is impossible by semantics. *)
  | exec_lexpr_member_next : forall expr lv headers size next this st tag typ dir sig,
                             exec_lexpr this st expr lv sig ->
                             exec_expr this st expr (ValBaseStack headers size next) ->
                             (next < size)%nat ->
                             exec_lexpr this st
                             (MkExpression tag (ExpExpressionMember expr !"next") typ dir)
                             (MkValueLvalue (ValLeftArrayAccess lv next) typ)
                             (if (next <? size)%nat then sig else (SReject StackOutOfBounds_str))
  (* ATTN: lo and hi interchanged here; lo & hi checked in the typechecker *)
  | exec_lexpr_bitstring_access : forall bits lv lo hi this st tag typ dir sig,
                                   exec_lexpr this st bits lv sig ->
                                   exec_lexpr this st
                                   (MkExpression tag (ExpBitStringAccess bits lo hi) typ dir)
                                   (MkValueLvalue (ValLeftBitAccess lv (N.to_nat hi) (N.to_nat lo)) typ) sig
  | exec_lexpr_array_access : forall array lv idx idxv idxz idxn this st tag typ dir sig,
                               exec_lexpr this st array lv sig ->
                               exec_expr this st idx idxv ->
                               array_access_idx_to_z idxv = Some idxz ->
                               (idxz >= 0)%Z ->
                               Z_to_nat idxz = Some idxn ->
                               exec_lexpr this st
                               (MkExpression tag (ExpArrayAccess array idx) typ dir)
                               (MkValueLvalue (ValLeftArrayAccess lv idxn) typ) sig
  (* Make negative idxz equal to size to stay out of bound as a nat idx. *)
  | exec_lexpr_array_access_neg : forall array lv headers size next idx idxv idxz this st tag typ dir sig,
                                   exec_expr this st array (ValBaseStack headers size next) ->
                                   exec_lexpr this st array lv sig ->
                                   exec_expr this st idx idxv ->
                                   array_access_idx_to_z idxv = Some idxz ->
                                   (idxz < 0)%Z ->
                                   exec_lexpr this st
                                   (MkExpression tag (ExpArrayAccess array idx) typ dir)
                                   (MkValueLvalue (ValLeftArrayAccess lv size) typ) sig.

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
      lval_equivb lv1 lv2 && Nat.eqb msb1 msb2 && Nat.eqb lsb1 lsb2
  | MkValueLvalue (ValLeftArrayAccess lv1 idx1) _, MkValueLvalue (ValLeftArrayAccess lv2 idx2) _ =>
      lval_equivb lv1 lv2 && Nat.eqb idx1 idx2
  | _, _ => false
  end.

Definition update_val_by_loc (this : path) (s : state) (loc : Locator) (v : Val): state :=
  let p := loc_to_path this loc in
  update_memory (PathMap.set p v) s.

Inductive exec_read (this : path) : state -> Lval -> Val -> Prop :=
  | exec_read_name : forall name loc st v typ,
                       loc_to_val this loc st = Some v ->
                       exec_read this st (MkValueLvalue (ValLeftName name loc) typ) v
  | exec_read_by_member : forall lv name st v typ,
                         exec_read_member this st lv name typ v ->
                         exec_read this st (MkValueLvalue (ValLeftMember lv name) typ) v
  (* | exec_read_bit_access
     | exec_read_array_access *)

(* (ValLeftMember (ValBaseStack headers size) !"next") is guaranteed avoided
   by conversions in exec_lexpr to (ValLeftArrayAccess (ValBaseStack headers size) index). *)
with exec_read_member (this : path) : state -> Lval -> P4String -> P4Type -> Val -> Prop :=
  | exec_read_member_header : forall is_valid fields st lv name typ v,
                          exec_read this st lv (ValBaseHeader fields is_valid) ->
                          read_header_field is_valid fields name typ v ->
                          exec_read_member this st lv name typ v
  | exec_read_member_struct : forall fields st lv name typ v,
                          exec_read this st lv (ValBaseStruct fields) ->
                          AList.get fields name = Some v ->
                          exec_read_member this st lv name typ v
  | exec_read_member_union: forall fields st lv name typ v,
                        exec_read this st lv (ValBaseUnion fields) ->
                        AList.get fields name = Some v ->
                        exec_read_member this st lv name typ v.

(* TODO: write to the field of an invalid header in a union makes the possibly existing valid header
    take undefined value. It should be guaranteed there is at most one valid header in a union. *)
Inductive write_header_field: Val -> P4String -> Val -> Val -> Prop :=
  (* Writing to an invalid header does not change "any state that is currently defined in the system".
     Besides, the reading afterwards still produces undefined behavior. *)
  | write_header_field_intro : forall fields fname bool fv fields',
                               AList.set fields fname fv = Some fields' ->
                               write_header_field (ValBaseHeader fields bool) fname fv
                               (ValBaseHeader fields' bool).

Fixpoint update_union_member (fields: P4String.AList tags_t Val) (fname: P4String)
                             (hfields: P4String.AList tags_t Val) (is_valid: bool) :
                             option (P4String.AList tags_t Val) :=
  match fields with
  | [] => Some []
  | (fname', ValBaseHeader hfields' is_valid') :: tl =>
    match update_union_member tl fname hfields is_valid with
    | None => None
    | Some tl' =>
      if is_valid
      then if P4String.equivb fname fname'
          then Some ((fname, ValBaseHeader hfields true) :: tl')
          else Some ((fname', ValBaseHeader hfields' false) :: tl')
      else if P4String.equivb fname fname'
          then Some ((fname', ValBaseHeader hfields' false) :: tl')
          else Some ((fname', ValBaseHeader hfields' is_valid') :: tl')
    end
  | _ :: _ => None
  end.

(* (ValLeftMember (ValBaseStack headers size) !"next") is guaranteed avoided
   by conversions in exec_lexpr to (ValLeftArrayAccess (ValBaseStack headers size) index).
   Also, value here if derived from lvalue in the caller, so last_string does not exist. *)
Inductive update_member : Val -> P4String -> Val -> Val -> Prop :=
  | update_member_header : forall fields is_valid fname fv v,
                           write_header_field (ValBaseHeader fields is_valid) fname fv v ->
                           update_member (ValBaseHeader fields is_valid) fname fv v
  | update_member_struct : forall fields' fields fname fv,
                           AList.set fields fname fv = Some fields' ->
                           update_member (ValBaseStruct fields) fname fv (ValBaseStruct fields')
  | update_member_union : forall hfields (is_valid: bool) fields fields' is_valid fname,
                          update_union_member fields fname hfields is_valid = Some fields' ->
                          update_member (ValBaseUnion fields) fname (ValBaseHeader hfields is_valid)
                          (ValBaseUnion fields').

Fixpoint update_stack_header (headers: list Val) (idx: nat) (v: Val) : list Val :=
  match headers, idx with
  | header :: tl, O => v :: tl
  | header :: tl, S n => header :: (update_stack_header tl n v)
  | [], _ => []
  end.

Definition update_bitstring (i : Z) (lsb : nat) (msb : nat) (n : Z) : Z :=
  let lsbz := Z.of_nat lsb in
  let msbz := Z.of_nat msb in
  let new_n := (Z.shiftl n lsbz) in
  let mask := (Z.lxor (-1) (Z.shiftl (Z.pow 2 (msbz - lsbz + 1) - 1) lsbz))%Z in
  Z.lxor (Z.land i mask) new_n.


Inductive exec_write (this : path) : state -> Lval -> Val -> state -> Prop :=
  | exec_write_name : forall name loc st rhs typ st',
                         update_val_by_loc this st loc rhs = st' ->
                         exec_write this st (MkValueLvalue (ValLeftName name loc) typ) rhs st'
  | exec_write_member : forall lv fname v v' st rhs typ st',
                           exec_read this st lv v ->
                           update_member v fname rhs v' ->
                           exec_write this st lv v' st' ->
                           exec_write this st (MkValueLvalue (ValLeftMember lv fname) typ) rhs st'
  | exec_write_bit_access_bit : forall lv bitsv w bitsz bitsz' lsb msb w' n st typ st',
                                   exec_read this st lv (ValBaseBit w bitsz) ->
                                   (lsb <= msb < w)%nat ->
                                   update_bitstring bitsv lsb msb n = bitsz' ->
                                   exec_write this st lv (ValBaseBit w (BitArith.mod_bound w bitsz')) st' ->
                                   exec_write this st (MkValueLvalue (ValLeftBitAccess lv msb lsb) typ)
                                   (ValBaseBit w' n) st'
   | exec_write_bit_access_int : forall lv bitsv w bitsz bitsz' lsb msb w' n st typ st',
                                   exec_read this st lv (ValBaseInt w bitsz) ->
                                   (lsb <= msb < w)%nat ->
                                   update_bitstring bitsv lsb msb n = bitsz' ->
                                   exec_write this st lv (ValBaseInt w (IntArith.mod_bound w bitsz')) st' ->
                                   exec_write this st (MkValueLvalue (ValLeftBitAccess lv msb lsb) typ)
                                   (ValBaseBit w' n) st'
  (* By update_stack_header, if idx >= size, state currently defined is unchanged. *)
  | exec_write_array_access : forall lv headers size next (idx: nat) headers' idx st rhs typ st',
                                 exec_read this st lv (ValBaseStack headers size next) ->
                                 update_stack_header headers idx rhs = headers' ->
                                 exec_write this st lv (ValBaseStack headers' size next) st' ->
                                 exec_write this st (MkValueLvalue (ValLeftArrayAccess lv idx) typ) rhs st'.

Definition argument : Type := (option Val) * (option Lval).

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
Inductive exec_arg : path -> state -> option (@Expression tags_t) -> direction -> argument -> signal -> Prop :=
  | exec_arg_in : forall this st expr val,
                  exec_expr this st expr val ->
                  exec_arg this st (Some expr) In (Some val, None) SContinue
  | exec_arg_out_dontcare : forall this st,
                            exec_arg this st None Out (None, None) SContinue
  | exec_arg_out : forall this st expr lval sig,
                   exec_lexpr this st expr lval sig ->
                   exec_arg this st (Some expr) Out (None, Some lval) sig
  | exec_arg_inout : forall this st expr lval val sig,
                     exec_lexpr this st expr lval sig ->
                     exec_read this st lval val ->
                     exec_arg this st (Some expr) InOut (Some val, Some lval) sig.

(* exec_arg on a list *)
Inductive exec_args : path -> state -> list (option (@Expression tags_t)) -> list direction -> list argument -> signal -> Prop :=
| exec_args_nil: forall p s,
                 exec_args p s nil nil nil SContinue
| exec_args_cons : forall p s exp exps dir dirs arg args sig sig',
                   exec_arg p s exp dir arg sig ->
                   exec_args p s exps dirs args sig' ->
                   exec_args p s (exp :: exps) (dir :: dirs) (arg :: args)
                   (if is_continue sig then sig' else sig).
(* After SimplExpr, sig here in fact can only be SReject.
   Todo: the current behavior is after getting a non-continue signal, all args are still evaluated.
         SimplExpr makes execution stops at the non-continue signal. Even though exec_args won't
         affect state, it is still good to make the two behavior consistent. *)
(* | exec_args_cons_other : forall p s exp exps dir dirs arg args sig sig',
                         exec_arg p s exp dir arg sig ->
                         not_continue sig = true ->
                         exec_args p s exps dirs args sig' ->
                         exec_args p s (exp :: exps) (dir :: dirs) (arg :: args) sig. *)

Inductive exec_write_option : path -> state -> option Lval -> Val -> state -> Prop :=
| exec_write_option_some : forall p s lval val s',
                           exec_write p s lval val s' ->
                           exec_write_option p s (Some lval) val s'
| exec_write_option_none : forall p s val,
                           exec_write_option p s None val s.

Inductive exec_write_options : path -> state -> list (option Lval) -> list Val -> state -> Prop :=
| exec_write_options_nil : forall p s,
                           exec_write_options p s nil nil s
| exec_write_options_cons : forall p s1 s2 s3 lv lvs val vals,
                            exec_write_option p s1 lv val s2 ->
                            exec_write_options p s2 lvs vals s3 ->
                            exec_write_options p s1 (lv :: lvs) (val :: vals) s3.

Definition extract_invals (args : list argument) : list Val :=
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

Fixpoint match_switch_case (member: P4String) (cases : list StatementSwitchCase) : option Block :=
  let fix find_next_action cases :=
    match cases with
    | [] => None
    | StatSwCaseAction _ _ code :: _ => Some code
    | _ :: tl => find_next_action tl
    end in
  match cases with
  | [] => None
  | StatSwCaseAction _ (StatSwLabName _ label) code :: tl =>
    if P4String.equivb label member then Some code
    else match_switch_case member tl
  | StatSwCaseFallThrough _ (StatSwLabName _ label) :: tl =>
    if P4String.equivb label member then find_next_action tl
    else match_switch_case member tl
  | StatSwCaseAction _ (StatSwLabDefault _) code :: _ => Some code
  | StatSwCaseFallThrough _ (StatSwLabDefault _) :: _ => None
  end.

Definition table_retv (b : bool) (ename member : P4String) : ValueBase :=
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

Inductive exec_builtin : path -> state -> Lval -> ident -> list Val -> state -> signal -> Prop :=
  (* this_path s lv fname args s' sig *) (* TODO *)
  .

Definition empty_statement := (MkStatement dummy_tags StatEmpty StmUnit).
Definition empty_block := (BlockEmpty dummy_tags).


Inductive exec_stmt : path -> inst_mem -> state -> (@Statement tags_t) -> state -> signal -> Prop :=
  | exec_stmt_assign : forall lhs lv rhs v this_path inst_m st tags typ st' sig,
                        exec_expr this_path st rhs v ->
                        exec_lexpr this_path st lhs lv sig ->
                        (if is_continue sig then exec_write this_path st lv v st' else True) ->
                        exec_stmt this_path inst_m st
                        (MkStatement tags (StatAssignment lhs rhs) typ)
                        (if is_continue sig then st' else st)
                        (if is_continue sig then SContinue else sig)
  | exec_stmt_assign_func_call : forall lhs lv rhs v this_path inst_m st tags typ st' st'' sig sig',
                                 exec_call this_path inst_m st rhs st' sig' ->
                                 exec_lexpr this_path st lhs lv sig ->
                                 (if is_return sig' then get_return_val sig' = Some v else True) ->
                                 (if is_return sig' then exec_write this_path st' lv v st'' else True)->
                                 exec_stmt this_path inst_m st
                                 (MkStatement tags (StatAssignment lhs rhs) typ)
                                 (if not_continue sig then st else if not_return sig' then st' else st'')
                                 (if not_continue sig then sig else if not_return sig' then sig' else SContinue)
  | exec_stmt_method_call : forall this_path inst_m st tags func args typ st' sig sig',
                            exec_call this_path inst_m st
                              (MkExpression dummy_tags (ExpFunctionCall func nil args) TypVoid Directionless)
                              st' sig ->
                            force_continue_signal sig = sig' ->
                            exec_stmt this_path inst_m st
                            (MkStatement tags (StatMethodCall func nil args) typ) st' sig'
  | exec_stmt_direct_application : forall this_path inst_m st tags typ' args typ st' sig sig',
                                   exec_call this_path inst_m st
                                      (MkExpression dummy_tags
                                        (ExpFunctionCall (direct_application_expression typ') nil (map Some args)) TypVoid Directionless)
                                      st' sig ->
                                   force_continue_signal sig = sig' ->
                                   exec_stmt this_path inst_m st
                                   (MkStatement tags (StatDirectApplication typ' args) typ) st' sig'
  | exec_stmt_conditional_some_fls : forall cond tru fls b this_path inst_m st tags typ st' sig,
                                     exec_expr this_path st cond (ValBaseBool b) ->
                                     exec_stmt this_path inst_m st (if b then tru else fls) st' sig ->
                                     exec_stmt this_path inst_m st
                                     (MkStatement tags (StatConditional cond tru (Some fls)) typ) st' sig
  | exec_stmt_conditional_none_fls : forall cond tru b this_path inst_m st tags typ st' sig,
                                     exec_expr this_path st cond (ValBaseBool b) ->
                                     exec_stmt this_path inst_m st (if b then tru else empty_statement) st' sig ->
                                     exec_stmt this_path inst_m st
                                     (MkStatement tags (StatConditional cond tru None) typ) st SContinue
  | exec_stmt_block : forall block this_path inst_m st tags typ st' sig,
                      exec_block this_path inst_m st block st' sig ->
                      exec_stmt this_path inst_m st
                      (MkStatement tags (StatBlock block) typ) st' sig
  | exec_stmt_exit : forall this_path inst_m (st: state) tags typ st,
                     exec_stmt this_path inst_m st
                     (MkStatement tags StatExit typ) st SExit
  | exec_stmt_return_none : forall this_path inst_m (st: state) tags typ st,
                            exec_stmt this_path inst_m st
                            (MkStatement tags (StatReturn None) typ) st SReturnNull
  | exec_stmt_return_some : forall e v this_path inst_m (st: state) tags typ st,
                            exec_expr this_path st e v ->
                            exec_stmt this_path inst_m st
                            (MkStatement tags (StatReturn (Some e)) typ) st (SReturn v)
  | exec_stmt_empty : forall this_path inst_m (st: state) tags typ st,
                      exec_stmt this_path inst_m st
                      (MkStatement tags StatEmpty typ) st SContinue
  | exec_stmt_switch_none: forall e b ename member cases  typ dir this_path inst_m (st st': state) tags tags' typ' st st',
                           exec_call this_path inst_m st e st' (SReturn (table_retv b ename member)) ->
                           match_switch_case member cases = None ->
                           exec_stmt this_path inst_m st
                           (MkStatement tags (StatSwitch (MkExpression tags' (ExpExpressionMember e !"action_run") typ dir) cases) typ') st' SContinue
  | exec_stmt_switch_some: forall e b ename member cases block typ dir this_path inst_m (st st': state) st'' tags tags' typ' st st' sig,
                           exec_call this_path inst_m st e st' (SReturn (table_retv b ename member)) ->
                           match_switch_case member cases = Some block ->
                           exec_block this_path inst_m st' block st'' sig ->
                           exec_stmt this_path inst_m st
                           (MkStatement tags (StatSwitch (MkExpression tags' (ExpExpressionMember e !"action_run") typ dir) cases) typ') st'' sig
  | exec_stmt_variable : forall typ' name e v loc this_path inst_m st tags typ st',
                         exec_expr this_path st e v ->
                         exec_write this_path st (MkValueLvalue (ValLeftName (BareName name) loc) typ') v st' ->
                         exec_stmt this_path inst_m st
                         (MkStatement tags (StatVariable typ' name (Some e) loc) typ) st' SContinue
  | exec_stmt_variable_func_call : forall typ' name e v loc this_path inst_m st tags typ st' st'',
                                   exec_call this_path inst_m st e st' (SReturn v) ->
                                   exec_write this_path st' (MkValueLvalue (ValLeftName (BareName name) loc) typ') v st'' ->
                                   exec_stmt this_path inst_m st
                                   (MkStatement tags (StatVariable typ' name (Some e) loc) typ) st'' SContinue
  | exec_stmt_variable_func_call' : forall typ' name e loc this_path inst_m st tags typ st' st'' sig,
                                    exec_call this_path inst_m st e st' sig ->
                                    is_return sig = false ->
                                    exec_stmt this_path inst_m st
                                    (MkStatement tags (StatVariable typ' name (Some e) loc) typ) st'' sig
  | exec_stmt_variable_undef : forall typ' name loc v this_path inst_m st tags typ st',
                               is_uninitialized_value v typ' ->
                               exec_write this_path st (MkValueLvalue (ValLeftName (BareName name) loc) typ') v st' ->
                               exec_stmt this_path inst_m st
                               (MkStatement tags (StatVariable typ' name None loc) typ) st' SContinue
  | exec_stmt_constant: forall typ' name v loc this_path inst_m st tags typ st',
                        exec_write this_path st (MkValueLvalue (ValLeftName (BareName name) loc) typ') v st' ->
                        exec_stmt this_path inst_m st
                        (MkStatement tags (StatConstant typ' name v loc) typ) st' SContinue
  (* StatInstantiation not considered yet *)

with exec_block : path -> inst_mem -> state -> (@Block tags_t) -> state -> signal -> Prop :=
  | exec_block_nil : forall this_path inst_m st tags,
                     exec_block this_path inst_m st (BlockEmpty tags) st SContinue
  | exec_block_cons : forall stmt rest this_path inst_m st st' st'' sig sig',
                      exec_stmt this_path inst_m st stmt st' sig ->
                      exec_block this_path inst_m st' (if is_continue sig then rest else empty_block) st'' sig' ->
                      exec_block this_path inst_m st (BlockCons stmt rest)
                      st'' (if is_continue sig then sig' else sig)

with exec_call : path -> inst_mem -> state -> (@Expression tags_t) -> state -> signal -> Prop :=
  | exec_call_builtin : forall this_path inst_m s tags tag' lhs fname tparams params typ' args typ dir argvals s' sig sig' sig'' lv,
      let dirs := map get_param_dir params in
      exec_lexpr this_path s lhs lv sig ->
      exec_args this_path s args dirs argvals sig' ->
      exec_builtin this_path s lv fname (extract_invals argvals) s' sig'' ->
      exec_call this_path inst_m s (MkExpression tags (ExpFunctionCall
          (MkExpression tag' (ExpExpressionMember lhs fname) (TypFunction (MkFunctionType tparams params FunBuiltin typ')) dir)
          nil args) typ dir)
          (if not_continue sig then s else if not_continue sig' then s else s')
          (if not_continue sig then sig else if not_continue sig' then sig' else sig'')

  (* eval the call expression:
       1. eval arguments;
       2. lookup the function to call;
       3. call the function by exec_funcall;
       4. write back out parameters.
  *)
  | exec_call_func : forall this_path inst_m s tags func targs args typ dir argvals obj_path fd outvals s' s'' sig sig',
      let dirs := get_arg_directions func in
      exec_args this_path s args dirs argvals sig ->
      lookup_func this_path inst_m func = Some (obj_path, fd) ->
      exec_func obj_path inst_m s fd targs (extract_invals argvals) s' outvals sig' ->
      exec_write_options this_path s' (extract_outlvals dirs argvals) outvals s'' ->
      exec_call this_path inst_m s (MkExpression tags (ExpFunctionCall func targs args) typ dir)
      (if is_continue sig then s'' else s)
      (if is_continue sig then sig' else sig)
  (* The only example of non-continue signals during exec_args (after SimplExpr) is hd.extract(hdrs.next). *)
  (* | exec_call_other : forall this_path inst_m s tags func args typ dir argvals sig,
      let dirs := get_arg_directions func in
      exec_args this_path s args dirs argvals sig ->
      not_continue sig = true ->
      exec_call this_path inst_m s (MkExpression tags (ExpFunctionCall func nil args) typ dir) s sig *)

(* Only in/inout arguments in the first list Val and only out/inout arguments in the second list Val. *)
with exec_func : path -> inst_mem -> state -> fundef -> list P4Type -> list Val -> state -> list Val -> signal -> Prop :=
  | exec_func_internal : forall obj_path inst_m s params init body args s''' args' s' s'' sig sig' sig'',
      bind_parameters (map (map_fst (fun param => loc_to_path obj_path param)) params) args s s' ->
      exec_block obj_path inst_m s' init  s'' sig ->
      not_continue sig = false ->
      exec_block obj_path inst_m s'' body s''' sig' ->
      force_return_signal sig' = sig'' ->
      extract_parameters (filter_out (map (map_fst (fun param => loc_to_path obj_path param)) params)) s''' = Some args'->
      exec_func obj_path inst_m s (FInternal params init body) nil args s''' args' sig''

  | exec_func_table_match : forall obj_path name inst_m keys actions action_name ctrl_args action default_action const_entries s s',
      exec_table_match obj_path s name const_entries (Some (mk_action_ref action_name ctrl_args)) ->
      add_ctrl_args (get_action actions name) ctrl_args = Some action ->
      exec_call obj_path inst_m s action s' SReturnNull ->
      exec_func obj_path inst_m s (FTable name keys actions default_action const_entries) nil nil s' nil
            (SReturn (table_retv true !"" (get_expr_func_name action)))

  | exec_func_table_default : forall obj_path name inst_m keys actions default_action const_entries s s',
      exec_table_match obj_path s name const_entries None ->
      exec_call obj_path inst_m s default_action s' SReturnNull ->
      exec_func obj_path inst_m s (FTable name keys actions (Some default_action) const_entries) nil nil s' nil
            (SReturn (table_retv false !"" (get_expr_func_name default_action)))

  (* This will not happen in the latest spec. *)
  (* | exec_func_table_noaction : forall obj_path name inst_m keys actions const_entries s,
      exec_table_match obj_path s name const_entries SReturnNull ->
      exec_func obj_path inst_m s (FTable name keys actions None const_entries) nil s nil None *)

  | exec_func_external : forall obj_path inst_m class_name name (* params *) m es es' targs args args' sig,
      exec_extern es class_name name obj_path targs args es' args' sig ->
      exec_func obj_path inst_m (m, es) (FExternal class_name name (* params *)) targs args (m, es') args' sig.

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

Fixpoint load_decl (p : path) (ge : genv_func) (decl : @Declaration tags_t) : genv_func :=
  match decl with
  | DeclParser _ name type_params params constructor_params locals states =>
      let params := map get_param_name_dir params in
      let params := map (map_fst (fun param => LInstance [param])) params in
      let params := filter (compose is_directional snd) params in
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
      let params := filter (compose is_directional snd) params in
      let ge := fold_left (load_decl (p ++ [name])) locals ge in
      let init := process_locals locals in
      PathMap.set (p ++ [name]) (FInternal params init apply) ge
  | DeclFunction _ _ name type_params params body =>
      let params := map get_param_name_dir params in
      let params := map (map_fst (fun param => LGlobal [name; param])) params in
      PathMap.set (p ++ [name]) (FInternal params BlockNil body) ge
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
      let params := map get_param_name_dir params in
      let ctrl_params := map (fun name => (name, In)) (map get_param_name ctrl_params) in
      let combined_params :=
        if path_equivb p [] then
          map (map_fst (fun param => LGlobal [name; param])) (params ++ ctrl_params)
        else
          map (map_fst (fun param => LInstance [name; param])) (params ++ ctrl_params) in
      PathMap.set (p ++ [name]) (FInternal combined_params BlockNil body) ge
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
