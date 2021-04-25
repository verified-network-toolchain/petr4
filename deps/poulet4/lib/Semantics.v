Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Program.Program.
Require Import Poulet4.Typed.
Require Import Poulet4.Syntax.
Require Import Poulet4.P4Int.
Require Import Poulet4.Ops.
Require Import Poulet4.Maps.
Require Export Poulet4.Target.
Require Export Poulet4.SyntaxUtil.
Import ListNotations.

Section Semantics.

Context {tags_t: Type}.
Notation Val := (@ValueBase tags_t).

Notation ident := (P4String.t tags_t).
Notation path := (list ident).
Notation P4Int := (P4Int.t tags_t).
Notation P4String := (P4String.t tags_t).

Context `{@Target tags_t (@Expression tags_t)}.
Local Hint Resolve extern_sem : typeclass_instances.

Definition mem := @PathMap.t tags_t Val.

Definition state : Type := mem * extern_state.

Definition set_memory m (s : state) : state :=
  let (_, es) := s in (m, es).

Definition update_memory (f : mem -> mem) (s : state) : state :=
  let (m, es) := s in (f m, es).

Definition get_memory (s : state) : mem :=
  let (m, _) := s in m.

Definition loc_to_path (this : path) (loc : Locator) : option path :=
  match loc with
  | LGlobal p => Some p
  | LInstance p => Some (this ++ p)
  end.

Inductive fundef :=
  | FInternal
      (* true -> global; false -> instance *)
      (* Do we need this global flag? *)
      (global : bool)
      (params : list (ident * direction))
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

Definition genv := @PathMap.t tags_t fundef.
Definition genv_typ := @IdentMap.t tags_t (@P4Type tags_t).
Definition genv_senum := @IdentMap.t tags_t Val.

Definition name_to_type (ge_typ: genv_typ) (typ : @Typed.name tags_t):
  option (@P4Type tags_t) :=
  match typ with
  | BareName id => IdentMap.get id ge_typ
  | QualifiedName _ id => IdentMap.get id ge_typ
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

Definition gen_ge_typ (l: list (@Declaration tags_t)): option genv_typ :=
  add_decls_to_ge_typ (Some IdentMap.empty) l.

Variable ge : genv.
Variable ge_typ : genv_typ.
Variable ge_senum : genv_senum.

Definition get_real_type (typ: @P4Type tags_t): option (@P4Type tags_t) :=
  match typ with
  | TypTypeName name => name_to_type ge_typ name
  | _ => Some typ
  end.

Definition eval_p4int (n: P4Int) : Val :=
  match P4Int.width_signed n with
  | None => ValBaseInteger (P4Int.value n)
  | Some (w, true) => ValBaseInt w (P4Int.value n)
  | Some (w, false) => ValBaseBit w (P4Int.value n)
  end.

Definition loc_to_val (this : path) (loc : Locator) (s : state) : option Val :=
  let p := loc_to_path this loc in
  match p with
  | Some p' =>
    match PathMap.get p' (get_memory s) with
    | Some v => Some v
    | _ => None
    end
  | _ => None
  end.

Definition array_access_idx_to_z (v : Val) : (option Z) :=
  match v with
  | ValBaseInt _ value
  | ValBaseBit _ value
  | ValBaseInteger value => Some value
  | _ => None
  end.

Definition bitstring_slice_bits_to_z (v : Val) : option (nat * Z) :=
  match v with
  | ValBaseInt width value
  | ValBaseBit width value => Some (width, value)
  | _ => None
  end.

Definition z_to_nat (i : Z) : option nat :=
  if (i >=? 0)%Z then Some (Z.to_nat i) else None.


(* Ref:When accessing the bits of negative numbers, all functions below will
   use the two's complement representation.
   For instance, -1 will correspond to an infinite stream of true bits.
   https://coq.inria.fr/library/Coq.ZArith.BinIntDef.html *)
Definition bitstring_slice (i : Z) (lo : N) (hi : N) : Z :=
  let mask := (Z.pow 2 (Z.of_N (hi - lo + 1)) - 1)%Z in
  Z.land (Z.shiftr i (Z.of_N lo)) mask.

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
  | exec_expr_array_access: forall array headers size next idx idxv idxz idxn header this st tag typ dir,
                            exec_expr this st array (ValBaseStack headers size next) ->
                            exec_expr this st idx idxv ->
                            array_access_idx_to_z idxv = Some idxz ->
                            (0 <= idxz < (Z.of_nat size))%Z ->
                            z_to_nat idxz = Some idxn ->
                            List.nth_error headers idxn = Some header ->
                            exec_expr this st
                            (MkExpression tag (ExpArrayAccess array idx) typ dir)
                            header
  | exec_expr_array_access_undef: forall array headers size next idx idxv idxz v this st tag typ dir,
                                  exec_expr this st array (ValBaseStack headers size next) ->
                                  exec_expr this st idx idxv ->
                                  array_access_idx_to_z idxv = Some idxz ->
                                  (idxz < 0)%Z \/ (idxz >= (Z.of_nat size))%Z ->
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
  | exec_expr_type_member_enum : forall tname member ename members this st tag typ dir,
                                 name_to_type ge_typ tname = Some (TypEnum ename None members) ->
                                 List.In member members ->
                                 exec_expr this st
                                 (MkExpression tag (ExpTypeMember tname member) typ dir)
                                 (ValBaseEnumField ename member)
  (* We need rethink about how to handle senum lookup. *)
  | exec_expr_type_member_senum : forall tname member ename etyp members fields v this st tag typ dir,
                                  name_to_type ge_typ tname = Some (TypEnum ename (Some etyp) members) ->
                                  IdentMap.get ename ge_senum = Some (ValBaseSenum fields) ->
                                  AList.get fields member = Some v ->
                                  exec_expr this st
                                  (MkExpression tag (ExpTypeMember tname member) typ dir)
                                  (ValBaseSenumField ename member v)
  | exec_expr_error_member : forall err this st tag typ dir,
                             exec_expr this st
                             (MkExpression tag (ExpErrorMember err) typ dir)
                             (ValBaseError err)
  (* | exec_expr_expression_member omitted for now *)
  | exec_expr_ternary_tru : forall cond tru truv fls this st tag typ dir,
                            exec_expr this st cond (ValBaseBool true) ->
                            exec_expr this st tru truv ->
                            exec_expr this st
                            (MkExpression tag (ExpTernary cond tru fls) typ dir)
                            truv
  | exec_expr_ternary_fls : forall cond tru fls flsv this st tag typ dir,
                            exec_expr this st cond (ValBaseBool false) ->
                            exec_expr this st fls flsv ->
                            exec_expr this st
                            (MkExpression tag (ExpTernary cond tru fls) typ dir)
                            flsv
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

Definition filter_in (params : list (path * direction)) : list path :=
  let f param :=
    if is_in (snd param) then [fst param] else [] in
  flat_map f params.

Definition filter_out (params : list (path * direction)) : list path :=
  let f param :=
    if is_out (snd param) then [fst param] else [] in
  flat_map f params.

(* NOTE: We may need to modify for the call convention for overloaded functions. *)
Definition bind_parameters (params : list (path * direction)) (args : list Val) (s s' : state) :=
  s' = update_memory (PathMap.sets (filter_in params) args) s.

(* NOTE: We may need to modify for the call convention for overloaded functions. *)
Definition extract_parameters (params : list (path * direction)) (args : list Val) (s : state) :=
  map Some args = PathMap.gets (filter_out params) (get_memory s).

Inductive signal : Type :=
   | SContinue : signal
   | SReturn : option Val -> signal
   | SExit
   (* parser's states include accept and reject *)
   | SReject : string -> signal.

Definition get_external_state (s : state) :=
  let (_, es) := s in es.

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
Axiom dummy_tags : tags_t.

Definition add_ctrl_args (oaction : option (@Expression tags_t)) (ctrl_args : list (option (@Expression tags_t))) : option (@Expression tags_t) :=
  match oaction with
  | Some action =>
      match action with
      | MkExpression _ (ExpFunctionCall f type_args args) _ dir =>
          Some (MkExpression dummy_tags (ExpFunctionCall f type_args (args ++ ctrl_args)) dummy_type dir)
      | _ => None
      end
  | None => None
  end.

Definition TableKeyKey (key : @TableKey tags_t) : (@Expression tags_t) :=
  match key with
  | MkTableKey _ e _ => e
  end.

Definition TableKeyMatchKind (key : @TableKey tags_t) : ident :=
  match key with
  | MkTableKey _ _ match_kind => match_kind
  end.

Definition getEntries (s : state) (table : path) (const_entries : option (list table_entry)) : (list table_entry) :=
  match const_entries with
  | Some entries => entries
  | None => extern_get_entries (get_external_state s) table
  end.

Inductive exec_table_match : path -> state -> ident -> option (list table_entry) -> option action_ref -> Prop :=
  | exec_table_match_intro : forall this_path name keys keyvals const_entries s matched_action,
      let entries := getEntries s (this_path ++ [name]) const_entries in
      let match_kinds := map TableKeyMatchKind keys in
      exec_exprs this_path s (map TableKeyKey keys) keyvals ->
      extern_match (combine keyvals match_kinds) entries = matched_action ->
      exec_table_match this_path s name const_entries matched_action.

Inductive Lval : Type.

Definition argument : Type := (option Val) * (option Lval).

Definition get_arg_directions (func : @Expression tags_t) : list direction :=
  match func with
  | MkExpression _ _ (TypFunction (MkFunctionType _ params _ _)) _ =>
      map get_param_dir params
  | _ => nil (* impossible *)
  end.

Inductive exec_args : path -> state -> list (option (@Expression tags_t)) -> list direction -> list argument -> Prop :=.
(* TODO *)

Inductive exec_copy_out : path -> state -> list Lval -> list Val -> state -> Prop :=.
(* TODO *)
(* This depends on assigning to lvalues. *)

Inductive inst_mem_val :=
  | IMVal (v : Val)
  (* Instances, including parsers, controls, and external objects. *)
  | IMInst (class : ident) (p : path).

Definition inst_mem := @PathMap.t tags_t inst_mem_val.

(* TODO Should we move this to GenLoc? *)
Definition apply_string : ident := {| P4String.tags := dummy_tags; P4String.str := "apply" |}.

Definition lookup_func (this_path : path) (inst_m : inst_mem) (func : @Expression tags_t) : option (path * fundef) :=
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
  (* TODO add other built-in functions *)
  (* apply and builtin, but builtin unsupported yet. *)
  | MkExpression _ (ExpExpressionMember expr name) _ _ =>
      if P4String.equivb name apply_string then
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
      (* If the method name does not match any of the keywords, it is an external method. *)
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

Definition extract_invals (args : list argument) : list Val :=
  let f arg :=
    match arg with
    | (Some v, _) => [v]
    | (None, _) => []
    end in
  flat_map f args.

Definition extract_outlvals (args : list argument) : list Lval :=
  let f arg :=
    match arg with
    | (_, Some lv) => [lv]
    | (_, None) => []
    end in
  flat_map f args.

Inductive exec_lvalue_expr : path -> state -> (@Expression tags_t) -> (@ValueLvalue tags_t) -> Prop :=
  | exec_lvalue_expr_name : forall name loc this st tag typ dir,
                            exec_lvalue_expr this st
                            (MkExpression tag (ExpName name loc) typ dir)
                            (MkValueLvalue (ValLeftName name loc) typ)
  | exec_lvalue_expr_member : forall expr lv name this st tag typ dir,
                              exec_lvalue_expr this st expr lv ->
                              exec_lvalue_expr this st
                              (MkExpression tag (ExpExpressionMember expr name) typ dir)
                              (MkValueLvalue (ValLeftMember lv name) typ)
  (* ATTN: lo and hi interchanged here *)
  | exec_lvalue_bitstring_access : forall bits lv lo hi this st tag typ dir,
                                   exec_lvalue_expr this st bits lv ->
                                   exec_lvalue_expr this st
                                   (MkExpression tag (ExpBitStringAccess bits lo hi) typ dir)
                                   (MkValueLvalue (ValLeftBitAccess lv (N.to_nat hi) (N.to_nat lo)) typ)
  (* Since array size is unknown here, only the lower-bound undefined behavior is defined.
     The upper bound should be handled after getting the value from lvalue. *)
  | exec_lvalue_array_access : forall array lv idx idxv idxz idxn this st tag typ dir,
                               exec_lvalue_expr this st array lv ->
                               exec_expr this st idx idxv ->
                               array_access_idx_to_z idxv = Some idxz ->
                               z_to_nat idxz = Some idxn ->
                               exec_lvalue_expr this st
                               (MkExpression tag (ExpArrayAccess array idx) typ dir)
                               (MkValueLvalue (ValLeftArrayAccess lv idxn) typ)
  | exec_lvalue_array_access_undef_lo : forall array alv idx idxv idxz lv this st tag typ dir,
                                        exec_lvalue_expr this st array alv ->
                                        exec_expr this st idx idxv ->
                                        array_access_idx_to_z idxv = Some idxz ->
                                        (idxz < 0)%Z ->
                                        exec_lvalue_expr this st
                                        (MkExpression tag (ExpArrayAccess array idx) typ dir)
                                        lv.

Definition update_val_by_loc (this : path) (s : state) (loc : Locator) (v : Val): option state :=
  let p := loc_to_path this loc in
  match p with
  | Some p' => Some (update_memory (PathMap.set p' v) s)
  | _ => None
  end.

Definition assign_lvalue (this : path) (st : state) (lhs : @ValueLvalue tags_t) (rhs : Val) : option (state * signal) :=
  match lhs with
  | MkValueLvalue (ValLeftName name loc) _ =>
    let opt_st := update_val_by_loc this st loc rhs in
      match opt_st with
      | Some st' => Some (st', SContinue)
      | _ => None
      end
  | _ => None (* omitted for now *)
  end.

Inductive exec_stmt : path -> inst_mem -> state -> (@Statement tags_t) -> state -> signal -> Prop :=
  | eval_stmt_assignment : forall lhs lv rhs v this_path inst_m st tag typ st' sig,
                           exec_lvalue_expr this_path st lhs lv ->
                           exec_expr this_path st rhs v ->
                           assign_lvalue this_path st lv v = Some (st', SContinue) ->
                           exec_stmt this_path inst_m st
                           (MkStatement tag (StatAssignment lhs rhs) typ) st' sig

with exec_block : path -> inst_mem -> state -> (@Block tags_t) -> state -> signal -> Prop :=
with exec_call : path -> inst_mem -> state -> (@Expression tags_t) -> state -> option Val -> Prop :=
  (* eval the call expression:
       1. lookup the function to call;
       2. eval arguments;
       3. call the function by exec_funcall;
       4. write back out parameters.
  *)
  | exec_call_intro : forall this_path inst_m s tags func args typ dir argvals obj_path fd outvals s' s'' vret,
      let dirs := get_arg_directions func in
      exec_args this_path s args dirs argvals ->
      lookup_func this_path inst_m func = Some (obj_path, fd) ->
      exec_func obj_path inst_m s fd (extract_invals argvals) s' outvals vret ->
      exec_copy_out this_path s' (extract_outlvals argvals) outvals s'' ->
      exec_call this_path inst_m s (MkExpression tags (ExpFunctionCall func nil args) typ dir) s' vret

(* Only in/inout arguments in the first list Val and only out/inout arguments in the second list Val. *)

with exec_func : path -> inst_mem -> state -> fundef -> list Val -> state -> list Val -> option Val -> Prop :=
  | exec_func_internal : forall obj_path inst_m s global params init body args s''' args' vret s' s'',
      bind_parameters (map (map_fst (fun param => obj_path ++ [param])) params) args s s' ->
      exec_block obj_path inst_m s' init  s'' SContinue ->
      exec_block obj_path inst_m s'' body s''' (SReturn vret) ->
      extract_parameters (map (map_fst (fun param => obj_path ++ [param])) params) args' s''' ->
      exec_func obj_path inst_m s (FInternal global params init body) args s''' args' vret

  | exec_func_table_match : forall obj_path name inst_m keys actions action_name ctrl_args action default_action const_entries s s',
      exec_table_match obj_path s name const_entries (Some (mk_action_ref action_name ctrl_args)) ->
      add_ctrl_args (get_action actions name) ctrl_args = Some action ->
      exec_call obj_path inst_m s action s' None ->
      exec_func obj_path inst_m s (FTable name keys actions default_action const_entries) nil s' nil None

  | exec_func_table_default : forall obj_path name inst_m keys actions default_action const_entries s s',
      exec_table_match obj_path s name const_entries None ->
      exec_call obj_path inst_m s default_action s' None ->
      exec_func obj_path inst_m s (FTable name keys actions (Some default_action) const_entries) nil s' nil None

  | exec_func_table_noaction : forall obj_path name inst_m keys actions const_entries s,
      exec_table_match obj_path s name const_entries None ->
      exec_func obj_path inst_m s (FTable name keys actions None const_entries) nil s nil None

  | exec_func_external : forall obj_path inst_m class_name name (* params *) m es es' args args' vret,
      exec_extern es class_name name obj_path args es' args' vret ->
      exec_func obj_path inst_m (m, es) (FExternal class_name name (* params *)) args (m, es') args' vret.

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

(* Only allowing instances as constructor parameters is assumed in this implementation.
  To support value expressions, we need a Gallina function to evaluate expressions.
  And we convert the inst_mem into a mem (for efficiency, maybe need lazy evaluation in this conversion). *)

Fixpoint instantiate_expr' (rev_decls : list (@Declaration tags_t)) (e : ienv) (expr : @Expression tags_t) (p : path)
      (m : inst_mem) (s : extern_state) {struct expr} : inst_mem_val * inst_mem * extern_state :=
  let instantiate' := instantiate'' instantiate_expr' in
  match expr with
  | MkExpression _ (ExpName (BareName name) _) _ _ =>
      let inst := force dummy_inst_mem_val (IdentMap.get name e) in
      (inst, PathMap.set p inst m, s)
  | MkExpression _ (ExpNamelessInstantiation typ args) _ _ =>
      instantiate' rev_decls e typ args p m s
  (* TODO evaluate val parameters. *)
  | _ => (dummy_inst_mem_val, m, s)
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

(* TODO we need to evaluate constants in instantiation. *)

Fixpoint instantiate_class_body (rev_decls : list (@Declaration tags_t)) (e : ienv) (class_name : ident) (p : path)
      (m : inst_mem) (s : extern_state) {struct rev_decls} : path * inst_mem * extern_state :=
  match rev_decls with
  | decl :: rev_decls' =>
      let instantiate_decls := instantiate_decls' (instantiate_class_body rev_decls') in
      match decl with
      | DeclParser _ class_name' _ _ _ _ _ =>
          if P4String.equivb class_name class_name' then
            let m := PathMap.set p (IMInst class_name p) m in
            (nil, m, s) (* TODO *)
          else
            instantiate_class_body rev_decls' e class_name p m s
      | DeclControl _ class_name' _ _ _ locals _ =>
          if P4String.equivb class_name class_name' then
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

(* TODO generate other components of ge. *)

Definition BlockNil := BlockEmpty dummy_tags.

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

Fixpoint load_decl (p : path) (ge : genv) (decl : @Declaration tags_t) : genv :=
  match decl with
  (* TODO parser *)
  | DeclControl _ name type_params params constructor_params locals apply =>
      let params := map get_param_name_dir params in
      let constructor_params := map get_param_name constructor_params in
      let ge := fold_left (load_decl (p ++ [name])) locals ge in
      let init := process_locals locals in
      PathMap.set (p ++ [name]) (FInternal false params init apply) ge
  | DeclFunction _ _ name type_params params body =>
      let params := map get_param_name_dir params in
      PathMap.set (p ++ [name]) (FInternal (path_equivb p nil) params BlockNil body) ge
  | DeclAction _ name params ctrl_params body =>
      let params := map get_param_name_dir params in
      let ctrl_params := map (fun name => (name, In)) (map get_param_name ctrl_params) in
      PathMap.set (p ++ [name]) (FInternal (path_equivb p nil) (params ++ ctrl_params) BlockNil body) ge
  | _ => ge
  end.

Definition load_prog (prog : @program tags_t) : genv :=
  match prog with
  | Program decls => fold_left (load_decl nil) decls PathMap.empty
  end.

End Semantics.
