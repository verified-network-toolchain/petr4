Require Import Strings.String.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Program.Program.
Require Import Typed.
Require Import Syntax.
Require Import P4Int.
Require Import Ops.
Import ListNotations.

Module IdentMap.

Section IdentMap.

Context {tags_t: Type}.
Notation ident := (P4String.t tags_t).
Context {A: Type}.

Definition t := ident -> option A.

Definition empty : t := fun _ => None.
Definition get : ident -> t -> option A := fun id idMap => idMap id.
Definition set : ident -> A -> t -> t :=
  fun id value idMap x => if P4String.equivb x id then Some value else idMap x.

Definition sets: list ident -> list A -> t -> t :=
  fun idList valueList idMap =>
    fold_left (fun idM ivPair => set (fst ivPair) (snd ivPair) idM)
              (combine idList valueList) idMap.

Definition gets (kl : list ident) (m : t) : list (option A) :=
  map (fun k => get k m) kl.

End IdentMap.

End IdentMap.

Definition list_eqb {A} (eqb : A -> A -> bool) al bl :=
  Nat.eqb (length al) (length bl) &&
  forallb (uncurry eqb) (combine al bl).

Definition path_equivb {tags_t: Type} :
  (list (P4String.t tags_t)) -> (list (P4String.t tags_t)) -> bool :=
  list_eqb (@P4String.equivb tags_t).

Module PathMap.

Section PathMap.

Context {tags_t: Type}.
Notation ident := (P4String.t tags_t).
Notation path := (list ident).
Context {A: Type}.

Definition t := path -> option A.

Definition empty : t := fun _ => None.
Definition get : path -> t -> option A := fun p pM => pM p.
Definition set : path -> A -> t -> t :=
  fun p v pM x => if path_equivb x p then Some v else pM x.

Definition sets : list path -> list A -> t -> t :=
  fun pList vList pMap =>
    fold_left (fun idM ivPair => set (fst ivPair) (snd ivPair) idM)
              (combine pList vList) pMap.

Definition gets (kl : list path) (m : t) : list (option A) :=
  map (fun k => get k m) kl.

End PathMap.

End PathMap.

Arguments IdentMap.t {_} _.
Arguments PathMap.t {_} _.

Section Semantics.

(* Inductive val :=
  | VInt (v : Z)
  (* TODO *). *)

Context {tags_t: Type}.
Notation Val := (@ValueBase tags_t).

Notation ident := (P4String.t tags_t).
Notation path := (list ident).
Notation P4Int := (P4Int.t tags_t).
Notation P4String := (P4String.t tags_t).

(* We want to share the notation of External between P4light and P4cub, so later we need to
  have a parameter `ActionRef`, while `Match` is just shared. *)
(* Because the entries can refer to constructor parameters, we need to refer the arguments as expressions. *)
(* Maybe we can just use the definition in Syntax.v. *)
Inductive table_entry :=
  Entry (matches : list (@Match tags_t)) (action : ident) (args : list (option (@Expression tags_t))).

Class External := {
  ExternalState : Type;
  GetEntries : ExternalState -> path -> list table_entry;
  GetMatch : list (Val * ident (* match_kind *)) -> list table_entry -> option table_entry (* action *);
  (* Allocation should be a function; calling may be fine as a relation. *)
  AllocExtern : ExternalState -> ident (* class *) -> path -> list Val -> ExternalState;
  CallExtern : ExternalState -> ident (* class *) -> ident (* method *) -> path -> list Val -> ExternalState -> list Val -> option Val -> Prop
}.

Section UseExternal.

Context `{External}.

Inductive memory_val :=
  | MVal (v : Val)
  (* Pointer of program level references those are not available as normal values,
      including pointers to methods and functions,
        and pointers to instances. *)
  | MInstance (p : path)
  | MClass (name : ident).
  (* Should these pointers be paths or locs? *)

Definition mem := @PathMap.t tags_t Val.

Definition state : Type := mem * ExternalState.

Definition set_memory m (s : state) : state :=
  let (_, es) := s in (m, es).

Definition update_memory (f : mem -> mem) (s : state) : state :=
  let (m, es) := s in (f m, es).

Definition get_memory (s : state) : mem :=
  let (m, _) := s in m.

Definition name_cons (p: path) (id: ident) : path :=
  p ++ [id].

(* Inductive env_enty... *)

Inductive env_entry :=
  | Global (p : path)
  | Instance (p : path).

Definition env := @IdentMap.t tags_t env_entry.

(* Axiom env_set : env -> P4String -> path -> env.
Axiom env_get : env -> P4String -> option path. *)

Definition ident_to_path (e : env) (i : ident) (this : path) : option path :=
  match (IdentMap.get i e) with
  | Some (Global p) => Some p
  | Some (Instance p) => Some (this ++ p)
  | None => None
  end.

Inductive fundef :=
  | FInternal
      (* true -> global; false -> instance *)
      (global : bool)
      (decl_path : path)
      (e : env)
      (params : list ident)
      (body : @Block tags_t)
  | FTable
      (name : ident)
      (e : env)
      (keys : list (@TableKey tags_t))
      (actions : list (@Expression tags_t))
      (default_action : option (@Expression tags_t))
      (entries : option (list table_entry))
  | FExternal
      (class : ident)
      (name : ident).

Axiom dummy_fundef : fundef.

(* Definition genv := (@program tags_t) * (path -> option env). *)
(* only give the Statement is not enough; need call convention. *)
Definition genv := path -> option fundef.
(* Definition get_decl (ge : genv) (p : path) : option (env * @Declaration tags_t) :=
  match p with
  | BareName  *)

Variable ge : genv.

Definition name_to_path (e : env) (this_path : path) (name : @Typed.name tags_t) : option path :=
  match name with
  | QualifiedName p n =>
      Some (p ++ [n])
  | BareName id =>
      ident_to_path e id this_path
  end.

Definition eval_p4int (n: P4Int) : Val :=
  match P4Int.width_signed n with
  | None => ValBaseInteger (P4Int.value n)
  | Some (w, true) => ValBaseInt w (P4Int.value n)
  | Some (w, false) => ValBaseBit w (P4Int.value n)
  end.

Definition name_to_val (e: env) (n : @Typed.name tags_t) (this : path) (s : state) : option Val :=
  let p :=
    match n with
    | BareName i => ident_to_path e i this
    | QualifiedName ns i => Some (name_cons ns i)
    end
  in 
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
Inductive exec_expr : env -> path -> (* temp_env -> *) state -> 
                      (@Expression tags_t) -> Val -> 
                      (* trace -> *) (* temp_env -> *) (* state -> *) (* signal -> *) Prop :=
  | exec_expr_bool : forall b e this st tag typ dir,
                     exec_expr e this st
                     (MkExpression tag (ExpBool b) typ dir)
                     (ValBaseBool b)
  | exec_expr_int : forall i iv e this st tag typ dir,
                    iv = eval_p4int i ->
                    exec_expr e this st
                    (MkExpression tag (ExpInt i) typ dir)
                    iv
  | exec_expr_string : forall s e this st tag typ dir,
                       exec_expr e this st
                       (MkExpression tag (ExpString s) typ dir)
                       (ValBaseString s)
  | exec_expr_name: forall name e v this st tag typ dir,
                    name_to_val e name this st = Some v ->
                    exec_expr e this st
                    (MkExpression tag (ExpName name) typ dir)
                    v
  | exec_expr_array_access: forall array headers size next idx idxv idxz idxn header e this st tag typ dir,
                            exec_expr e this st array (ValBaseStack headers size next) ->
                            exec_expr e this st idx idxv ->
                            array_access_idx_to_z idxv = Some idxz ->
                            (0 <= idxz < (Z.of_nat size))%Z ->
                            z_to_nat idxz = Some idxn ->
                            List.nth_error headers idxn = Some header ->
                            exec_expr e this st
                            (MkExpression tag (ExpArrayAccess array idx) typ dir)
                            header
  | exec_expr_array_access_undef: forall array headers size next idx idxv idxz v e this st tag typ dir,
                                  exec_expr e this st array (ValBaseStack headers size next) ->
                                  exec_expr e this st idx idxv ->
                                  array_access_idx_to_z idxv = Some idxz ->
                                  (idxz < 0)%Z \/ (idxz >= (Z.of_nat size))%Z ->
                                  exec_expr e this st
                                  (MkExpression tag (ExpArrayAccess array idx) typ dir)
                                  v
  | exec_expr_bitstring_access : forall bits bitsv bitsz w lo hi e this st tag typ dir,
                                 exec_expr e this st bits bitsv ->
                                 bitstring_slice_bits_to_z bitsv = Some (w, bitsz) ->
                                 (lo <= hi < (N.of_nat w))%N ->
                                 exec_expr e this st
                                 (MkExpression tag (ExpBitStringAccess bits lo hi) typ dir)
                                 (ValBaseBit (N.to_nat (hi - lo + 1)%N) (bitstring_slice bitsz lo hi))
  | exec_expr_list_nil : forall e this st tag typ dir,
                         exec_expr e this st
                         (MkExpression tag (ExpList nil) typ dir)
                         (ValBaseTuple nil)
  | exec_expr_list_cons : forall expr v es vs e this st tag typ dir,
                          exec_expr e this st expr v ->
                          exec_expr e this st (MkExpression tag (ExpList es) typ dir) (ValBaseTuple vs) ->
                          exec_expr e this st
                          (MkExpression tag (ExpList (expr :: es)) typ dir)
                          (ValBaseTuple (v :: vs))
  | exec_expr_record_nil : forall e this st tag typ dir,
                           exec_expr e this st
                           (MkExpression tag (ExpRecord nil) typ dir)
                           (ValBaseRecord nil)
  | exec_expr_record_cons : forall exprk exprv v es kvs e this st tag_expr tag_kv typ dir,
                            exec_expr e this st exprv v ->
                            exec_expr e this st (MkExpression tag_expr (ExpRecord es) typ dir) (ValBaseRecord kvs) ->
                            exec_expr e this st
                            (MkExpression tag_expr (ExpRecord ((MkKeyValue tag_kv exprk exprv) :: es)) typ dir)
                            (ValBaseRecord ((exprk, v) :: kvs))
  | exec_expr_unary_op : forall op arg argv v e this st tag typ dir,
                         exec_expr e this st arg argv ->
                         Ops.eval_unary_op op argv = Some v ->
                         exec_expr e this st
                         (MkExpression tag (ExpUnaryOp op arg) typ dir)
                         v
  | exec_expr_binary_op : forall op larg largv rarg rargv v e this st tag typ dir,
                          exec_expr e this st larg largv ->
                          exec_expr e this st rarg rargv ->
                          Ops.eval_binary_op op largv rargv = Some v ->
                          exec_expr e this st
                          (MkExpression tag (ExpBinaryOp op (larg, rarg)) typ dir)
                          v
  | exec_expr_cast : forall newtyp expr oldv newv e this st tag typ dir,
                     exec_expr e this st expr oldv ->
                     (* eval_cast need env and state of new types *)
                     Ops.eval_cast newtyp oldv = Some newv ->
                     exec_expr e this st
                     (MkExpression tag (ExpCast newtyp expr) typ dir)
                     newv
  (* | exec_expr_type_member omitted for now *)
  | exec_expr_error_member : forall err e this st tag typ dir,
                             exec_expr e this st
                             (MkExpression tag (ExpErrorMember err) typ dir)
                             (ValBaseError err)
  (* | exec_expr_expression_member omitted for now *)
  | exec_expr_ternary_tru : forall cond tru truv fls e this st tag typ dir,
                            exec_expr e this st cond (ValBaseBool true) ->
                            exec_expr e this st tru truv ->
                            exec_expr e this st
                            (MkExpression tag (ExpTernary cond tru fls) typ dir)
                            truv
  | exec_expr_ternary_fls : forall cond tru fls flsv e this st tag typ dir,
                            exec_expr e this st cond (ValBaseBool false) ->
                            exec_expr e this st fls flsv ->
                            exec_expr e this st
                            (MkExpression tag (ExpTernary cond tru fls) typ dir)
                            flsv
  | exec_expr_dont_care : forall e this st tag typ dir,
                          exec_expr e this st
                          (MkExpression tag ExpDontCare typ dir)
                          ValBaseNull
  (* the following two expressions output ValueSet instead of ValueBase *)
  (* | exec_expr_mask : forall expr exprv mask maskv e this st tag typ dir,
                     exec_expr e this st expr exprv ->
                     exec_expr e this st mask maskv ->
                     exec_expr e this st
                     (MkExpression tag (ExpMask expr mask) typ dir)
                     (ValSetMask exprv maskv)
  | exec_expr_range : forall lo lov hi hiv e this st tag typ dir,
                      exec_expr e this st lo lov ->
                      exec_expr e this st hi hiv ->
                      exec_expr e this st
                      (MkExpression tag (ExpRange lo hi) typ dir)
                      (ValSetRange lov hiv) *)
  .

Inductive exec_exprs : env -> path -> state -> list (@Expression tags_t) -> list Val -> Prop :=
  | exec_exprs_nil : forall e this st,
                     exec_exprs e this st nil nil
  | exec_exprs_cons : forall e this st expr es v vs,
                      exec_expr e this st expr v ->
                      exec_exprs e this st es vs ->
                      exec_exprs e this st (expr :: es) (v :: vs).


Axiom param_to_name : (@P4Parameter tags_t) -> ident.

Definition copy_in_copy_out (params : list path)
                            (args : list Val) (args' : list Val)
                            (s s' s'' : state) :=
  s' = update_memory (PathMap.sets params args) s /\
  map Some args' = PathMap.gets params (get_memory s).

Inductive signal : Type :=
   | SContinue : signal
   | SReturn : option Val -> signal
   | SExit
   (* parser's states include accept and reject *)
   | SReject : string -> signal. 

Definition get_external_state (s : state) :=
  let (_, es) := s in es.

Axiom get_action : forall (actions : list (@Expression tags_t)) (name : ident), (@Expression tags_t).
Axiom add_ctrl_args : forall (action : @Expression tags_t) (ctrl_args : list (option (@Expression tags_t))), (@Expression tags_t).

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
  | None => GetEntries (get_external_state s) table
  end.

Inductive exec_table_match : env -> path -> state -> ident -> option (list table_entry) -> option table_entry -> Prop :=
  | exec_table_match_intro : forall this_path name e keys keyvals const_entries s matched_entry,
      let entries := getEntries s (this_path ++ [name]) const_entries in
      let match_kinds := map TableKeyMatchKind keys in
      exec_exprs e this_path s (map TableKeyKey keys) keyvals ->
      GetMatch (combine keyvals match_kinds) entries = matched_entry ->
      exec_table_match e this_path s name const_entries matched_entry.

Inductive Lval : Type.

Definition argument : Type := (option Val) * (option Lval).
(* Inductive argument :=
  | MkArgument (ov : option Val) (olv : option Lval). *)

Definition get_arg_directions (func : @Expression tags_t) : list direction.
Admitted.

Inductive exec_args : env -> path -> state -> list (option (@Expression tags_t)) -> list direction -> list argument -> Prop :=.

Inductive exec_copy_out : env -> path -> state -> list argument -> list Val -> state -> Prop :=.

(* We split the memory into constant and non-constant parts. *)
Definition inst_mem := @PathMap.t tags_t memory_val.

Axiom dummy_tag : tags_t.
Definition apply_string : ident := {| P4String.tags := dummy_tag; P4String.str := "apply" |}.

Definition lookup_func (this_path : path) (e : env) (inst_m : inst_mem) (func : @Expression tags_t) : option (path * fundef) :=
  (* We should think about using option monad in this function. *)
  match func with
  (* function/action *)
  | MkExpression _ (ExpName name) _ _ =>
      match name with
      | BareName id =>
          match IdentMap.get id e with
          | Some (Global p) => option_map (fun fd => (nil, fd)) (PathMap.get p ge)
          | Some (Instance p) =>
              match PathMap.get this_path inst_m with
              | Some (MClass class_name) =>
                  option_map (fun fd => (this_path, fd)) (PathMap.get ([class_name] ++ p) ge)
              | _ => None
              end
          | None => None
          end
      | QualifiedName p n => option_map (fun fd => (nil, fd)) (PathMap.get (p ++ [n]) ge)
      end
  (* apply and builtin, but builtin unsupported yet. *)
  | MkExpression _ (ExpExpressionMember expr name) _ _ =>
      if P4String.equivb name apply_string then
        match expr with
        (* Instances should only be referred with bare names. *)
        | MkExpression _ (ExpName (BareName name)) _ _ =>
            let oinst_path :=
              match PathMap.get (this_path ++ [name]) inst_m with
              | Some (MInstance inst) =>
                  Some inst
              | Some (MClass _) =>
                  Some (this_path ++ [name])
              | _ => None
              end
            in
            match oinst_path with
            | Some inst_path =>
                match PathMap.get inst_path inst_m with
                | Some (MClass class_name) =>
                    option_map (fun fd => (inst_path, fd)) (PathMap.get [class_name] ge)
                | _ => None
                end
            | None => None
            end
        | _ => None
        end
      (* If the method name does not match any of the keywords, it is an external method. *)
      else
        match expr with
        (* Instances should only be referred with bare names. *)
        | MkExpression _ (ExpName (BareName name)) _ _ =>
            let oinst_path :=
              match PathMap.get (this_path ++ [name]) inst_m with
              | Some (MInstance inst) =>
                  Some inst
              | Some (MClass _) =>
                  Some (this_path ++ [name])
              | _ => None
              end
            in
            match oinst_path with
            | Some inst_path =>
                match PathMap.get inst_path inst_m with
                | Some (MClass class_name) =>
                    Some (inst_path, FExternal class_name name)
                | _ => None
                end
            | None => None
            end
        | _ => None
        end
  | _ => None
  end.

Definition extract_argvals : list argument -> list Val.
Admitted.

Inductive exec_lvalue_expr : env -> path -> state -> (@Expression tags_t) -> (@ValueLvalue tags_t) -> Prop :=
  | exec_lvalue_expr_name : forall name e this st tag typ dir,
                            exec_lvalue_expr e this st 
                            (MkExpression tag (ExpName name) typ dir)
                            (MkValueLvalue (ValLeftName name) typ)
  | exec_lvalue_expr_member : forall expr lv name e this st tag typ dir,
                              exec_lvalue_expr e this st expr lv ->
                              exec_lvalue_expr e this st 
                              (MkExpression tag (ExpExpressionMember expr name) typ dir)
                              (MkValueLvalue (ValLeftMember lv name) typ)
  (* ATTN: lo and hi interchanged here *)
  | exec_lvalue_bitstring_access : forall bits lv lo hi e this st tag typ dir,
                                   exec_lvalue_expr e this st bits lv ->
                                   exec_lvalue_expr e this st 
                                   (MkExpression tag (ExpBitStringAccess bits lo hi) typ dir)
                                   (MkValueLvalue (ValLeftBitAccess lv (N.to_nat hi) (N.to_nat lo)) typ)
  (* Since array size is unknown here, only the lower-bound undefined behavior is defined.
     The upper bound should be handled after getting the value from lvalue. *)
  | exec_lvalue_array_access : forall array lv idx idxv idxz idxn e this st tag typ dir,
                               exec_lvalue_expr e this st array lv ->
                               exec_expr e this st idx idxv ->
                               array_access_idx_to_z idxv = Some idxz ->
                               z_to_nat idxz = Some idxn ->
                               exec_lvalue_expr e this st 
                               (MkExpression tag (ExpArrayAccess array idx) typ dir)
                               (MkValueLvalue (ValLeftArrayAccess lv idxn) typ)
  | exec_lvalue_array_access_undef_lo : forall array alv idx idxv idxz lv e this st tag typ dir,
                                        exec_lvalue_expr e this st array alv ->
                                        exec_expr e this st idx idxv ->
                                        array_access_idx_to_z idxv = Some idxz ->
                                        (idxz < 0)%Z ->
                                        exec_lvalue_expr e this st 
                                        (MkExpression tag (ExpArrayAccess array idx) typ dir)
                                        lv.

Definition update_val_by_name (e: env) (this : path) (s : state) (n : @Typed.name tags_t) (v : Val): option state :=
  let p :=
    match n with
    | BareName i => ident_to_path e i this
    | QualifiedName ns i => Some (name_cons ns i)
    end
  in 
    match p with
    | Some p' => Some (update_memory (PathMap.set p' v) s)
    | _ => None
    end.

Definition assign_lvalue (e : env) (this : path) (st : state) (lhs : @ValueLvalue tags_t) (rhs : Val) : option (state * signal) :=
  match lhs with
  | MkValueLvalue (ValLeftName name) _ =>
    let opt_st := update_val_by_name e this st name rhs in
      match opt_st with 
      | Some st' => Some (st', SContinue)
      | _ => None
      end
  | _ => None (* omitted for now *)
  end.

(*this_path -> decl_path*)
Inductive exec_stmt : path -> path -> env -> inst_mem -> state -> (@Statement tags_t) -> state -> signal -> Prop :=
  | eval_stmt_assignment : forall lhs lv rhs v this_path decl_path e inst_m st tag typ st' sig,
                           exec_lvalue_expr e this_path st lhs lv ->
                           exec_expr e this_path st rhs v ->
                           assign_lvalue e this_path st lv v = Some (st', SContinue) ->
                           exec_stmt this_path decl_path e inst_m st
                           (MkStatement tag (StatAssignment lhs rhs) typ) st' sig
  
with exec_block : path -> path -> env -> inst_mem -> state -> (@Block tags_t) -> state -> signal -> Prop :=
with exec_func_caller : path -> env-> inst_mem -> state -> (@Expression tags_t) -> state -> option Val -> Prop :=
  (* eval the call expression:
       1. lookup the function to call;
       2. eval arguments;
       3. call the function by exec_funcall;
       4. write back out parameters.
  *)
  | exec_func_function : forall this_path e inst_m s tag func args typ dir argvals obj_path fd outvals s' s'' vret,
      let dirs := get_arg_directions func in
      exec_args e this_path s args dirs argvals ->
      lookup_func this_path e inst_m func = Some (obj_path, fd) ->
      exec_func_callee obj_path inst_m s fd (extract_argvals argvals) s' outvals vret ->
      exec_copy_out e this_path s' argvals outvals s'' ->
      exec_func_caller this_path e inst_m s (MkExpression tag (ExpFunctionCall func nil args) typ dir) s' vret

with exec_func_callee : path -> inst_mem -> state -> fundef -> list Val -> state -> list Val -> option Val -> Prop :=
  | exec_func_internal : forall obj_path global decl_path e inst_m params body s args args' s' s'' vret,
      copy_in_copy_out (map (fun param => obj_path ++ decl_path ++ [param]) params) args args' s s' s'' ->
      exec_block obj_path decl_path e inst_m s' body s'' (SReturn vret) ->
      exec_func_callee obj_path inst_m s (FInternal global decl_path e params body) args s'' args' vret

  | exec_func_table_match : forall obj_path name e inst_m keys actions matches action_name ctrl_args default_action const_entries s s',
      exec_table_match e obj_path s name const_entries (Some (Entry matches action_name ctrl_args)) ->
      exec_func_caller obj_path e inst_m s (add_ctrl_args (get_action actions name) ctrl_args) s' None ->
      exec_func_callee obj_path inst_m s (FTable name e keys actions default_action const_entries) nil s' nil None

  | exec_func_table_default : forall obj_path name e inst_m keys actions default_action const_entries s s',
      exec_table_match e obj_path s name const_entries None ->
      exec_func_caller obj_path e inst_m s default_action s' None ->
      exec_func_callee obj_path inst_m s (FTable name e keys actions (Some default_action) const_entries) nil s' nil None

  | exec_func_table_noaction : forall obj_path name e inst_m keys actions const_entries s,
      exec_table_match e obj_path s name const_entries None ->
      exec_func_callee obj_path inst_m s (FTable name e keys actions None const_entries) nil s nil None

  | exec_func_external : forall obj_path inst_m class_name name m es es' args args' vret (*   e inst_m keys actions const_entries s *),
      CallExtern es class_name name obj_path args es' args' vret ->
      exec_func_callee obj_path inst_m (m, es) (FExternal class_name name) args (m, es') args' vret.

(* Return the declaration whose name is [name]. *)
Fixpoint get_decl (rev_decls : list (@Declaration tags_t)) (name : ident) : (@Declaration tags_t) :=
  match rev_decls with
  | decl :: rev_decls' =>
      match decl with
      | DeclParser _ name' _ _ _ _ _
      | DeclControl _ name' _ _ _ _ _
      | DeclPackageType _ name' _ _ =>
          if P4String.equivb name name' then
            decl
          else
            get_decl rev_decls' name
      | _ => get_decl rev_decls' name
      end
  | [] => DeclError dummy_tag nil (* Abuse DeclError to report not found. *)
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

Definition get_type_name (typ : @P4Type tags_t) : ident :=
  match typ with
  | TypSpecializedType (TypTypeName (BareName type_name)) _ => type_name
  | TypTypeName (BareName type_name) => type_name
  | _ => dummy_ident
  end.

Definition ienv := @IdentMap.t tags_t path.

Definition force {A} (default : A) (x : option A) : A :=
  match x with
  | Some x => x
  | None => default
  end.

(* A trick to define mutually recursive functions. *)
Section instantiate_class_body.

Variable instantiate_class_body_rev_decls : forall (e : ienv) (class_name : ident) (p : path) (m : inst_mem), path * inst_mem.

Section instantiate_expr'.

Variable instantiate_expr' : forall (rev_decls : list (@Declaration tags_t)) (e : ienv) (expr : @Expression tags_t) (p : path) (m : inst_mem), path * inst_mem.

Definition instantiate'' (rev_decls : list (@Declaration tags_t)) (e : ienv) (typ : @P4Type tags_t) (args : list (@Expression tags_t)) (p : path) (m : inst_mem) : path * inst_mem :=
  let class_name := get_type_name typ in
  let decl := get_decl rev_decls class_name in
  let params := get_constructor_param_names decl in
  let instantiate_arg (acc : list path * inst_mem * list ident) arg :=
    let (acc', params) := acc in
    let (args, m) := acc' in
    let (arg, m) := instantiate_expr' rev_decls e arg (p ++ [hd dummy_ident params]) m in
    (* O(n^2) time complexity here. *)
    (args ++ [arg], m, tl params) in
  let (args, m) := fst (fold_left instantiate_arg args (nil, m, params)) in
  let e := IdentMap.sets params args e in
  let (_, m) := instantiate_class_body_rev_decls e class_name p m in
  (p, m).

End instantiate_expr'.

(* Only allowing instances as constructor parameters is assumed in this implementation.
  To support value expressions, we need a Gallina function to evaluate expressions.
  And we convert the inst_mem into a mem (for efficiency, maybe need lazy evaluation in this conversion). *)

Fixpoint instantiate_expr' (rev_decls : list (@Declaration tags_t)) (e : ienv) (expr : @Expression tags_t) (p : path) (m : inst_mem) {struct expr} : path * inst_mem :=
  let instantiate' := instantiate'' instantiate_expr' in
  match expr with
  | MkExpression _ (ExpName (BareName name)) _ _ =>
      let inst := force nil (IdentMap.get name e) in
      (inst, PathMap.set p (MInstance inst) m)
  | MkExpression _ (ExpNamelessInstantiation typ args) _ _ =>
      instantiate' rev_decls e typ args p m
  | _ => (nil, m)
  end.

Definition instantiate' :=
  instantiate'' instantiate_expr'.

Definition instantiate_decl' (rev_decls : list (@Declaration tags_t)) (e : ienv) (decl : @Declaration tags_t) (p : path) (m : inst_mem) : ienv * inst_mem :=
  match decl with
  | DeclInstantiation _ typ args name _ =>
      let class_name := get_type_name typ in
      let decl := get_decl rev_decls class_name in
      let (_, m) := instantiate' rev_decls e typ args (p ++ [name]) m in
      (IdentMap.set name (p ++ [name]) e, m)
  | _ => (e, m)
  end.

Definition instantiate_decls' (rev_decls : list (@Declaration tags_t)) (e : ienv) (decls : list (@Declaration tags_t)) (p : path) (m : inst_mem) : inst_mem :=
  let instantiate_decl'' (em : ienv * inst_mem) (decl : @Declaration tags_t) : ienv * inst_mem :=
    let (e, m) := em in instantiate_decl' rev_decls e decl p m in
  snd (fold_left instantiate_decl'' decls (e, m)).

End instantiate_class_body.

(* Definition get_instantce_path (p : path) (m : inst_mem) : path :=
  match PathMap.get p m with
  | Some (MClass _) => p
  | Some (MInstance p') => p'
  | _ => nil (* dummy *)
  end. *)

Fixpoint instantiate_class_body (rev_decls : list (@Declaration tags_t)) (e : ienv) (class_name : ident) (p : path) (m : inst_mem) {struct rev_decls} : path * inst_mem :=
  match rev_decls with
  | decl :: rev_decls' =>
      let instantiate_decls := instantiate_decls' (instantiate_class_body rev_decls') in
      match decl with
      | DeclParser _ class_name' _ _ _ _ _ =>
          if P4String.equivb class_name class_name' then
            let m := PathMap.set p (MClass class_name) m in
            (nil, m) (* TODO *)
          else
            instantiate_class_body rev_decls' e class_name p m
      | DeclControl _ class_name' _ _ _ locals _ =>
          if P4String.equivb class_name class_name' then
            let m := instantiate_decls rev_decls' e locals p m in
            let m := PathMap.set p (MClass class_name) m in
            (p, m)
          else
            instantiate_class_body rev_decls' e class_name p m
      | _ => instantiate_class_body rev_decls' e class_name p m
      end
  | nil => (nil, m)
  end.

Definition instantiate_expr (rev_decls : list (@Declaration tags_t)) :=
  instantiate_expr' (instantiate_class_body rev_decls) rev_decls.

Definition instantiate (rev_decls : list (@Declaration tags_t)) :=
  instantiate' (instantiate_class_body rev_decls) rev_decls.

Definition instantiate_decl (rev_decls : list (@Declaration tags_t)) :=
  instantiate_decl' (instantiate_class_body rev_decls) rev_decls.

Definition instantiate_decls (rev_decls : list (@Declaration tags_t)) :=
  instantiate_decls' (instantiate_class_body rev_decls) rev_decls.


Fixpoint instantiate_global_decls' (decls : list (@Declaration tags_t)) (rev_decls : list (@Declaration tags_t)) (e : ienv) (m : inst_mem) : inst_mem :=
  match decls with
  | [] => m
  | decl :: decls' =>
      let (e, m) := instantiate_decl rev_decls e decl nil m in
      instantiate_global_decls' decls' (decl :: rev_decls) e m
  end.

Definition instantiate_global_decls (decls : list (@Declaration tags_t)) : forall (m : inst_mem), inst_mem :=
  instantiate_global_decls' decls nil IdentMap.empty.

Definition instantiate_prog (prog : @program tags_t) : inst_mem :=
  match prog with
  | Program decls =>
      instantiate_global_decls decls PathMap.empty
  end.


Definition add_name (p : path) (name : ident) (e : env) : env :=
  if path_equivb p nil then
    IdentMap.set name (Global [name]) e
  else
    IdentMap.set name (Instance (tl p ++ [name])) e.

Definition add_name' (p : path) (e : env) (name : ident) : env :=
  add_name p name e.

Definition add_names (p : path) (names : list ident) (e : env) : env :=
  fold_left (add_name' p) names e.

Fixpoint load_decl (p : path) (ege : env * genv) (decl : @Declaration tags_t) : env * genv :=
  let (e, ge) := ege in
  match decl with
  | DeclConstant _ _ name _ =>
      (add_name p name e, ge)
  (* TODO parser *)
  | DeclControl _ name type_params params constructor_params locals apply =>
      let params := map param_to_name params in
      let constructor_params := map param_to_name constructor_params in
      let e' := add_names (p ++ [name]) (params ++ constructor_params) e in
      let (e', ge) := fold_left (load_decl (p ++ [name])) locals (e', ge) in
      (add_name p name e,
        PathMap.set (p ++ [name]) (FInternal false [name] e' params apply) ge)
  | DeclFunction _ _ name type_params params body =>
      let params := map param_to_name params in
      (add_name p name e,
        PathMap.set (p ++ [name]) (FInternal (path_equivb p nil) [name] (add_names (p ++ [name]) params e) params body) ge)
  | DeclVariable _ _ name _ =>
      (add_name p name e, ge)
  | DeclAction _ name params ctrl_params body =>
      let params := map param_to_name params in
      let ctrl_params := map param_to_name ctrl_params in
      (add_name p name e,
        (* Maybe we need to replace directionless with in in ctrl_params. *)
        PathMap.set (p ++ [name]) (FInternal (path_equivb p nil) [name] (add_names (p ++ [name]) (params ++ ctrl_params) e) (params ++ ctrl_params) body) ge)
  | _ => (e, ge)
  end.

Definition load_prog (prog : @program tags_t) : genv :=
  match prog with
  | Program decls => snd (fold_left (load_decl nil) decls (IdentMap.empty, PathMap.empty))
  end.

End UseExternal.

Class Architecture := {
  ExternalSem : External;
  Evoker : (path -> list Val -> list Val -> Prop) -> Prop
}.

End Semantics.





