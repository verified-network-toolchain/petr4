Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.
Require Import Coq.Program.Program.
Require Import Petr4.Typed.
Require Import Petr4.Syntax.
Require Import Petr4.P4Int.
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

End PathMap.

End PathMap.



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

Class External := {
  ExternalState : Type;
  GetControlParam : ExternalState -> ident -> option Val
}.

Context `{External}.

Inductive memory_val :=
  | MVal (v : Val)
  (* Pointer of program level references those are not available as normal values,
      including pointers to methods and functions,
        and pointers to instances. *)
  | MInstance (p : path)
  | MClass (name : ident).
  (* Should these pointers be paths or locs? *)

Definition mem := @PathMap.t tags_t memory_val.

(* Definition set : mem -> path -> memory_val -> mem :=
  (fun m p v => fun p' => if path_equivb p p' then Some v else m p'). *)
Definition set_args : list path -> list memory_val -> mem -> mem := PathMap.sets.
(* Definition get : mem -> path -> option memory_val := id. *)

Definition get_args : mem -> list path -> list (option memory_val) := (fun m => (map (fun p => PathMap.get p m))).

(* Definition set' p v (m : mem) :=
  PathMap.set m p v. *)

(* Definition set_args' p v m :=
  set_args m p v. *)

Definition state : Type := mem * ExternalState.

Definition set_memory m (s : state) : state :=
  let (_, es) := s in (m, es).

Definition update_memory (f : mem -> mem) (s : state) : state :=
  let (m, es) := s in (f m, es).

Definition get_memory (s : state) : mem :=
  let (m, _) := s in m.

Definition name_cons : path -> ident -> path :=
  fix name_cons (p: path) (id: ident): path :=
    match p with
    | nil => cons id nil
    | cons id' restIds => cons id' (name_cons restIds id)
    end.

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
  (* this_path = nil: global; this_path <> nil: instance *)
  | FInternal
      (this_path : path)
      (decl_path : path)
      (e : env)
      (params : list ident)
      (ctrl_params : list ident)
      (body : @Block tags_t)
  | FExternal.

Axiom dummy_fundef : fundef.

(* Definition genv := (@program tags_t) * (path -> option env). *)
(* only give the Statement is not enough; need call convention. *)
Definition genv := path -> option fundef.
(* Definition get_decl (ge : genv) (p : path) : option (env * @Declaration tags_t) :=
  match p with
  | BareName  *)

Variable ge : genv.

(* Inductive deref_loc (* (ty: type) *) (m : mem) (this : path) (name : ident) : (* trace *) memory_val -> Prop :=
  | deref_loc_value: forall v,
      m (name_cons this name) = Some v ->
      deref_loc m this name v. *)



(* Axiom temp_env : Type. *)

(* Definition name_to_path (e : env) (this_path : path) (name : ident) :=
  match  *)

Definition eval_p4int (n: P4Int) : Val :=
  match P4Int.width_signed n with
    | None => ValBaseInteger (value n)
    | Some (w, true) => ValBaseBit w (value n)
    | Some (w, false) => ValBaseInt w (value n)
  end.

Definition name_only (n: @Typed.name tags_t) : P4String :=
  match n with
    | BareName s
    | QualifiedName _ s => s
  end.

Definition ident_to_val (e: env) (i : ident) (this : path) (s : state) : Val :=
  match (IdentMap.get i e) with
  | Some (Global p) => 
    match PathMap.get p (get_memory s) with
      | Some (MVal v) => v
      | _ => ValBaseNull
    end
  | Some (Instance p) => 
    match PathMap.get (this ++ p) (get_memory s) with
      | Some (MVal v) => v
      | _ => ValBaseNull
    end
  | None => ValBaseNull
  end.

(* Note that expressions don't need decl_path. *)
Inductive exec_expr : env -> path -> (* temp_env -> *) state -> 
                      (@Expression tags_t) -> Val -> 
                      (* trace -> *) (* temp_env -> *) (* state -> *) (* outcome -> *) Prop :=
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
  | exec_expr_name: forall n e this st tag typ dir,
                    exec_expr e this st
                    (MkExpression tag (ExpName n) typ dir)
                    (ident_to_val e (name_only n) this st)
  (* | exec_expr_arrayaccess: forall a i e this st tag typ dir,
                           exec_expr e this st
                           (MkExpression tag (ExpArrayAccess a i) typ dir)
                           
  ExpArrayAccess  *)
  .




Axiom param_to_name : (@P4Parameter tags_t) -> ident.

Definition copy_in_copy_out (params : list path)
                            (args : list Val) (args' : list Val)
                            (s s' s'' : state) :=
  s' = update_memory (set_args params (map MVal args)) s /\
  map Some (map MVal args') = get_args (get_memory s) params.

(* Variable (this : path). (* So this pointer only matters for declarations, not for using the variables. *) *)

Inductive outcome : Type :=
   | Out_normal : outcome
   | Out_return : option Val -> outcome.

Definition get_external_state (s : state) :=
  let (_, es) := s in es.

Definition get_ctrl_params (s : state) : list ident -> list (option Val) :=
  map (GetControlParam (get_external_state s)).

Inductive exec_stmt : path -> path -> env -> state -> (@Statement tags_t) -> state -> outcome -> Prop :=
with exec_block : path -> path -> env -> state -> (@Block tags_t) -> state -> outcome -> Prop :=
with exec_funcall : state -> fundef -> list Val -> state -> list Val -> option Val -> Prop :=
  | exec_funcall_internal : forall this_path decl_path e params ctrl_params body s args control_args args' s' s'' vret,
      get_ctrl_params s ctrl_params = map Some control_args ->
      copy_in_copy_out (map (fun param => this_path ++ decl_path ++ [param]) (params ++ ctrl_params)) (args ++ control_args) args' s s' s'' ->
      exec_block this_path decl_path e s' body s'' (Out_return vret) ->
      exec_funcall s (FInternal this_path decl_path e params ctrl_params body) args s'' args' vret.
(* with eval_funcall: mem -> fundef -> list Val -> trace -> mem -> Val -> Prop :=
  | eval_funcall_internal: forall le m f vargs t e m1 m2 m3 out vres m4,
      alloc_variables ge empty_env m (f.(fn_params) ++ f.(fn_vars)) e m1 ->
      list_norepet (var_names f.(fn_params) ++ var_names f.(fn_vars)) ->
      bind_parameters ge e m1 f.(fn_params) vargs m2 ->
      exec_stmt e (create_undef_temps f.(fn_temps)) m2 f.(fn_body) t le m3 out ->
      outcome_result_value out f.(fn_return) vres m3 ->
      Mem.free_list m3 (blocks_of_env ge e) = Some m4 ->
      eval_funcall m (Internal f) vargs t m4 vres
  | eval_funcall_external: forall m ef targs tres cconv vargs t vres m',
      external_call ef ge vargs m t vres m' ->
      eval_funcall m (External ef targs tres cconv) vargs t m' vres. *)

(* Inductive exec_instantiation : path -> ident -> state -> list memory_val -> state -> Prop :=
  | exec_instantiation_control : forall p module s (constructor_params : list (@P4Parameter tags_t)) args s',
      match get_decl ge module with
      | Some (DeclControl _ _ _ _ constructor_params _ _) =>
          s' = update_memory (compose (PathMap.set p (MClass module))
                    (set_args (map (name_cons p) (map param_to_name constructor_params)) args))
                    s
      | _ => False
      end ->
      exec_instantiation p module s args s'
  (* which one is better? *)
  | exec_instantiation_control' : forall p module s (constructor_params : list (@P4Parameter tags_t)) args s',
      match get_decl ge module with
      | Some (DeclControl _ _ _ _ constructor_params' _ _) =>
          constructor_params' = constructor_params
      | _ => False
      end ->
      s' = update_memory
             (compose (PathMap.set p (MClass module))
                 (set_args (map (name_cons p) (map param_to_name constructor_params)) args))
             s ->
      exec_instantiation p module s args s'. *)

Axiom dummy_tag : tags_t.

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
  | [] => DeclError dummy_tag nil
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

Section instantiate_class_body.

Variable instantiate_class_body_rev_decls : forall (e : ienv) (class_name : ident) (p : path) (m : mem), path * mem.

Section instantiate_expr'.

Variable instantiate_expr' : forall (rev_decls : list (@Declaration tags_t)) (e : ienv) (expr : @Expression tags_t) (p : path) (m : mem), path * mem.

Definition instantiate'' (rev_decls : list (@Declaration tags_t)) (e : ienv) (typ : @P4Type tags_t) (args : list (@Expression tags_t)) (p : path) (m : mem) : path * mem :=
  let class_name := get_type_name typ in
  let decl := get_decl rev_decls class_name in
  let params := get_constructor_param_names decl in
  let instantiate_arg (acc : list path * mem * list ident) arg :=
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

Fixpoint instantiate_expr' (rev_decls : list (@Declaration tags_t)) (e : ienv) (expr : @Expression tags_t) (p : path) (m : mem) {struct expr} : path * mem :=
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

Definition instantiate_decl' (rev_decls : list (@Declaration tags_t)) (e : ienv) (decl : @Declaration tags_t) (p : path) (m : mem) : ienv * mem :=
  match decl with
  | DeclInstantiation _ typ args name _ =>
      let class_name := get_type_name typ in
      let decl := get_decl rev_decls class_name in
      let (_, m) := instantiate' rev_decls e typ args (p ++ [name]) m in
      (IdentMap.set name (p ++ [name]) e, m)
  | _ => (e, m)
  end.

Definition instantiate_decls' (rev_decls : list (@Declaration tags_t)) (e : ienv) (decls : list (@Declaration tags_t)) (p : path) (m : mem) : mem :=
  let instantiate_decl'' (em : ienv * mem) (decl : @Declaration tags_t) : ienv * mem :=
    let (e, m) := em in instantiate_decl' rev_decls e decl p m in
  snd (fold_left instantiate_decl'' decls (e, m)).

End instantiate_class_body.

(* Definition get_instantce_path (p : path) (m : mem) : path :=
  match PathMap.get p m with
  | Some (MClass _) => p
  | Some (MInstance p') => p'
  | _ => nil (* dummy *)
  end. *)

Fixpoint instantiate_class_body (rev_decls : list (@Declaration tags_t)) (e : ienv) (class_name : ident) (p : path) (m : mem) {struct rev_decls} : path * mem :=
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


Fixpoint instantiate_global_decls' (decls : list (@Declaration tags_t)) (rev_decls : list (@Declaration tags_t)) (e : ienv) (m : mem) : mem :=
  match decls with
  | [] => m
  | decl :: decls' =>
      let (e, m) := instantiate_decl rev_decls e decl nil m in
      instantiate_global_decls' decls' (decl :: rev_decls) e m
  end.

Definition instantiate_global_decls (decls : list (@Declaration tags_t)) : forall (m : mem), mem :=
  instantiate_global_decls' decls nil IdentMap.empty.

Definition instantiate_prog (prog : @program tags_t) : mem :=
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
        PathMap.set (p ++ [name]) (FInternal p [name] e' params nil apply) ge)
  | DeclFunction _ _ name type_params params body =>
      let params := map param_to_name params in
      (add_name p name e,
        PathMap.set (p ++ [name]) (FInternal p [name] (add_names (p ++ [name]) params e) params nil body) ge)
  | DeclVariable _ _ name _ =>
      (add_name p name e, ge)
  | DeclAction _ name params ctrl_params body =>
      let params := map param_to_name params in
      let ctrl_params := map param_to_name ctrl_params in
      (add_name p name e,
        PathMap.set (p ++ [name]) (FInternal p [name] (add_names (p ++ [name]) (params ++ ctrl_params) e) params ctrl_params body) ge)
  | _ => (e, ge)
  end.

Definition load_prog (prog : @program tags_t) : genv :=
  match prog with
  | Program decls => snd (fold_left (load_decl nil) decls (IdentMap.empty, PathMap.empty))
  end.

End Semantics.
