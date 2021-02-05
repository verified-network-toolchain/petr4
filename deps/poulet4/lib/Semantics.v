Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.
Require Import Coq.Program.Program.
Require Import Petr4.Typed.
Require Import Petr4.Syntax.

Module IdentMap.

Section IdentMap.

Context {tags_t: Type}.
Notation ident := (P4String.t tags_t).
Context {A: Type}.

Definition t := ident -> option A.

Axiom empty : t.
Axiom get : t -> ident -> option A.
Axiom set : t -> ident -> A -> t.

End IdentMap.

End IdentMap.

Module PathMap.

Section PathMap.

Context {tags_t: Type}.
Notation path := (@Typed.name tags_t).
Context {A: Type}.

Definition t := path -> option A.

Axiom empty : t.
Axiom get : t -> path -> option A.
Axiom set : t -> path -> A -> t.

End PathMap.

End PathMap.

Class External := {
  ExternalState : Type(* ;
  ExternalDummy : Type *)
}.

Section Semantics.

Inductive val :=
  | VInt (v : Z)
  (* TODO *).

Context {tags_t: Type}.
Notation ident := (P4String.t tags_t).
Notation path := (@Typed.name tags_t).
Notation P4Int := (P4Int.t tags_t).

Context `{External}.

Inductive memory_val :=
  | MVal (v : val)
  (* Pointer of program level references those are not available as normal values,
      including pointers to methods and functions,
        and pointers to instances. *)
  | MPointer (p : path).
  (* Should these pointers be paths or locs? *)

Definition list_eqb {A} (eqb : A -> A -> bool) al bl :=
  Nat.eqb (length al) (length bl) &&
    forallb (uncurry eqb) (combine al bl).

Definition path_equivb (p p' : path) :=
  match (p, p') with
  | (BareName n, BareName n') => P4String.equivb n n'
  | (QualifiedName ns n, QualifiedName ns' n') =>
      list_eqb (@P4String.equivb tags_t) ns ns' && P4String.equivb n n'
  | _ => false
  end.

Definition mem := @PathMap.t tags_t memory_val.

(* Definition set : mem -> path -> memory_val -> mem :=
  (fun m p v => fun p' => if path_equivb p p' then Some v else m p'). *)
Axiom set_args : mem -> list path -> list memory_val -> mem.
(* Definition get : mem -> path -> option memory_val := id. *)

Definition get_args : mem -> list path -> list (option memory_val) := (fun m => (map (PathMap.get m))).

Definition set' p v (m : mem) :=
  PathMap.set m p v.

Definition set_args' p v m :=
  set_args m p v.

Definition state : Type := mem * ExternalState.

Definition set_memory m (s : state) : state :=
  let (_, es) := s in (m, es).

Definition update_memory (f : mem -> mem) (s : state) : state :=
  let (m, es) := s in (f m, es).

Definition get_memory (s : state) : mem :=
  let (m, _) := s in m.

Axiom name_cons : path-> ident -> path.

(* Inductive env_enty... *)

Inductive env_entry :=
  | Global (p : path)
  | Instance (p : path).

Definition env := @IdentMap.t tags_t env_entry.

(* Axiom env_set : env -> P4String -> path -> env.
Axiom env_get : env -> P4String -> option path. *)

Axiom ident_to_path : forall (e : env) (i : ident) (this : path), path.

(* Definition genv := (@program tags_t) * (path -> option env). *)
(* only give the Statement is not enough; need call convention. *)
Definition genv := path -> option (@Statement tags_t * env).
(* Definition get_decl (ge : genv) (p : path) : option (env * @Declaration tags_t) :=
  match p with
  | BareName  *)

Axiom get_decl : genv -> ident -> option (@Declaration tags_t).
Variable ge : genv.

(* Inductive deref_loc (* (ty: type) *) (m : mem) (this : path) (name : ident) : (* trace *) memory_val -> Prop :=
  | deref_loc_value: forall v,
      m (name_cons this name) = Some v ->
      deref_loc m this name v. *)

(* Axiom temp_env : Type. *)

Inductive fundef :=
  | FInternal (p : path)
  | FExternal.

(* Note that expressions don't use this pointer. *)
Inductive exec_expr : env -> path -> (* temp_env -> *) state -> (@Expression tags_t) -> (* trace -> *) (* temp_env -> *) (* state -> *) (* outcome -> *) Prop :=
  .

Axiom param_to_name : (@P4Parameter tags_t) -> ident.

Definition copy_in_copy_out (params : list path)
                            (args : list val) (args' : list val)
                            (s s' s'' : state) :=
  s' = update_memory (set_args' params (map MVal args)) s /\
  map Some (map MVal args') = get_args (get_memory s) params.

(* Variable (this : path). (* So this pointer only matters for declarations, not for using the variables. *) *)

Inductive outcome : Type :=
   | Out_normal : outcome
   | Out_return : option val -> outcome.

Inductive exec_stmt : path -> path -> env -> state -> (@Statement tags_t) -> state -> outcome -> Prop :=
with exec_block : path -> path -> env -> state -> (@Block tags_t) -> state -> outcome -> Prop :=
with exec_funcall : state -> fundef -> list val -> state -> list val -> option val -> Prop :=
  | exec_funcall_control : forall p1 p2 envx p module s apply args args' s' s'' vret,
      PathMap.get (get_memory s) p = Some (MPointer (BareName module)) ->
      exec_block p1 p2 envx s' apply s'' (Out_return vret) ->
      match get_decl ge module with
      | Some (DeclControl _ _ _ params _ _ apply') =>
          copy_in_copy_out (map (name_cons p) (map param_to_name params)) args args' s s' s'' /\
          apply = apply'
      | _ => False
      end ->
      exec_funcall s (FInternal p) args s'' args' vret.
(* with eval_funcall: mem -> fundef -> list val -> trace -> mem -> val -> Prop :=
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



Inductive exec_instantiation : path -> ident -> state -> list memory_val -> state -> Prop :=
  | exec_instantiation_control : forall p module s (constructor_params : list (@P4Parameter tags_t)) args s',
      match get_decl ge module with
      | Some (DeclControl _ _ _ _ constructor_params _ _) =>
          s' = update_memory (compose (set' p (MPointer (BareName module)))
                    (set_args' (map (name_cons p) (map param_to_name constructor_params)) args))
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
             (compose (set' p (MPointer (BareName module)))
                 (set_args' (map (name_cons p) (map param_to_name constructor_params)) args))
             s ->
      exec_instantiation p module s args s'.

End Semantics.
