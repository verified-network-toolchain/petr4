Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.
Require Import Coq.Program.Program.
Require Import Petr4.Typed.
Require Import Petr4.Syntax.

Class External {
  ExternalState : Type
}.

Section Semantics.

Inductive val :=
  | VInt (v : Z)
  (* TODO *).


Context {tags_t: Type}.
Notation path := (@Typed.name tags_t).
Notation P4String := (P4String.t tags_t).
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

Definition mem := path -> option memory_val.

Definition set : mem -> path -> memory_val -> mem :=
  (fun m p v => fun p' => if path_equivb p p' then Some v else m p').
Axiom set_args : mem -> list path -> list memory_val -> mem.
Definition get : mem -> path -> option memory_val := id.

Definition get_args : mem -> list path -> list (option memory_val) := (fun m => (map m)).

Definition set' p v m :=
  set m p v.

Definition set_args' p v m :=
  set_args m p v.

Definition state : Type := mem * ExternalState.

Definition set_memory m (s : state) : state :=
  let (_, es) := s in (m, es).

Definition update_memory (f : mem -> mem) (s : state) : state :=
  let (m, es) := s in (f m, es).

Definition get_memory (s : state) : mem :=
  let (m, _) := s in m.

Axiom name_cons : path-> P4String -> path.

Axiom genv : Type.
Axiom get_decl : genv -> P4String -> option (@Declaration tags_t).
Variable ge : genv.

Inductive deref_loc (* (ty: type) *) (m : mem) (this : path) (name : P4String) : (* trace *) memory_val -> Prop :=
  | deref_loc_value: forall v,
      m (name_cons this name) = Some v ->
      deref_loc m this name v.

Axiom env : Type.
Axiom temp_env : Type.

Inductive fundef :=
  | FInternal (p : path)
  | FExternal.

Axiom param_to_name : (@P4Parameter tags_t) -> P4String.

Definition copy_in_copy_out (params : list path)
                            (args : list val) (args' : list val)
                            (s s' s'' : state) :=
  s' = update_memory (set_args' params (map MVal args)) s /\
  map Some (map MVal args') = get_args (get_memory s) params.

Variable (this : path).

Inductive exec_expr : env -> (* temp_env -> *) state -> (@Statement tags_t) -> (* trace -> *) (* temp_env -> *) state -> (* outcome -> *) Prop :=
with exec_stmt : env -> (* temp_env -> *) state -> (@Statement tags_t) -> (* trace -> *) (* temp_env -> *) state -> (* outcome -> *) Prop :=
with exec_block : env -> (* temp_env -> *) state -> (@Block tags_t) -> (* trace -> *) (* temp_env -> *) state -> (* outcome -> *) Prop :=
with exec_funcall : state -> fundef -> list val -> (* trace -> *) state -> list val -> option val -> Prop :=
  | exec_funcall_control : forall envx p module s apply args args' s' s'' ret,
      get (get_memory s) p = Some (MPointer (BareName module)) ->
      exec_block envx s' apply s'' -> (* return ? *)
      match get_decl ge module with
      | Some (DeclControl _ _ _ params _ _ apply') =>
          copy_in_copy_out (map (name_cons p) (map param_to_name params)) args args' s s' s'' /\
          apply = apply'
      | _ => False
      end ->
      exec_funcall s (FInternal p) args s'' args' ret.
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

Inductive exec_instantiation : path -> P4String -> state -> list memory_val -> state -> Prop :=
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

