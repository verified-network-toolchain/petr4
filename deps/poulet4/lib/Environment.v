Require Import Coq.Lists.List.
Require Import Coq.FSets.FMapList.
Require Import Coq.Structures.OrderedTypeEx.

Require Import Monads.Monad.
Require Import Monads.Option.
Require Import Monads.State.

Require String.
Require Import Syntax.

Open Scope monad.

Module Import MStr := FMapList.Make(String.StringOT).

Inductive exception :=
| PacketTooShort
| Reject
| Exit
| Internal
| AssertError (error_msg: String.t).

Section Environment.

  Context (tags_t: Type).
  Context (tags_dummy: tags_t).

  Definition scope := MStr.t (Value tags_t).
  Definition environment := list scope.

  Definition env_monad := @state_monad environment exception.

  Definition map_env (f : environment -> environment) : env_monad unit :=
    fun env => mret tt (f env).

  Definition lift_env_fn (f : environment -> option environment) : env_monad unit :=
    fun env =>
      match f env with
      | Some env' => mret tt env'
      | None => state_fail Internal env
      end.

  Definition lift_env_lookup_fn (f: environment -> option (Value tags_t)) : env_monad (Value tags_t) :=
    fun env =>
      match f env with
      | Some res => mret res env
      | None => state_fail Internal env
      end.

  Definition lift_option {A : Type} (x: option A) : env_monad A := fun env => 
                                                                     match x with
                                                                     | Some it => mret it env
                                                                     | None => (inr Internal, env)
                                                                     end.

  Definition update_scope (key: String.t) (val: (Value tags_t)) (bindings: scope) : option scope :=
    MStr.find key bindings;;
    mret (MStr.add key val (MStr.remove key bindings)).

  Definition insert_scope (key: String.t) (val: (Value tags_t)) (bindings: scope) : option scope :=
    MStr.find key bindings;;
    mret (MStr.add key val bindings).

  Definition extend_scope (key: String.t) (val: (Value tags_t)) (bindings: scope) : scope :=
      MStr.add key val bindings.

  Definition find_scope (key: String.t) (bindings: scope) : option (Value tags_t) :=
    MStr.find key bindings.

  Definition push_scope (env: environment) :=
    MStr.empty _ :: env.

  Definition pop_scope (env: environment) : option environment :=
    match env with
    | _ :: rest => Some rest
    | nil => None
    end.

  Fixpoint update_environment' (key: String.t) (val: (Value tags_t)) (env: environment) : option environment :=
    match env with
    | inner :: rest =>
      if MStr.find key inner
      (* TODO: insert vs update makes proofs slightly easier but is less efficient.
          we could alleviate the burden with a lemma for environments.
      *)
      (* then let* inner' := update_scope key val inner in *)
      then let* inner' := insert_scope key val inner in
           mret (inner' :: rest)
      else let* rest' := update_environment' key val rest in
           mret (inner :: rest')
    | nil => None
    end.

  Definition update_environment (key: String.t) (val: (Value tags_t)) : env_monad unit :=
    lift_env_fn (update_environment' key val).

  Definition insert_environment' (key: String.t) (val: (Value tags_t)) (env: environment) : option environment :=
    match env with
    | inner :: rest =>
      let* inner' := insert_scope key val inner in
      mret (inner' :: rest)
    | nil => None
    end.

  Definition insert_environment (key: String.t) (val: (Value tags_t)) : env_monad unit :=
    lift_env_fn (insert_environment' key val).

  Fixpoint find_environment' (key: String.t) (env: environment) : option (Value tags_t) :=
    match env with
    | inner :: rest =>
      match MStr.find key inner with
      | Some v => Some v
      | None => find_environment' key rest
      end
    | nil => None
    end.

  Definition find_environment (key: String.t) : env_monad (Value tags_t) :=
    lift_env_lookup_fn (find_environment' key).

  (* TODO handle name resolution properly *)
  Definition str_of_name_warning_not_safe (t: Typed.name) : String.t :=
    match t with 
    | Typed.BareName s => s
    | Typed.QualifiedName _ s => s
    end.

  Fixpoint find_lvalue' (lval: ValueLvalue) (env: environment) : option (Value tags_t) :=
    let '(MkValueLvalue pre_lval _) := lval in
    match pre_lval with
    | ValLeftName var =>
      let s := str_of_name_warning_not_safe var in
      find_environment' s env
    | ValLeftMember lval' member =>
      let* val := find_lvalue' lval' env in
      match val with
      | ValBase _ (ValBaseRecord _ map) =>
        match (Raw.find member map) with
        | Some v => Some (ValBase _ v)
        | None => None
        end
      | _ => None
      end
    | _ => None (* TODO *)
    end.

  Definition find_lvalue (lval: ValueLvalue) : env_monad (Value tags_t) :=
    lift_env_lookup_fn (find_lvalue' lval).

  Definition update_member (obj: (Value tags_t)) (member: String.t) (val: (Value tags_t)) : option (Value tags_t).
  Admitted.

  Fixpoint update_lvalue' (lval: ValueLvalue) (val: (Value tags_t)) (env: environment) : option environment :=
    let '(MkValueLvalue pre_lval _) := lval in
    match pre_lval with
    | ValLeftName var =>
      let s := str_of_name_warning_not_safe var in
      update_environment' s val env
    | ValLeftMember lval' member =>
      let* obj := find_lvalue' lval' env in
      let* obj' := update_member obj member val in
      update_lvalue' lval' obj' env
    | _ => None (* TODO *)
    end.

  Definition update_lvalue (lval: ValueLvalue) (val: (Value tags_t)) : env_monad unit :=
    lift_env_fn (update_lvalue' lval val).

  Definition toss_value (original: env_monad (Value tags_t)) : env_monad unit :=
    fun env =>
      match original env with
      | (inl result, env') => mret tt env'
      | (inr exc, env') => state_fail exc env'
      end.

  Definition dummy_value (original: env_monad unit) : env_monad (Value tags_t) :=
    fun env =>
      match original env with
      | (inl tt, env') => mret (ValBase _ (ValBaseNull _)) env'
      | (inr exc, env') => state_fail exc env'
      end.

  (* Predicates for relating strings to values in a scope (MapsToS) and an Environment (MapsToE). *)
  Inductive MapsToS : String.string -> Value tags_t -> scope -> Prop :=
    (* a pair s,v is in an env if env is extended with s,v *)
    | MapsToSE : forall s v env, MapsToS s v (extend_scope s v env)
    (* if s1,v1 is already in an env, then extending the env with a distinct key does not forget the existing pair *)
    | MapsToSI : forall s1 s2 v1 v2 env, s1 <> s2 -> MapsToS s1 v1 env -> MapsToS s1 v1 (extend_scope s2 v2 env)
    .
  Inductive MapsToE : String.string -> Value tags_t -> environment -> Prop :=
    (* if a pair s,v is in a scope, then for any environment env, s,v is also in scope :: env*)
    | MapsToES : forall s v env scope, MapsToS s v scope -> MapsToE s v (scope :: env).
    (* TODO: a constructor for when a pair is in a nested scope. To properly do this, we need something like:
      forall environments env, env_pre, 
      a pair s,v is in env_pre ++ env iff s,v is in env and also s is not in the domain of env_pre
    *)


  
  Lemma option_ineq : forall A, forall x: A, None <> Some x.
  Proof.
  Admitted.
  
  Lemma find_scope_corr : 
    forall s v scope, MapsToS s v scope <-> find_scope s scope = Some v.
  Proof using tags_t.
  intros. split.
    - 
      intros.
      unfold find_scope.
      induction H.
      -- 
        unfold extend_scope.
        eapply MStr.find_1.
        eapply MStr.add_1.
        auto.
      --
        eapply MStr.find_1.
        unfold extend_scope.
        eapply MStr.add_2. 
          --- auto. 
          ---
            apply MStr.find_2.
            assumption.
    -
      intros. unfold find_scope.
      unfold find_scope in H.
      destruct scope0.
      induction this0.
        --
          unfold find in H.
          unfold Raw.find in H.
          simpl in H.
          assert (HNeq := option_ineq).
          specialize (HNeq (Value tags_t) v).
          contradiction.
        --
          
    


  Admitted.

  (* TODO: we replaced the iff version of the env_corr correctness because it made erewrites hard.
      logically the iff version is stronger (and maybe preferable?) 
    *)
  (* Lemma find_env_corr : 
    forall s v env scope, MapsToS s v scope <-> exists env_pre env_post env',
      env = env_pre ++ scope :: env_post /\
      (* ~ MapsToS s v env_pre /\  *)
      MapsToS s v scope /\
      find_environment s env = (inl v, env').
  Proof.
  Admitted. *)

  Lemma find_env_corr : 
    forall s v (env : Environment.environment) (scope : Environment.scope) env_pre env_post, 
    Environment.MapsToS s v scope ->
      env = env_pre ++ (scope :: env_post) ->
      Environment.find_environment s env = (inl v, env).
  Proof using tags_t.
  Admitted.

  Lemma lift_env_lookup_corr : 
    forall s v env env',
    Environment.find_environment s env = (inl v, env') -> Environment.find_environment' s env = Some v.
  Proof using tags_t.
  Admitted.



End Environment.


