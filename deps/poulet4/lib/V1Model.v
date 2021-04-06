Require Import Strings.String.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Program.Program.
Require Import Typed.
Require Import Syntax.
Require Import P4Int.
Require Import Target.
Require Import Maps.
Import ListNotations.
Open Scope Z_scope.

Section V1Model.

Context {tags_t: Type}.
Context {Expression: Type}.
Notation ident := (P4String.t tags_t).
Notation path := (list ident).
Notation Val := (@ValueBase tags_t).
Notation table_entry := (@table_entry tags_t Expression).
Notation action_ref := (@action_ref tags_t Expression).

Inductive register := mk_register {
  reg_width : nat;
  reg_size : Z;
  reg_content : list Z
}.

Definition new_register (size : Z) (w : nat) :=
  mk_register w size (repeat 0 (Z.to_nat size)).

Definition extern_state := @PathMap.t tags_t register.

Definition extern_empty : extern_state := PathMap.empty.

Axiom dummy_tag : tags_t.
Definition register_string : ident := {| P4String.tags := dummy_tag; P4String.str := "register" |}.

Definition alloc_extern (s : extern_state) (class : ident) (params : list (@P4Type tags_t)) (p : path) (args : list Val) :=
  if P4String.equivb class register_string then
    match args with
    (* | [ValBaseInteger size] *)
    | [ValBaseBit _ size]
    (* | [ValBaseInt _ size] *) =>
        match params with
        | [TypBit w] =>
            PathMap.set p (new_register size w) s
        | _ => s (* fail *)
        end
    | _ => s (* fail *)
    end
  else
    s.

Definition extern_func_sem := extern_state -> path -> list Val -> extern_state -> list Val -> option Val -> Prop.

Inductive extern_func := mk_extern_func_sem {
  ef_class : ident;
  ef_func : ident;
  ef_sem : extern_func_sem
}.

Definition apply_extern_func_sem (func : extern_func) : extern_state -> ident -> ident -> path -> list Val -> extern_state -> list Val -> option Val -> Prop :=
  match func with
  | mk_extern_func_sem class_name func_name sem =>
      fun s class_name' func_name' =>
          if P4String.equivb class_name class_name' && P4String.equivb func_name func_name' then
            sem s
          else
            fun _ _ _ _ _ => False
  end.

Definition read_string : ident := {| P4String.tags := dummy_tag; P4String.str := "read" |}.

Definition Znth {A} : Z -> list A -> A.
Admitted.

Definition REG_INDEX_WIDTH := 32%nat.

Inductive register_read_sem : extern_func_sem :=
  | exec_register_read : forall s p reg w index result,
      PathMap.get p s = Some reg ->
      reg_width reg = w ->
      0 <= index < reg_size reg ->
      Znth index (reg_content reg) = result ->
      register_read_sem s p [ValBaseBit REG_INDEX_WIDTH index] s [ValBaseBit w result] None.

Definition register_read : extern_func := {|
  ef_class := register_string;
  ef_func := read_string;
  ef_sem := register_read_sem
|}.

Definition write_string : ident := {| P4String.tags := dummy_tag; P4String.str := "write" |}.

Definition upd_Znth {A} : Z -> A -> list A -> list A.
Admitted.

Inductive register_write_sem : extern_func_sem :=
  | exec_register_write : forall s p reg w content' index value,
      PathMap.get p s = Some reg ->
      reg_width reg = w ->
      0 <= index < reg_size reg ->
      upd_Znth index value (reg_content reg) = content' ->
      register_write_sem s p [ValBaseBit REG_INDEX_WIDTH index]
            (PathMap.set p (mk_register w (reg_size reg) content') s)
          [] None.

Definition register_write : extern_func := {|
  ef_class := register_string;
  ef_func := write_string;
  ef_sem := register_write_sem
|}.

Inductive exec_extern : extern_state -> ident (* class *) -> ident (* method *) -> path -> list Val -> extern_state -> list Val -> option Val -> Prop :=
  | exec_extern_register_read : forall s class method p args s' args' vret,
      apply_extern_func_sem register_read s class method p args s' args' vret ->
      exec_extern s class method p args s' args' vret
  | exec_extern_register_write : forall s class method p args s' args' vret,
      apply_extern_func_sem register_write s class method p args s' args' vret ->
      exec_extern s class method p args s' args' vret.

Axiom extern_get_entries : extern_state -> path -> list table_entry.

Axiom extern_match : list (Val * ident) -> list table_entry -> option action_ref.

Instance V1ModelExternSem : ExternSem := Build_ExternSem
  extern_state
  extern_empty
  alloc_extern
  exec_extern
  extern_get_entries
  extern_match.

Axiom exec_prog : (path -> extern_state -> list Val -> extern_state -> list Val -> Prop) -> Prop.

Instance V1Model : Target := Build_Target _ exec_prog.

End V1Model.
