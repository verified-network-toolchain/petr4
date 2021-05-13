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
Require Import Poulet4.SyntaxUtil.
Require Import Maps.
Import ListNotations.
Open Scope Z_scope.

Section V1Model.

Context {tags_t: Type}.
Context {Expression: Type}.
Notation ident := (P4String.t tags_t).
Notation path := (list ident).
Notation P4Type := (@P4Type tags_t).
Notation Val := (@ValueBase tags_t).
Notation signal := (@signal tags_t).
Notation table_entry := (@table_entry tags_t Expression).
Notation action_ref := (@action_ref tags_t Expression).

Inductive register := mk_register {
  reg_width : nat;
  reg_size : Z;
  reg_content : list Z
}.

Definition new_register (size : Z) (w : nat) :=
  mk_register w size (repeat 0 (Z.to_nat size)).

Definition packet_in := list bool.

Definition packet_out := list bool.

Inductive object :=
  | ObjTable (entries : list table_entry)
  | ObjRegister (reg : register)
  | ObjPin (pin : packet_in)
  | ObjPout (pout : packet_out).

Definition extern_state := @PathMap.t tags_t object.

Definition extern_empty : extern_state := PathMap.empty.

Axiom dummy_tags : tags_t.
Definition register_string : ident := {| P4String.tags := dummy_tags; P4String.str := "register" |}.

Definition alloc_extern (s : extern_state) (class : ident) (targs : list P4Type) (p : path) (args : list Val) :=
  if P4String.equivb class register_string then
    match args with
    (* | [ValBaseInteger size] *)
    | [ValBaseBit _ size]
    (* | [ValBaseInt _ size] *) =>
        match targs with
        | [TypBit w] =>
            PathMap.set p (ObjRegister (new_register size w)) s
        | _ => s (* fail *)
        end
    | _ => s (* fail *)
    end
  else
    s.

Definition extern_func_sem := extern_state -> path -> list P4Type -> list Val -> extern_state -> list Val -> signal -> Prop.

Inductive extern_func := mk_extern_func_sem {
  ef_class : ident;
  ef_func : ident;
  ef_sem : extern_func_sem
}.

Definition apply_extern_func_sem (func : extern_func) : extern_state -> ident -> ident -> path -> list P4Type -> list Val -> extern_state -> list Val -> signal -> Prop :=
  match func with
  | mk_extern_func_sem class_name func_name sem =>
      fun s class_name' func_name' =>
          if P4String.equivb class_name class_name' && P4String.equivb func_name func_name' then
            sem s
          else
            fun _ _ _ _ _ _ => False
  end.

Definition read_string : ident := {| P4String.tags := dummy_tags; P4String.str := "read" |}.

Definition Znth {A} : Z -> list A -> A.
Admitted.

Definition REG_INDEX_WIDTH := 32%nat.

Inductive register_read_sem : extern_func_sem :=
  | exec_register_read : forall s p reg w index result,
      PathMap.get p s = Some (ObjRegister reg) ->
      reg_width reg = w ->
      0 <= index < reg_size reg ->
      Znth index (reg_content reg) = result ->
      register_read_sem s p nil [ValBaseBit REG_INDEX_WIDTH index] s [ValBaseBit w result] SReturnNull.

Definition register_read : extern_func := {|
  ef_class := register_string;
  ef_func := read_string;
  ef_sem := register_read_sem
|}.

Definition write_string : ident := {| P4String.tags := dummy_tags; P4String.str := "write" |}.

Definition upd_Znth {A} : Z -> A -> list A -> list A.
Admitted.

Inductive register_write_sem : extern_func_sem :=
  | exec_register_write : forall s p reg w content' index value,
      PathMap.get p s = Some (ObjRegister reg) ->
      reg_width reg = w ->
      0 <= index < reg_size reg ->
      upd_Znth index value (reg_content reg) = content' ->
      register_write_sem s p nil [ValBaseBit REG_INDEX_WIDTH index]
            (PathMap.set p (ObjRegister (mk_register w (reg_size reg) content')) s)
          [] SReturnNull.

Definition register_write : extern_func := {|
  ef_class := register_string;
  ef_func := write_string;
  ef_sem := register_write_sem
|}.

Definition packet_in_string : ident := {| P4String.tags := dummy_tags; P4String.str := "packet_in" |}.
Definition extract_string : ident := {| P4String.tags := dummy_tags; P4String.str := "extract" |}.

Axiom extract : forall (pin : list bool) (typ : P4Type), Val * list bool.
Axiom extract2 : forall (pin : list bool) (typ : P4Type) (len : Z), Val * list bool.

Inductive packet_in_extract_sem : extern_func_sem :=
  | exec_packet_in_extract : forall s p pin typ v pin',
      PathMap.get p s = Some (ObjPin pin) ->
      extract pin typ = (v, pin') ->
      packet_in_extract_sem s p [typ] []
            (PathMap.set p (ObjPin pin') s)
          [v] SReturnNull
  | exec_packet_in_extract2 : forall s p pin typ len v pin',
      PathMap.get p s = Some (ObjPin pin) ->
      extract2 pin typ len = (v, pin') ->
      packet_in_extract_sem s p [typ] [ValBaseBit 32%nat len]
            (PathMap.set p (ObjPin pin') s)
          [v] SReturnNull.

Definition packet_in_extract : extern_func := {|
  ef_class := packet_in_string;
  ef_func := extract_string;
  ef_sem := packet_in_extract_sem
|}.

Definition packet_out_string : ident := {| P4String.tags := dummy_tags; P4String.str := "packet_out" |}.
Definition emit_string : ident := {| P4String.tags := dummy_tags; P4String.str := "emit" |}.

Axiom emit : forall (pout : list bool) (v : Val), list bool.

Inductive packet_out_emit_sem : extern_func_sem :=
  | exec_packet_out_emit : forall s p pout typ v pout',
      PathMap.get p s = Some (ObjPout pout) ->
      emit pout v = pout' ->
      packet_out_emit_sem s p [typ] [v]
            (PathMap.set p (ObjPout pout') s)
          [] SReturnNull.

Definition packet_out_emit : extern_func := {|
  ef_class := packet_out_string;
  ef_func := emit_string;
  ef_sem := packet_out_emit_sem
|}.

Inductive exec_extern : extern_state -> ident (* class *) -> ident (* method *) -> path -> list P4Type -> list Val -> extern_state -> list Val -> signal -> Prop :=
  | exec_extern_register_read : forall s class method p targs args s' args' vret,
      apply_extern_func_sem register_read s class method p targs args s' args' vret ->
      exec_extern s class method p targs args s' args' vret
  | exec_extern_register_write : forall s class method p targs args s' args' vret,
      apply_extern_func_sem register_write s class method p targs args s' args' vret ->
      exec_extern s class method p targs args s' args' vret
  | exec_extern_packet_in_extract : forall s class method p targs args s' args' vret,
      apply_extern_func_sem packet_in_extract s class method p targs args s' args' vret ->
      exec_extern s class method p targs args s' args' vret
  | exec_extern_packet_out_emit : forall s class method p targs args s' args' vret,
      apply_extern_func_sem packet_out_emit s class method p targs args s' args' vret ->
      exec_extern s class method p targs args s' args' vret.

Definition extern_get_entries (es : extern_state) (p : path) : list table_entry :=
  match PathMap.get p es with
  | Some (ObjTable entries) => entries
  | _ => nil
  end.

Axiom extern_match : list (Val * ident) -> list table_entry -> option action_ref.

Instance V1ModelExternSem : ExternSem := Build_ExternSem
  extern_state
  extern_empty
  alloc_extern
  exec_extern
  extern_get_entries
  extern_match.

Definition main_string : ident := {| P4String.tags := dummy_tags; P4String.str := "main" |}.
Definition p_string : ident := {| P4String.tags := dummy_tags; P4String.str := "p" |}.
Definition vr_string : ident := {| P4String.tags := dummy_tags; P4String.str := "vr" |}.
Definition ig_string : ident := {| P4String.tags := dummy_tags; P4String.str := "ig" |}.
Definition eg_string : ident := {| P4String.tags := dummy_tags; P4String.str := "eg" |}.
Definition ck_string : ident := {| P4String.tags := dummy_tags; P4String.str := "ck" |}.
Definition dep_string : ident := {| P4String.tags := dummy_tags; P4String.str := "dep" |}.

Inductive exec_prog : (path -> extern_state -> list Val -> extern_state -> list Val -> signal -> Prop) ->
    extern_state -> list bool -> extern_state -> list bool -> Prop :=
  | exec_prog_intro : forall (module_sem : _ -> _ -> _ -> _ -> _ -> _ -> Prop) s0 pin s7 pout s1 s2 s3 s4 s5 s6
      meta1 standard_metadata1 hdr2 meta2 standard_metadata2 hdr3 meta3 hdr4 meta4 standard_metadata4 hdr5 meta5 standard_metadata5 hdr6 meta6,
      PathMap.set [packet_in_string] (ObjPin pin) s0 = s1 ->
      module_sem [main_string; p_string] s1 [meta1; standard_metadata1] s2 [hdr2; meta2; standard_metadata2] SReturnNull ->
      module_sem [main_string; vr_string] s2 [hdr2; meta2] s3 [hdr3; meta3] SReturnNull ->
      module_sem [main_string; ig_string] s3 [hdr3; meta3; standard_metadata2] s4 [hdr4; meta4; standard_metadata4] SReturnNull ->
      module_sem [main_string; eg_string] s4 [hdr4; meta4; standard_metadata4] s5 [hdr5; meta5; standard_metadata5] SReturnNull ->
      module_sem [main_string; ck_string] s5 [hdr5; meta5] s6 [hdr6; meta6] SReturnNull ->
      module_sem [main_string; dep_string] s6 [hdr6] s7 nil SReturnNull ->
      PathMap.get [packet_out_string] s7 = Some (ObjPout pout) ->
      exec_prog module_sem s0 pin s7 pout.

Instance V1Model : Target := Build_Target _ exec_prog.

End V1Model.
