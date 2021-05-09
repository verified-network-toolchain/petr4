Require Import Coq.Lists.List.
Require Import Typed.
Require Import Syntax.
Require Export Maps.
Require Import String.
Import ListNotations.

Section SyntaxUtil.

Context {tags_t: Type}.
Variable default_tag: tags_t.
Notation Val := (@ValueBase tags_t).

Notation ident := (P4String.t tags_t).
Notation path := (list ident).
Notation P4Int := (P4Int.t tags_t).
Notation P4String := (P4String.t tags_t).

Axiom dummy_ident : unit -> ident. (* make it lazy for extracted OCaml. *)
Axiom dummy_val : Val.

Definition get_type_name (typ : @P4Type tags_t) : ident :=
  match typ with
  | TypSpecializedType (TypTypeName (BareName type_name)) _ => type_name
  | TypTypeName (BareName type_name) => type_name
  | _ => dummy_ident tt
  end.

Definition get_param_name (param : @P4Parameter tags_t) : ident :=
  match param with
  | MkParameter _ _ _ _ name => name
  end.

Definition get_param_dir (param : @P4Parameter tags_t) : direction :=
  match param with
  | MkParameter _ dir _ _ _ => dir
  end.

Definition get_param_name_dir (param : @P4Parameter tags_t) : ident * direction :=
  match param with
  | MkParameter _ dir _ _ name => (name, dir)
  end.

Definition get_parser_state_statements (parser_state : @ParserState tags_t) : list (@Statement tags_t) :=
  match parser_state with
  | MkParserState _ _ statements _ => statements
  end.

Fixpoint list_statement_to_block (stmts : list (@Statement tags_t)) : @Block tags_t :=
  match stmts with
  | nil => BlockEmpty default_tag
  | stmt :: stmts' => BlockCons stmt (list_statement_to_block stmts')
  end.

Fixpoint block_to_list_statement (blk : @Block tags_t) : list (@Statement tags_t) :=
  match blk with
  | BlockEmpty _ => nil
  | BlockCons stmt blk' => stmt :: block_to_list_statement blk'
  end.

Fixpoint block_app (block1 block2 : @Block tags_t) :=
  match block1 with
  | BlockEmpty _ => block2
  | BlockCons stmt block =>
      BlockCons stmt (block_app block block2)
  end.

Definition force {A} (default : A) (x : option A) : A :=
  match x with
  | Some x => x
  | None => default
  end.

Definition map_fst {A B C} (f : A -> B) (p : A * C) : B * C :=
  let (a, c) := p in (f a, c).

Definition map_snd {A B C} (f : A -> B) (p : C * A) : C * B :=
  let (c, a) := p in (c, f a).

(* ************ Semantics common definitions ************************)
Inductive signal : Type :=
 | SContinue : signal
 | SReturn : Val -> signal
 | SExit
 (* parser's states include accept and reject *)
 | SReject : string -> signal.

Definition SReturnNull := SReturn ValBaseNull.

(* Errors *)
Open Scope string_scope.
Definition NoError_str := "NoError".
Definition PacketTooShort_str:= "PacketTooShort".
Definition NoMatch_str := "NoMatch".
Definition StackOutOfBounds_str := "StackOutOfBounds".
Definition HeaderTooShort_str := "HeaderTooShort".
Definition ParserTimeout_str := "ParserTimeout".
Definition ParserInvalidArgument_str := "ParserInvalidArgument".

End SyntaxUtil.
