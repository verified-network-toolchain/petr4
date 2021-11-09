Require Import Coq.Lists.List.
Require Import Coq.Program.Program.
Require Import Coq.Strings.String.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.NArith.BinNatDef.

Require Import Poulet4.Typed.
Require Import Poulet4.Syntax.
Require Import Poulet4.Value.
Require Export Poulet4.Maps.
Require Export Poulet4.Sublist.
Require Import Poulet4.P4Notations.
Require Import String.
Import ListNotations.

Section SyntaxUtil.

Context {tags_t: Type} {inhabitant_tags_t : Inhabitant tags_t}.
Variable default_tag: tags_t.
Notation Val := (@ValueBase tags_t bool).

Notation ident := (P4String.t tags_t).
Notation path := (list ident).
Notation P4Int := (P4Int.t tags_t).
Notation P4String := (P4String.t tags_t).
Check !"next".
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

Definition get_param_dir_typ (param : @P4Parameter tags_t) : direction * P4Type :=
  match param with
  | MkParameter _ dir typ _ _ => (dir, typ)
  end.

Definition get_param_typ (param : @P4Parameter tags_t) : P4Type :=
  match param with
  | MkParameter _ _ typ _ _ => typ
  end.

Definition get_param_name_typ (param : @P4Parameter tags_t) : ident * P4Type :=
  match param with
  | MkParameter _ _ typ _ name => (name, typ)
  end.

Definition get_param_name_dir (param : @P4Parameter tags_t) : ident * direction :=
  match param with
  | MkParameter _ dir _ _ name => (name, dir)
  end.

Definition get_parser_state_statements (parser_state : @ParserState tags_t) : list (@Statement tags_t) :=
  match parser_state with
  | MkParserState _ _ statements _ => statements
  end.

Definition get_decl_class_name (decl : @Declaration tags_t) : option P4String :=
  match decl with
  | DeclParser _ name _ _ _ _ _
  | DeclControl _ name _ _ _ _ _
  | DeclPackageType _ name _ _ =>
      Some name
  | _ =>
      None
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
 | SReject : P4String -> signal.

Definition SReturnNull := SReturn ValBaseNull.

(* Errors *)
Definition NoError := !"NoError".
Definition PacketTooShort := !"PacketTooShort".
Definition NoMatch := !"NoMatch".
Definition StackOutOfBounds := !"StackOutOfBounds".
Definition HeaderTooShort := !"HeaderTooShort".
Definition ParserTimeout := !"ParserTimeout".
Definition ParserInvalidArgument := !"ParserInvalidArgument".

(* Conversion *)
Definition pos_of_N (n : N) : positive :=
  match n with
  | N0 => 1
  | Npos p => p
  end.

Definition lift_option {A} (l : list (option A)) : option (list A) :=
  let lift_one_option (x : option A) (acc : option (list A)) :=
    match x, acc with
    | Some x', Some acc' => Some (x' :: acc')
    | _, _ => None
    end
  in List.fold_right lift_one_option (Some []) l.

Definition lift_option_kv {A B} (l : list (A * option B)) : option (list (A * B)) :=
  let lift_one_option (kv : A * option B) (acc : option (list (A * B))) :=
    match kv, acc with
    | (k, Some v), Some acc' => Some ((k, v) :: acc')
    | _, _ => None
    end
  in List.fold_right lift_one_option (Some []) l.

End SyntaxUtil.
