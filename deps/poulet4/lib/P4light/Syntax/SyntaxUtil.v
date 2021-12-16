Require Import Coq.Lists.List.
Require Import Coq.Program.Program.
Require Import Coq.Strings.String.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.NArith.BinNatDef.
Require Import Poulet4.P4light.Syntax.Typed.
Require Import Poulet4.P4light.Syntax.Syntax.
Require Export Poulet4.Utils.Maps VST.zlist.Zlist.
Require Import Poulet4.P4light.Syntax.P4Notations.
Require Import String.
Import ListNotations.

Section SyntaxUtil.

Context {tags_t: Type} {inhabitant_tags_t : Inhabitant tags_t}.
Variable default_tag: tags_t.

Notation ident := (P4String.t tags_t).
Notation path := (list ident).
Notation P4Int := (P4Int.t tags_t).
Notation P4String := (P4String.t tags_t).

Axiom dummy_ident : unit -> ident. (* make it lazy for extracted OCaml. *)

Definition get_type_name (typ : @P4Type tags_t) : ident :=
  match typ with
  | TypSpecializedType (TypTypeName type_name) _ => type_name
  | TypTypeName type_name => type_name
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
  | DeclExternObject _ name _ _
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

(* Conversion *)
Definition pos_of_N (n : N) : positive :=
  match n with
  | N0 => 1
  | Npos p => p
  end.

Definition lift_option_kv {A B} (l : list (A * option B)) : option (list (A * B)) :=
  let lift_one_option (kv : A * option B) (acc : option (list (A * B))) :=
    match kv, acc with
    | (k, Some v), Some acc' => Some ((k, v) :: acc')
    | _, _ => None
    end
  in List.fold_right lift_one_option (Some []) l.

Definition kv_map_func {K A B} (f: A -> B) (kv : K * A): K * B :=
  let (k, v) := kv in (k, f v).

Definition kv_map {K A B} (f: A -> B) (kvs : list (K * A)): list (K * B) :=
  List.map (kv_map_func f) kvs.

End SyntaxUtil.

Inductive OptForall {A: Type} (P: A -> Prop): list (option A) -> Prop :=
| OptForall_nil: OptForall P nil
| OptForall_cons_None: forall (l: list (option A)),
    OptForall P l -> OptForall P (None :: l)
| OptForall_cons_Some: forall (x: A) (l: list (option A)),
    P x -> OptForall P l -> OptForall P (Some x :: l).

Section ExprInd.
  Context {tags_t: Type}.
  Notation P4String := (P4String.t tags_t).
  Notation P4Int := (P4Int.t tags_t).
  Notation Expression := (@Expression tags_t).

  Variable P: Expression -> Prop.

  Hypothesis HBool: forall t typ dir b, P (MkExpression t (ExpBool b) typ dir).
  Hypothesis HInt: forall t typ dir i, P (MkExpression t (ExpInt i) typ dir).
  Hypothesis HString: forall t typ dir s, P (MkExpression t (ExpString s) typ dir).
  Hypothesis HName: forall t typ dir n l, P (MkExpression t (ExpName n l) typ dir).
  Hypothesis HArrayAccess: forall t typ dir ary idx,
      P ary -> P idx -> P (MkExpression t (ExpArrayAccess ary idx) typ dir).
  Hypothesis HBitStringAccess: forall t typ dir bits lo hi,
      P bits -> P (MkExpression t (ExpBitStringAccess bits lo hi) typ dir).
  Hypothesis HList: forall t typ dir vs,
      Forall P vs -> P (MkExpression t (ExpList vs) typ dir).
  Hypothesis HRecord: forall t typ dir es,
      Forall (fun '(_,v) => P v) es -> P (MkExpression t (ExpRecord es) typ dir).
  Hypothesis HUnaryOp: forall t typ dir op arg,
      P arg -> P (MkExpression t (ExpUnaryOp op arg) typ dir).
  Hypothesis HBinaryOp: forall t typ dir op args,
      P (fst args) -> P (snd args) -> P (MkExpression t (ExpBinaryOp op args) typ dir).
  Hypothesis HCast: forall t typ1 dir typ expr,
      P expr -> P (MkExpression t (ExpCast typ expr) typ1 dir).
  Hypothesis HTypeMember: forall t typ1 dir typ name,
      P (MkExpression t (ExpTypeMember typ name) typ1 dir).
  Hypothesis HErrorMember: forall t typ dir n,
      P (MkExpression t (ExpErrorMember n) typ dir).
  Hypothesis HExpressionMember: forall t typ dir exp name,
      P exp -> P (MkExpression t (ExpExpressionMember exp name) typ dir).
  Hypothesis HTernary: forall t typ dir cond tru fls,
      P cond -> P tru -> P fls -> P (MkExpression t (ExpTernary cond tru fls) typ dir).
  Hypothesis HFunctionCall: forall t typ dir func type_args args,
      P func -> OptForall P args ->
      P (MkExpression t (ExpFunctionCall func type_args args) typ dir).
  Hypothesis HNamelessInstantiation: forall t typ1 dir typ args,
      Forall P args -> P (MkExpression t (ExpNamelessInstantiation typ args) typ1 dir).
  Hypothesis HDontCare: forall t typ dir, P (MkExpression t ExpDontCare typ dir).

  Fixpoint expr_ind (e: Expression): P e :=
    let fix lind (vs: list Expression): Forall P vs :=
      match vs with
      | nil => Forall_nil _
      | v :: rest => Forall_cons _ (expr_ind v) (lind rest)
      end in
    let fix alind (vs: P4String.AList tags_t Expression):
      Forall (fun '(_, v)=> P v) vs :=
      match vs with
      | nil => Forall_nil _
      | (_, v) as xv :: rest => Forall_cons xv (expr_ind v) (alind rest)
      end in
    let fix olind (vs: list (option Expression)): OptForall P vs :=
      match vs with
      | nil => OptForall_nil _
      | None :: rest => OptForall_cons_None _ _ (olind rest)
      | Some x :: rest => OptForall_cons_Some _ _ _ (expr_ind x) (olind rest)
      end in
    match e with
    | MkExpression t expr typ1 dir =>
        match expr with
        | ExpBool b => HBool t typ1 dir b
        | ExpInt i => HInt t typ1 dir i
        | ExpString s => HString t typ1 dir s
        | ExpName n l => HName t typ1 dir n l
        | ExpArrayAccess ary idx =>
            HArrayAccess t typ1 dir ary idx (expr_ind ary) (expr_ind idx)
        | ExpBitStringAccess bits lo hi =>
            HBitStringAccess t typ1 dir bits lo hi (expr_ind bits)
        | ExpList vs => HList t typ1 dir vs (lind vs)
        | ExpRecord es => HRecord t typ1 dir es (alind es)
        | ExpUnaryOp op e => HUnaryOp t typ1 dir op e (expr_ind e)
        | ExpBinaryOp op args =>
            HBinaryOp t typ1 dir op args (expr_ind (fst args)) (expr_ind (snd args))
        | ExpCast typ exp => HCast t typ1 dir typ exp (expr_ind exp)
        | ExpTypeMember s1 s2 => HTypeMember t typ1 dir s1 s2
        | ExpErrorMember s => HErrorMember t typ1 dir s
        | ExpExpressionMember exp s =>
            HExpressionMember t typ1 dir exp s (expr_ind exp)
        | ExpTernary cond tru fls =>
            HTernary t typ1 dir cond tru fls
                     (expr_ind cond) (expr_ind tru) (expr_ind fls)
        | ExpFunctionCall func type_args args =>
            HFunctionCall t typ1 dir func type_args args (expr_ind func) (olind args)
        | ExpNamelessInstantiation typ args =>
            HNamelessInstantiation t typ1 dir typ args (lind args)
        | ExpDontCare => HDontCare t typ1 dir
        end
    end.

End ExprInd.
