Require Import Coq.Strings.String.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Poulet4.Syntax.
Require Import Poulet4.Typed.
Require Import Poulet4.P4Arith.
Require Import Poulet4.P4String.
Require Import Poulet4.Semantics.
Require Import Poulet4.Monads.Monad.
Require Import Poulet4.Monads.Option.

Section Interpreter.
  Context {tags_t: Type} {inhabitant_tags_t : Inhabitant tags_t}.
  Notation Val := (@ValueBase bool).
  Notation Sval := (@ValueBase (option bool)).
  Notation ValSet := (@ValueSet tags_t).
  Notation Lval := (@ValueLvalue tags_t).

  Notation ident := string.
  Notation path := (list ident).
  Notation P4Int := (P4Int.t tags_t).

  Context {target : @Target tags_t (@Expression tags_t)}.
  Variable (ge : genv).

  Definition last_index_of_next (next: N) : option Sval :=
    if (next =? 0)%N 
    then uninit_sval_of_typ None (TypBit 32)
    else Some (ValBaseBit (to_loptbool 32 (Z.of_N (next - 1)))).

  (* This function implements the get_member relation from the
     big-step semantics. *)
  Definition find_member (v: Sval) (member: string) : option Sval :=
    match v with
    | ValBaseStruct fields
    | ValBaseRecord fields
    | ValBaseUnion fields
    | ValBaseHeader fields _ =>
      AList.get fields member
    | ValBaseStack headers size next =>
      if string_dec member "size"
      then Some (ValBaseBit (to_loptbool 32 (Z.of_N size)))
      else if string_dec member "lastIndex"
           then last_index_of_next next
           else None
    | _ => None
    end.

  Definition interp_val {A B: Type} (v: @ValueBase A) : option (@ValueBase B) :=
    None.

  Definition interp_val_sval (v: Val) : option Sval :=
    interp_val v.

  Definition interp_sval_val (v: Sval) : option Val :=
    interp_val v.

  Fixpoint interp_expr (this: path) (st: state) (expr: @Expression tags_t) : option Sval :=
    let '(MkExpression tags expr typ dir) := expr in
    interp_pre_expr this st dir expr
  with interp_pre_expr (this: path) (st: state) (dir: direction) (expr: @ExpressionPreT tags_t) : option Sval :=
    match expr with
    | ExpBool b =>
      mret (ValBaseBool (Some b))
    | ExpInt i =>
      mret (eval_p4int_sval i)
    | ExpString s =>
      mret (ValBaseString (str s))
    | ExpName x loc =>
      if is_directional dir
      then loc_to_sval loc st
      else loc_to_sval_const ge this loc
    | ExpArrayAccess array index => None
    | ExpBitStringAccess bits lo hi => None
    | ExpList value => None
    | ExpRecord entries => None
    | ExpUnaryOp op arg =>
      let* argsv := interp_expr this st arg in
      let* argv := interp_val argsv in
      let* v := Ops.eval_unary_op op argv in
      interp_val_sval v
    | ExpBinaryOp op args => None
    | ExpCast typ expr => None
    | ExpTypeMember typ name => None
    | ExpErrorMember x => None
    | ExpExpressionMember expr name => None
    | ExpTernary cond tru fls => None
    | ExpFunctionCall func type_args args => None
    | ExpNamelessInstantiation typ args => None
    | ExpDontCare => None
    end.

End Interpreter.
