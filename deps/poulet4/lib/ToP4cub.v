Require Export Poulet4.Syntax.

Require Export Poulet4.P4cub.Syntax.Syntax
               Poulet4.P4cub.Util.Result.
Import AST Result P4cub.
Import ResultNotations.

Require Import String.
Open Scope string_scope.


Module ST := Stmt.
Module E := Expr.

Variable tags_t : Type.

Import Typed.
Import P4Int.

Definition pos : (nat -> positive) := BinPos.Pos.of_nat.
Definition posN (n : N) : positive := pos (BinNat.N.to_nat n).

Definition translate_op_uni (op : OpUni) : E.uop :=
  match op with
  | Not => E.Not
  | BitNot => E.BitNot
  | UMinus => E.UMinus
  end.

Definition translate_op_bin (op : OpBin) : result E.bop :=
  match op with
  | Plus => ok E.Plus
  | PlusSat => ok E.PlusSat
  | Minus => ok E.Minus
  | MinusSat => ok E.MinusSat
  | Mul => ok E.Times
  | Div => error "division not supported"
  | Mod => error "mod not supported"
  | Shl => ok E.Shl
  | Shr => ok E.Shr
  | Le => ok E.Le
  | Ge => ok E.Ge
  | Lt => ok E.Lt
  | Gt => ok E.Gt
  | Eq => ok E.Eq
  | NotEq => ok E.NotEq
  | BitAnd => ok E.BitAnd
  | BitXor => ok E.BitXor
  | BitOr => ok E.BitOr
  | PlusPlus => ok E.PlusPlus
  | And => ok E.And
  | Or => ok E.Or
  end.

Locate AList.

Fixpoint translate_exp_type (i : tags_t) (typ : @P4Type tags_t) {struct typ} : result E.t :=
  match typ with
  | TypBool => ok E.TBool
  | TypString =>
    (* TODO Strings should only occur as arguments to externs.  We should add these to P4cub *)
    error "[FIXME] P4cub doesnt support strings"
  | TypInteger =>
    (* TODO This should be added to P4cub, but can only be a value; enforced by the type system *)
    error "[FIXME] P4cub doesnt support Integers"
  | TypInt w => ok (E.TInt (pos w))
  | TypBit w => ok (E.TBit (pos w))
  | TypVarBit w =>  error "[FIXME] Add to p4cub -- remove in a later pass?"
  | TypArray typ size =>
    error "[FIXME] this is a headerstack"
  | TypTuple types =>
    let** types' := rred (List.map (translate_exp_type i) types) in
    E.TTuple types'
  | TypList types =>
    error "[FIXME] Should this be compiled to a tuple literal -- make sure we allow tuples to be cast"
  | TypRecord fields =>
    error "[FIXME] nearly a struct literal"
  | TypSet elt_type =>
    (* Shows up in typechecking a select *)
    error "[FIXME] translate to patterns"
  | TypError => ok E.TError
  | TypMatchKind => ok E.TMatchKind
  | TypVoid => error "[FIXME] void cannot type any expression literal"
  | TypHeader fields =>
    let** fields' := translate_alist_p4type i fields in
    E.THeader fields'
  | TypHeaderUnion _ =>
    error "[FIXME] Header Unions need to be compiled away or added to p4cub"
  | TypStruct fields =>
    let** fields' := translate_alist_p4type i fields in
    E.TStruct fields'
  | TypEnum name typ members =>
    error "[FIXME] Add Enums to p4cub"
  | TypTypeName name =>
    error "[FIXME] Should be in P4cub"
  | TypNewType name typ =>
    let** typ' := translate_expression_typ i typ in
    typ'
  | TypControl c =>
    error "A control is not an expression type"
  | TypParser c =>
    error "A Parser is not an expression type"
  | TypExtern name =>
    error "An extern is not an expression type"
  | TypFunction fn =>
    error "A function is not an expression"
  | TypAction _ _ =>
    error "An action is not an expression"
  | TypTable _ =>
    error "A table is not an expression"
  | TypPackage _ _ _ =>
    error "A package is not an expression"
  | TypSpecializedType base args =>
    error "Specialized types are not expression types"
  | TypConstructor _ _ _ _ =>
    error "A type constructor is not an expression"
  end
with translate_alist_p4type (i : tags_t) (fields : P4String.AList tags_t P4Type) : result (F.fs EquivUtil.string E.t) :=
  match fields with
  | [] => ok []
  | (name, typ)::rst =>
    let* typ' := translate_exp_type i typ in
    let** rst' := translate_alist_p4type i rst in
    (P4String.str name, typ')::rst'
  end.

Fixpoint translate_expression_pre_t (i : tags_t) (e_pre : @ExpressionPreT tags_t) : result (E.e tags_t) :=
  match e_pre with
  | ExpBool b =>
    ok (E.EBool b i)
  | ExpInt z =>
    match z.(width_signed) with
    | Some (w, b) =>
      if b then
        ok (E.EInt (pos w) z.(value) z.(tags))
      else
        ok (E.EBit (pos w) z.(value) z.(tags))
    | None => error "[FIXME] integer didnt have a width. What to do?"
    end
  | ExpString s =>
    error "[FIXME] Strings aren't real in P4cub (see above)"
  | ExpName name loc =>
    match name with
    | BareName str =>
      error "[FIXME] I want to translate this to an EVar but there's no type"
    | QualifiedName namespaces name =>
      error "Qualified names should be eliminated"
    end

  | ExpArrayAccess array index =>
    error "[FIXME] Need to hoist array literals to sequence of assignments"
  | ExpBitStringAccess bits lo hi =>
    let* e := translate_expression bits in
    let** typ := error "[FIXME] need type" in
    E.ESlice e typ (posN hi) (posN lo) i
  | ExpList value =>
    error "[FIXME] compile out lists"
  | ExpRecord entries =>
    error "[FIXME] Records should be structs?"
  | ExpUnaryOp op arg =>
    let eop := translate_op_uni op in
    let* type := error "[FIXME] need a type for unary operations" in
    let** earg := translate_expression arg in
    E.EUop eop type earg i
  | ExpBinaryOp op (e1,e2) =>
    let* e1' := translate_expression e1 in
    let* e2' := translate_expression e2 in
    let* t1 := error "[FIXME] need a type for the LHS of a binary operation" in
    let* t2 := error "[FIXME] need a type for the RHS of a binary operation"in
    let** eop := translate_op_bin op in
    E.EBop eop t1 t2 e1' e2' i
  | ExpCast typ expr =>
    let* expr' := translate_expression expr in
    let** typ' := translate_exp_type in
    E.ECast typ' expr'
  | ExpTypeMember typ name =>
    error "[FIXME] type members unimplemented"
  | ExpErrorMember str =>
    error "[FIXME] error members unimplemented"
  | ExpExpressionMember expr name =>
    error "[FIXME] expression members unimplemented"
  | ExpTernary cond tru fls =>
    error "[FIXME] ternary expressions unimplemented"
  | ExpFunctionCall func type_args args =>
    error "[FIXME] function calls unimplemented"
  | ExpNamelessInstantiation typ args =>
    error "[FIXME] nameless insts unimplemented"
  | ExpDontCare =>
    error "[FIXME] These are actually pattersns -- dont carees unimplemented"
  | ExpMask expr mask =>
    error "[FIXME] actually patterns masks unimplemented"
  | ExpRange lo hi =>
    error "[FIXME] actually patterns ranges unimplemented"
  end
with translate_expression (e : @Expression tags_t) : result (E.e tags_t) :=
  match e with
  | MkExpression tags expr typ dir =>
    translate_expression_pre_t tags expr
  end.



Fixpoint translate_statement_switch_case (ssw : @StatementSwitchCase tags_t) : result (ST.s tags_t) :=
  match ssw with
  | StatSwCaseAction tags label code =>
    error "[FIXME] switch case action unimplemented"
  | StatSwCaseFallThrough tags label =>
    error "[FIXME] switch case fall trhough unimplemented"
  end
with translate_statement_pre_t (i : tags_t) (pre_s : @StatementPreT tags_t) : result (ST.s tags_t) :=
  match pre_s with
  | StatMethodCall func type_args args =>
    error "[FIXME] (StatMethodCall) Needs to be disambiguated into Invoke, FUNCTION CALLS, and Extern Method Calls"
  | StatAssignment lhs rhs =>
    error "[FIXME] (StatAssignment) Where do we get the type?"
  | StatDirectApplication typ args =>
    error "[FIXME] (StatDirectApplication) Need to translate into instantiation and then application"
  | StatConditional cond tru fls =>
    error "[FIXME] (StatConditional) Where do we get guard type?"
  | StatBlock block =>
    let** sblck := translate_block i block in
    ST.SBlock sblck
  | StatExit =>
    ok (ST.SExit i)
  | StatEmpty =>
    ok (ST.SSkip i)
  | StatReturn expr_opt =>
    match expr_opt with
    | Some e =>
      error "[FIXME] (StatReturn::Some) `SReturnFruit typ e i` works for translated e but we need a type `typ` and a tag `i`"
    | None =>
      ok (ST.SReturnVoid i)
    end
  | StatSwitch expr cases =>
    error "[FIXME] switch statement not implemented"
  | StatConstant typ name value loc =>
    error "Should not occur"
  | StatVariable typ name init loc =>
    error "Should not occur"
  | StatInstantiation typ args name init =>
    error "Should not occur"
  end
with translate_statement (s : @Statement tags_t) : result (ST.s tags_t) :=
  match s with
  | MkStatement tags stmt typ =>
    translate_statement_pre_t tags stmt
  end
with translate_block (i : tags_t) (b : @Block tags_t) : result (ST.s tags_t) :=
  match b with
  | BlockEmpty tags =>
    ok (ST.SSkip i)
  | BlockCons statement rest =>
    let* s1 := translate_statement statement in
    let** s2 := translate_block i rest in
    ST.SSeq s1 s2 i
  end.
