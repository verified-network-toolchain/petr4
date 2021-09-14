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

(* TODO move to Result.v *)
Definition cons_res {A : Type} (hd_res : result A) (rlist : result (list A)) : result (list A) :=
  let* l := rlist in
  let** hd := hd_res in
  hd :: l.

Print Typed.name.
Program Fixpoint translate_exp_type (i : tags_t) (typ : @P4Type tags_t) {struct typ} : result E.t :=
  let translate_fields :=
      fold_right (fun '(name,typ) res_rst =>
                    let* cub_typ := translate_exp_type i typ in
                    let** rst := res_rst in
                    (P4String.str name, cub_typ) :: rst ) (ok [])
  in
  match typ with
  | TypBool => ok E.TBool
  | TypString =>
    (* TODO Strings should only occur as arguments to externs.  We should add these to P4cub *)
    ok E.TString
  | TypInteger =>
    (* TODO This should be added to P4cub, but can only be a value; enforced by the type system *)
    error "[FIXME] P4cub doesnt support Integers"
  | TypInt w => ok (E.TInt (pos w))
  | TypBit w => ok (E.TBit (pos w))
  | TypVarBit w =>
    error "[FIXME] Compile to fixed-width"
  | TypArray typ size =>
    match typ with
    | TypHeader fields =>
      let** cub_fields := translate_fields fields in
      E.THeaderStack cub_fields (pos size)
    | _ => error "Typeerror:: Arrays must contain Headers"
    end
  | TypTuple types =>
    (* TODO ensure are cast-able *)
    let** cub_types := fold_right (cons_res ∘ (translate_exp_type i)) (ok []) types in
    E.TTuple cub_types
  | TypList types =>
    let** cub_types := fold_right (cons_res ∘ (translate_exp_type i)) (ok []) types in
    E.TTuple cub_types
  | TypRecord fields =>
    let** cub_fields := translate_fields fields in
    E.TStruct cub_fields
  | TypSet elt_type =>
    (* Shows up in typechecking a select *)
    error "A set is not an expression type"
  | TypError => ok E.TError
  | TypMatchKind => ok E.TMatchKind
  | TypVoid => error "[FIXME] void is not the type of any expression literal"
  | TypHeader fields =>
    let** fields' := translate_fields fields in
    E.THeader fields'
  | TypHeaderUnion _ =>
    error "[FIXME] Header Unions need to be compiled away or added to p4cub"
  | TypStruct fields =>
    let** fields' := translate_fields fields in
    E.TStruct fields'
  | TypEnum name typ members =>
    (* TODO We're throwing away the type here. Should we be? *)
    let cub_name := P4String.str name in
    (* For some reason Coq needs this to ebe explicitly applied in order to guess the tags argument *)
    let cub_members := List.map (fun s => P4String.str s) members in
    ok (E.TEnum cub_name cub_members)
  | TypTypeName name =>
    match name with
    | BareName nm =>
      ok (E.TVar (P4String.str nm))
    | QualifiedName _ _ =>
      error "Unsure how to handle qualified names"
    end
  | TypNewType name typ =>
    let** typ' := translate_exp_type i typ in
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
  end.

Definition realize_array_index (e : @Expression tags_t) : result Z :=
  match e with
  | MkExpression _ (ExpInt z) _ _  =>
    (*TODO Do we have to do some normalizaztion here?*)
    ok (z.(value))
  | _ =>
    error "Array Indices must be literals"
  end.

Fixpoint translate_expression_pre_t (i : tags_t) (typ : P4Type) (e_pre : @ExpressionPreT tags_t) : result (E.e tags_t) :=
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
    | None => error "[FIXME] integer didnt have a width."
    end
  | ExpString s =>
    ok (E.EString (P4String.str s) i)
  | ExpName name loc =>
    match name with
    | BareName str =>
      let** cub_type := translate_exp_type i typ in
      E.EVar cub_type (P4String.str str) i
    | QualifiedName namespaces name =>
      error "Qualified names should be eliminated"
    end
  | ExpArrayAccess array index =>
    let* (_,stck) := translate_expression array in
    let** index := realize_array_index index in
    E.EHeaderStackAccess stck index i
  | ExpBitStringAccess bits lo hi =>
    let** (typ,e) := translate_expression bits in
    E.ESlice e typ (posN hi) (posN lo) i
  | ExpList values =>
    let f := fun v res_rst =>
               let* (_,cub_v) := translate_expression v in
               let** rst := res_rst in
               cub_v :: rst in
    let** cub_values := fold_right f (ok []) values in
    E.ETuple cub_values i
  | ExpRecord entries =>
    let f := fun kv res_rst =>
               let '(MkKeyValue i nm expr) := kv in
               let* type_expr := translate_expression expr in
               let** rst := res_rst in
               (P4String.str nm, type_expr) :: rst in
    let** cub_entries := fold_right f (ok []) entries  in
    E.EStruct cub_entries i
  | ExpUnaryOp op arg =>
    let eop := translate_op_uni op in
    let** (type, earg) := translate_expression arg in
    E.EUop eop type earg i
  | ExpBinaryOp op (e1,e2) =>
    let* (t1,e1') := translate_expression e1 in
    let* (t2,e2') := translate_expression e2 in
    let** eop := translate_op_bin op in
    E.EBop eop t1 t2 e1' e2' i
  | ExpCast typ expr =>
    let* (_,expr') := translate_expression expr in
    let** typ' := translate_exp_type i typ in
    E.ECast typ' expr' i
  | ExpTypeMember typ name =>
    error "[FIXME] type members unimplemented"
  | ExpErrorMember str =>
    ok (E.EError (Some (P4String.str str)) i)
  | ExpExpressionMember expr name =>
    let** (cub_typ,cub_expr) := translate_expression expr in
    E.EExprMember (P4String.str name) cub_typ cub_expr i
  | ExpTernary cond tru fls =>
    error "[FIXME] ternary expressions unimplemented"
  | ExpFunctionCall func type_args args =>
    error "[FIXME] function calls unimplemented"
  | ExpNamelessInstantiation typ args =>
    error "[FIXME] nameless insts unimplemented"
  | ExpDontCare =>
    error "[FIXME] These are actually patterns (unimplemented)"
  | ExpMask expr mask =>
    error "[FIXME] actually patterns (unimplemented)"
  | ExpRange lo hi =>
    error "[FIXME] actually patterns (unimplemented)"
  end
with translate_expression (e : @Expression tags_t) : result (E.t * E.e tags_t) :=
  match e with
  | MkExpression tags expr typ dir =>
    let* cub_type := translate_exp_type tags typ in
    let** cub_expr := translate_expression_pre_t tags typ expr in
    (cub_type, cub_expr)
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
    let* (cub_ltyp, cub_lhs) := translate_expression lhs in
    let** (_, cub_rhs) := translate_expression rhs in
    ST.SAssign cub_ltyp cub_lhs cub_rhs i
  | StatDirectApplication typ args =>
    error "[FIXME] (StatDirectApplication) Need to translate into instantiation and then application"
  | StatConditional cond tru fls_opt =>
    let* (cub_type, cub_cond) := translate_expression cond in
    let* cub_tru := translate_statement tru in
    let** cub_fls := match fls_opt with
                     | None => ok (ST.SSkip i)
                     | Some fls => translate_statement fls
                     end in
    ST.SConditional cub_type cub_cond cub_tru cub_fls i
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
      let** (cub_typ, cub_expr) := translate_expression e in
      ST.SReturnFruit cub_typ cub_expr i
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
