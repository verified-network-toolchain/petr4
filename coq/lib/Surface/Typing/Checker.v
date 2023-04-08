From Coq Require Import Lists.List
     NArith.NArith
     Strings.String
     ZArith.ZArith.

(* From Coq Require Import Numbers.BinNums Classes.EquivDec. *)
From Poulet4 Require Import Utils.AList
     Monads.Option
     Utils.AListUtil
     (* Monads.Result *)
     Surface.Syntax.Syntax
     Surface.Typing.CheckerEnv
     P4light.Syntax.Info
     P4light.Syntax.P4Int
     P4light.Semantics.Semantics.

From Poulet4.P4light.Syntax Require P4String.

Import Result ResultNotations.
(*initially have none for types when you parse from p4 to surface ir. *)

Section Checker.

  (* Context {tags_t: Type}. *)
  Notation P4String := (P4String.t Info).
  Notation P4Int := (P4Int.t Info).
  Notation Val := (@ValueBase bool).

  Definition type_int (tags: Info) (i: P4Int) : typ :=
    match width_signed i with
    | None                => TypInteger tags
    | Some (width, true)  => TypInt tags width
    | Some (width, false) => TypBit tags width
    end.

  (*dummy function definition for now. TODO: fill in.*)
  Definition compile_time_eval (env: checkerEnvs) (exp: expression) : option Val :=
    match exp with
    | _ => Some ValBaseNull
    end.

  Definition compile_time_known (env: checkerEnvs) (exp: expression) : bool :=
    match compile_time_eval env exp with
    | Some _ => true
    | _      => false
    end.


  Definition is_numeric (env: checkerEnvs) (exp: expression) (type: typ) : bool :=
    match type with
    | TypInt _ _   => true
    | TypBit _ _   => true
    | TypInteger _ => compile_time_known env exp
    | _            => false
    end.

  Definition is_bool (type: typ) : bool :=
    match type with
    | TypBool _ => true
    | _         => false
    end.

  Definition is_fixed_width_int (type: typ) : bool :=
    match type with
    | TypInt _ _ => true
    | TypBit _ _ => true
    | _          => false
    end.

  Definition is_integer (type: typ) : bool :=
    match type with
    | TypInteger _ => true
    | _            => false
    end.

  (*dummy function definition. fill in later. TODO.*)
  Definition to_nat (val: Val) : nat := 0.

  (*dummy function definition. fill in later. TODO.*)
  Definition type_bit_string_access (env: checkerEnvs) (w: N) (low: expression) (type_low: typ) (high: expression) (type_high: typ) : result Exn.t typ :=
    error (Exn.Other "fill out later.").

  (*dummy function definition. fill in later. TODO.*)
  Definition binary_op_typing (env: checkerEnvs) (op: binOp) (arg1: expression) (type_arg1: typ) (arg2: expression) (type_arg2: typ) : result Exn.t typ :=
    error (Exn.Other "fill out later.").

  (*dummy function definition. fill in later. TODO.*)
  Definition cast (env:checkerEnvs) (typ1 typ2: typ) : bool :=
    false.

  (*dummy function definition. fill in later. TODO.*)
  Definition lookup_type (type: P4String) (env: checkerEnvs) : result Exn.t typ :=
    error (Exn.Other "fill out later.").

  (*dummy function definition. fill in later. TODO.*)
  Definition type_eq (typ1 typ2: typ) : bool :=
    false.

  Definition mask_type (type_expr type_mask: typ) : result Exn.t typ :=
    match type_expr, type_mask with
    | TypBit _ w, TypBit _ w'
      => if (w == w')
        then ok type_mask
        else error (Exn.Other "mask incorrect")
    | TypBit w _, TypInteger _
      => ok type_mask
    | TypInteger _, TypBit w _
      => ok type_mask
    | _, _
      => error (Exn.Other "mask incorrect")
    end.

  Fixpoint type_expression (env: checkerEnvs) (tags: Info) (expr: expression) : result Exn.t typ :=
    match expr with
    | MkExpression tags type expr =>
        match expr with
        | ExpBool b
          => ok (TypBool tags)
        | ExpString s
          => ok (TypString tags)
        | ExpInt  i
          => ok (type_int tags i)
        | ExpName name
          => let* name' := from_opt (get_name name)
                                   (Exn.Other "qualified name failure") in
            let* (t, d) := from_opt (get (varEnv env) name')
                                    (Exn.Other "name not found") in
            ok t
        | ExpArrayAccess array index
          => let* type_array := type_expression env tags array in
            let* type_index := type_expression env tags index in
            match type_array with
            | TypHeaderStack tags typ size
              => if is_numeric env index type_index
                then ok typ
                else error (Exn.Other "array index not numeric")
                       (*the following block has a weird error. ask Ryan.*)
            (* | TypTuple tags types *)
              (* => if is_integer type_index *)
                (* then let* i := from_opt (compile_time_eval env index) *)
                                        (* (Exn.Other "failure in compile_time_eval")in *)
                     (* let* idx := from_opt (array_access_idx_to_z i) *)
                                          (* (Exn.Other "failure in array_access_idx_to_z")in *)
                     (* if andb (Nat.leb 1 (N.to_nat idx)) *)
                     (*         (Nat.leb (N.to_nat idx) (List.length types)) *)
                     (* then ok (Znth_default (TypVoid tags) (idx) types) *)
                     (* else error (Exn.Other "array access index out of bound") *)
                (* else error (Exn.Other "array access index not integer") *)
            | _ => error (Exn.Other "array access type incorrect")
            end
        | ExpBitStringAccess bits low high
          => let* type_bits := type_expression env tags bits in
            let* type_low  := type_expression env tags low in
            let* type_high := type_expression env tags high in
            match type_bits with
            | TypInt t w => type_bit_string_access env w low type_low high type_high
            | TypBit t w => type_bit_string_access env w low type_low high type_high
            | _ => error (Exn.Other "bit string access type incorrect")
            end
        (* | ExpList value *)
        (*   => let types := map (type_expression env tags) value in *)
        (*     if In None types *)
        (*     then None *)
        (*     else *)
        (*     ok (map from_opt types) *)
        (* | ExpRecord entries *)
        (*   => TypBool tags *)
        | ExpUnaryOp op arg
          => let* type_arg := type_expression env tags arg in
            match op with
            | Not tags
              => if is_bool type_arg
                then ok type_arg
                else error (Exn.Other "unary arg type not bool")
            | BitNot tags
              => if is_fixed_width_int type_arg
                then ok type_arg
                else error (Exn.Other "unary arg type not fixed width")
            | UMinus tags
              => if is_numeric env arg type_arg
                then ok type_arg
                else error (Exn.Other "unary arg type not numeric")
            end
        | ExpBinaryOp op arg1 arg2
          => let* type_arg1 := type_expression env tags arg1 in
            let* type_arg2 := type_expression env tags arg2 in
            binary_op_typing env op arg1 type_arg1 arg2 type_arg2
        | ExpCast typ expr
          => let* type_expr := type_expression env tags expr in
            match type_expr with
            | TypIdentifier tags name
              => let* typ' := lookup_type name env in
                let cast_ok := cast env typ typ' in
                if cast_ok
                then ok typ
                else error (Exn.Other "cast incorrect")
            | _
              => let cast_ok := cast env typ type_expr in
                if cast_ok
                then ok typ
                else error (Exn.Other "cast incorrect")
            end
        (* | ExpTypeMember typ mem *)
          (* => TypBool tags *)
        (* | ExpErrorMember mem *)
          (* =>  *)
        (* | ExpExpressionMember expr mem *)
        (*   => TypBool tags *)
        | ExpTernary cond tru fls
          => let* type_cond := type_expression env tags cond in
            let* type_tru  := type_expression env tags tru in
            let* type_fls  := type_expression env tags fls in
            match type_cond with
            | TypBool _
              => match type_tru with
                | TypInteger _
                  => if andb (is_integer type_fls)
                            (compile_time_known env cond)
                    then ok type_tru
                    else error (Exn.Other "ternary type incorrect")
                | _ => if type_eq type_tru type_fls
                      then ok type_tru
                      else error (Exn.Other "mismatch type tru fls ternary")
                end
            | _ => error (Exn.Other "ternary condition type incorrect")
            end
        (* | ExpFunctionCall func type_args args *)
        (*   => TypBool tags *)
        (* | ExpAnonymousInstantiation typ args *)
        (*   => TypBool tags *)
        | ExpBitMask expr mask
          => let* type_expr := type_expression env tags expr in
            let* type_mask := type_expression env tags mask in
            mask_type type_expr type_mask
        | ExpRange low high
          => let* type_low  := type_expression env tags low in
            let* type_high := type_expression env tags high in
            if andb (type_eq type_low type_high) (is_fixed_width_int type_low)
            then ok (TypSet tags type_low)
            else error (Exn.Other "range types incorrect")
        | _ => error (Exn.Other "filling out the func")
        end
    end.

  Definition type_statement (tags: Info) (stmt: statement ) : typ :=
    match stmt with
    | MkStatement tags type stmt
      => match stmt with
        | StmtMethodCall func type_args args
          => TypBool tags
        | StmtAssignment lhs rhs
          => TypBool tags
        | StmtDirectApplication typ args
          => TypBool tags
        | StmtConditional cond tru fls
          => TypBool tags
        | StmtBlock block
          => TypBool tags
        | StmtExit
          => TypBool tags
        | StmtEmpty
          => TypBool tags
        | StmtReturn expr
          => TypBool tags
        | StmtSwitch expr cases
          => TypBool tags
        | StmtDeclConstant typ name value
          => TypBool tags
        | StmtDeclVariable typ name init
          => TypBool tags
        | StmtDeclInstantiation typ args name init
          => TypBool tags
        end
    end.

  Definition type_declaration (tags: Info) (decl: declaration) : typ :=
    match decl with
    | MkDeclaration tags type decl
      => match decl with
        | DeclConstant typ name value
          => TypBool tags
        | DeclInstantiation typ args name init
          => TypBool tags
        | DeclParser name type_params params constructor_params locals states
          => TypBool tags
        | DeclControl name type_params params constructor_params locals apply
          => TypBool tags
        | DeclFunction ret_type name type_params params body
          => TypBool tags
        | DeclExternFunction ret_type name type_params params
          => TypBool tags
        | DeclVariable typ name init
          => TypBool tags
        | DeclValueSet typ name size
          => TypBool tags
        | DeclAction name data_params ctrl_params body
          => TypBool tags
        | DeclTable name props
          => TypBool tags
        | DeclHeaderTyp name fields
          => TypBool tags
        | DeclHeaderUnionTyp name fields
          => TypBool tags
        | DeclStructTyp name fields
          => TypBool tags
        | DeclError members
          => TypBool tags
        | DeclMatchKind members
          => TypBool tags
        | DeclEnumTyp name members
          => TypBool tags
        | DeclSerializableEnum typ name members
          => TypBool tags
        | DeclControlTyp name type_params params
          => TypBool tags
        | DeclParserTyp name type_params params
          => TypBool tags
        | DeclPackageTyp name type_params params
          => TypBool tags
        | DeclExternObject name type_params methods
          => TypBool tags
        | DeclTypeDef name typ_or_dcl
          => TypBool tags
        | DeclNewType name typ_or_dcl
          => TypBool tags
        end
    end.

End Checker. 

