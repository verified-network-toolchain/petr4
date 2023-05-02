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
     Surface.Typing.Utils
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

  (*dummy function definition. fill in later. TODO.*)
  Definition type_bit_string_access (env: checkerEnvs) (w: N) (low: expression) (type_low: typ) (high: expression) (type_high: typ) : result Exn.t typ :=
    error (Exn.Other "fill out later.").

  (*dummy function definition. fill in later. TODO.*)
  (*hint: binary operation rules in formalized spec. disregard the insertion of cast. that is, assume that all casts have been inserted.*)
  (*hint: lib/checker.ml --> type_binary_op.*)
  Definition type_binary_op (env: checkerEnvs) (op: binOp) (arg1: expression) (type_arg1: typ) (arg2: expression) (type_arg2: typ) : result Exn.t typ :=
    match op with
    | And _
    | Or _
      => error (Exn.Other "@Harim fill out.")
    | Plus _
    | Minus _
    | Mul _
      => error (Exn.Other "@Harim fill out.")
    | Eq _
    | NotEq _
      => error (Exn.Other "@Harim fill out.")
    | PlusSat _
    | MinusSat _
      => error (Exn.Other "@Harim fill out.")
    | BitAnd _
    | BitXor _
    | BitOr _
      => error (Exn.Other "@Harim fill out.")
    | PlusPlus _
      => error (Exn.Other "@Harim fill out.")
    | Le _
    | Ge _
    | Lt _
    | Gt _
      => error (Exn.Other "@Harim fill out.")
    | Mod _
    | Div _
      => error (Exn.Other "@Harim fill out.")
    | Shl _
    | Shr _
      => error (Exn.Other "@Harim fill out.")
    end.

  (*dummy function definition. fill in later. TODO.*)
  (*checks equality of two types. If they are equal it returns true, otherwise, it returns false.*)
  (*assume all generic types have been instantiated. *)
  (*hint: type equality judgment in formalized spec.*)
  (*hint: lib/checker.ml --> type_equality function which calls solve_types. solve_types does the inference.*)
  Definition type_eq (typ1 typ2: typ) : bool :=
    false.

  Definition type_mask (type_expr type_mask: typ) : result Exn.t typ :=
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

  (*dummy function definition. fill in later. TODO.*)
  Definition type_expression_member (env: checkerEnvs) (type_expr: typ) (mem: P4String) : result Exn.t typ :=
    error (Exn.Other "fill in later.").

  (*the tuple case has little mismatches of types. TODO. fix it. for now returns a dummy value.*)
  Definition type_array_access (env: checkerEnvs) (array: expression) (type_array: typ) (index: expression) (type_index: typ) : result Exn.t typ :=
    error (Exn.Other "fill in later.").
    (* match type_array with *)
    (* | TypHeaderStack tags typ size *)
    (*   => if is_numeric env index type_index *)
    (*     then ok typ *)
    (*     else error (Exn.Other "array index not numeric") *)
    (*                    (*the following block has a weird error. ask Ryan.*) *)
    (* | TypTuple tags types *)
    (*   => if is_integer type_index *)
    (*     then let* i := from_opt (compile_time_eval env index) *)
    (*                             (Exn.Other "failure in compile_time_eval")in *)
    (*          let* idx := from_opt (array_access_idx_to_z i) *)
    (*                               (Exn.Other "failure in array_access_idx_to_z")in *)
    (*          if andb (Nat.leb 1 (N.to_nat idx)) *)
    (*                  (Nat.leb (N.to_nat idx) (List.length types)) *)
    (*          then ok typ (*(Znth_default (TypVoid tags) (idx) types)*) (*TODO: dummy value returned*) *)
    (*          else error (Exn.Other "array access index out of bound") *)
    (*     else error (Exn.Other "array access index not integer") *)
    (* | _ => error (Exn.Other "array access type incorrect") *)
    (* end. *)

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
            type_array_access env array type_array index type_index
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
        (*   => let* types := rred (map (type_expression env tags) value) in *)
        (*     ok (TypTuple types) *)
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
            type_binary_op env op arg1 type_arg1 arg2 type_arg2
        | ExpCast typ expr
          => let* type_expr := type_expression env tags expr in
            match type_expr with
            | TypName tags name
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
        | ExpTypeMember typ mem
          => let* (t, d) := lookup_var (append_type typ mem) env in
            ok t
        | ExpErrorMember mem
          => let* (t, d) := lookup_var (append_error mem) env in
            if is_type_error t
            then ok t
            else error (Exn.Other "error member type incorrect")
        | ExpExpressionMember expr mem
          => let* type_expr := type_expression env tags expr in
            type_expression_member env type_expr mem
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
          => let* typed_expr := type_expression env tags expr in
            let* typed_mask := type_expression env tags mask in
            type_mask typed_expr typed_mask
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

