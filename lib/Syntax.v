Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.NArith.BinNatDef.
Require Import Coq.Bool.Bvector.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

Require Import Monads.Monad.
Require Import Monads.Option.
Require Import Monads.State.

Require Import Utils.
Require Import Environment.
Require Import Value.


Open Scope string_scope.
Close Scope vector_scope.
Open Scope monad.


Inductive direction :=
  | In
  | Out
  | InOut
  | Directionless.

Inductive function_kind := 
  | Parser
  | Control
  | Extern
  | Table
  | Action
  | Function
  | Builtin
.

Inductive name :=
  | BareName (nm: string)
  | QualifiedName (path: list string) (nm: string)
.

Inductive unaryoperator :=
  | Not
  | BitNot
  | BitMinus
.

Inductive binaryoperator :=
  | Plus
  | PlusSat
  | Minus
  | MinusSat
  | Mul
  | Div
  | Mod
  | Shl
  | Shr
  | Le
  | Ge
  | Lt
  | Gt
  | Eq
  | NotEq
  | BitAnd
  | BitXor
  | BitOr
  | PlusPlus
  | And
  | Or
.

Inductive type := 
  | Bool
  | String
  | Integer
  | Int (width: nat)
  | Bit (width: nat)
  | VarBit (width: nat)
  | Array (inner: type) (size: nat)
  | Tuple (types: list type)
  | RecordType (fields: list (string * type))
  | SetType (inner: type)
  | Error
  | MatchKind
  | TypeName (name: string)
  | NewType (inner: type)
  | Void
  | Header (fields: list (string * type))
  | HeaderUnion (fields: list (string * type))
  | Struct (fields: list (string * type))
  | Enum (name: string) (members: list string) (inner: option type)
  | SpecializedType (base: type) (args: list type)
  | ExternType (name: string) (type_params: list string) (methods: list (string * function))
  | FunctionType (inner: function) 
  | ActionType (data_params: list param) (control_params: list param)
  | Constructor (type_params: list string) (params: list param) (return_type: type)

with function := MkFunction 
  (type_params: list string)
  (parameters: list param)
  (kind: function_kind)
  (return_type: type)

with param := MkParam
  (dir: direction)
  (typ: type)
  (variable: string)
  (opt_value: option expression)
  
with keyvalue := MkKeyValue
  (key: string)
  (expr: expression)

with argument :=
  | Expression (value: expression)
  | KeyValue (key: string) (value: expression)
  | Missing

with expression := 
  | BoolExpression (value : bool)
  | IntExpression (value: nat)
  | StringExpression (value: string)
  | NameExpression (value: name)
  | ArrayAccess (array: expression) (index: expression)
  | BitStringAccess (array: expression) (hi: expression) (lo: expression)
  | List (values: list expression)
  | Record (entries: list keyvalue)
  | UnaryOp (op: unaryoperator) (arg: expression)
  | BinaryOp (op: binaryoperator) (arg: expression)
  | Cast (type: type) (expr: expression)
  | TypeMember (type: name) (name: string)
  | ErrorMember (error: string)
  | ExpressionMember (expr: expression) (name: string)
  | Ternary (cond: expression) (true: expression) (false: expression)
  | FunctionCall (function: expression) (type_args: list type) (args: list argument)
  | NamelessInstantiation (type: type) (args: list argument)
  | Mask (expr: expression) (mask: expression)
  | Range (lo: expression) (hi: expression)
.

Inductive declaration :=
  | DeclarationConstant (type: type) (name: string) (value: expression)
  | DeclarationVariable (type: type) (name: string) (init: option expression)
  | Instantiation (type: type) (args: list expression) (name: string)
.

Inductive statement := 
  | MethodCall (func: expression) (type_args: list type) (args: list (option expression))
  | Assignment (lhs: expression) (rhs: expression)
  | BlockStatement (blk: block)
  (* same as the corresponding cases of declaration *)
  | StatementConstant (type: type) (name: string) (value: expression)
  | StatementVariable (type: type) (name: string) (init: option expression)

with block :=
  | BlockEmpty : block
  | BlockCons : statement -> block -> block
.

Inductive match_expression := 
  | DontCare
  | MatchExpression (expr: expression)
.

Module Case.
Record case := { 
  matches: list match_expression;
  next: string 
}.
End Case.

Module Transition.
Record transition := { 
  exprs: list expression;
  cases: list Case.case 
}.
End Transition.

Module State.
Record state := { 
  name: string;
  statements: list statement;
  transition: Transition.transition
}.
End State.


Module Parser.
Record parser := MkParser { 
  parser_name: string;
  (*type_params: list string;*)
  params: list param;
  constructor_params: list param;
  locals: list declaration;
  states: list State.state 
}.
End Parser.

Fixpoint list_slice {A: Type} (l: list A) (lo: nat) (hi: nat) : option (list A) := 
  match (lo, hi) with
  | (0, 0)          => Some nil
  | (S _, 0)        => None
  | (0, S hi')      => 
    match l with
    | nil     => None
    | x :: xs => option_map (fun t => x :: t) (list_slice xs 0 hi')
    end
  | (S lo', S hi')  => 
    match l with
    | nil      => None
    | x :: xs => option_map (fun t => x :: t) (list_slice xs lo' hi')
    end
  end.

Definition mapEnv (f : environment -> environment) : env_monad unit :=
  fun env => mret tt (f env).

Definition defaultValue (A: type) : value.
Admitted.

Definition evalLvalue (expr: expression) : env_monad lvalue.
Admitted.

Definition powTwo (w: nat) : N.
Admitted.

Definition of_bvector {w} (bits: Bvector w) : N.
Admitted.

Definition evalMinus (v: value) : option value := 
  match v with
  | ValBit width bits => Some (ValFixedInt width (N.to_nat (N.sub (powTwo width) (of_bvector bits))))
  | ValFixedInt width value => Some (ValFixedInt width (N.to_nat (N.sub (powTwo width) (N.of_nat value))))
  | ValSignedInt n => Some (ValSignedInt (Decimal.opp n))
  | _ => None
  end.

Fixpoint evalExpression (expr: expression) : env_monad value :=
  match expr with
  | BoolExpression value => mret (ValBool value)
  | IntExpression value => mret (ValInt value)
  | StringExpression value => mret (ValString value)
  | ArrayAccess array index =>
    let* index' := evalExpression index in
    let* array' := evalExpression array in
    match (array', index') with
    | (ValArray array'', ValInt index'') => lift_option (List.nth_error array'' index'')
    | _ => state_fail Internal
    end
  | BitStringAccess array hi lo =>
    let* array' := evalExpression array in
    let* hi'    := evalExpression hi in
    let* lo'    := evalExpression lo in
    match (array', hi', lo') with
    | (ValArray array'', ValInt hi'', ValInt lo'') => lift_option (option_map ValArray (list_slice array'' lo'' hi''))
    | _ => state_fail Internal
    end
  | List exprs => liftM ValArray (sequence (List.map evalExpression exprs))
  | Record entries => 
    let actions := List.map (fun x => match x with | MkKeyValue k e => v <- evalExpression e ;; mret (k, v) end) entries in
    liftM ValRecord (sequence actions)
  | UnaryOp op arg => 
    let* inner := evalExpression arg in
    match op with
    | Not => 
      match inner with
      | ValBool b => mret (ValBool (negb b))
      | _ => state_fail Internal
      end
    | BitNot => 
      match inner with
      | ValBit w bits => mret (ValBit w (Bneg w bits))
      | _ => state_fail Internal
      end
    | BitMinus => lift_option (evalMinus inner)
    end
  | _ => mret (ValBool false) (* TODO *)
  end.

Definition evalIsValid (obj: lvalue) : env_monad value :=
  let* result := findLvalue obj
  in match result with
  | ValHeader (MkHeader valid fields) => mret (ValBool valid)
  | _ => state_fail Internal
  end.

Definition evalSetBool (obj: lvalue) (valid: bool) : env_monad unit :=
  let* value := findLvalue obj in
  match value with
  | ValHeader (MkHeader _ fields) =>
    updateLvalue obj (ValHeader (MkHeader valid fields))
  | _ => state_fail Internal
  end.

Definition evalPopFront (obj: lvalue) (args: list (option value)) : env_monad unit :=
  match args with
  | Some (ValInt count) :: nil => 
      let* value := findLvalue obj in
      match value with
      | ValHeaderStack size nextIndex elements =>
        match rotateLeft elements count (MkHeader false (MStr.Raw.empty _)) with
        | None => state_fail Internal
        | Some elements' =>
          let value' := ValHeaderStack size (nextIndex - count) elements' in
          updateLvalue obj value
        end
      | _ => state_fail Internal
      end
  | _ => state_fail Internal
  end.

Definition evalPushFront (obj: lvalue) (args: list (option value)) : env_monad unit :=
  match args with
  | Some (ValInt count) :: nil => 
      let* value := findLvalue obj in
      match value with
      | ValHeaderStack size nextIndex elements =>
        match rotateRight elements count (MkHeader false (MStr.Raw.empty _)) with
        | None => state_fail Internal
        | Some elements' =>
          let nextIndex' := min size (nextIndex + count) in
          let value' := ValHeaderStack size nextIndex' elements' in
          updateLvalue obj value
        end
      | _ => state_fail Internal
      end
  | _ => state_fail Internal
  end.

Definition evalBuiltinFunc (name: string) (obj: lvalue) (args: list (option value)) : env_monad value :=
  match name with
  | "isValid" => evalIsValid obj
  | "setValid" => dummyValue (evalSetBool obj true)
  | "setInvalid" => dummyValue (evalSetBool obj false)
  | "pop_front" => dummyValue (evalPopFront obj args)
  | "push_front" => dummyValue (evalPushFront obj args)
  | _ => state_fail Internal
  end.

Fixpoint evalArguments (args: list (option expression)) : env_monad (list (option value)) :=
  match args with
  | nil => mret nil
  | Some arg :: args' =>
    let* val := evalExpression arg in
    let* vals := evalArguments args' in
    mret (Some val :: vals)
  | None :: args' =>
    let* vals := evalArguments args' in
    mret (None :: vals)
  end.

Fixpoint evalBlock (blk: block) : env_monad unit :=
  match blk with
  | BlockCons stmt rest =>
    evalStatement stmt;;
    evalBlock rest
  | BlockEmpty => mret tt
  end

with evalStatement (stmt: statement) : env_monad unit :=
  match stmt with
  | MethodCall func type_args args =>
    let* func' := evalExpression func in
    let* args' := evalArguments args in
    match func' with
    | ValBuiltinFunc name obj => tossValue (evalBuiltinFunc name obj args')
    | _ => mret tt (* TODO: other function types *)
    end
  | Assignment lhs rhs =>
    let* lval := evalLvalue lhs in
    let* val := evalExpression rhs in
    updateLvalue lval val
  | BlockStatement block =>
    mapEnv pushScope;;
    evalBlock block;;
    liftEnvFn popScope
  | StatementConstant type name init =>
    let* value := evalExpression init in
    insertEnvironment name value
  | StatementVariable type name init =>
    let* value :=
       match init with
       | None => mret (defaultValue type)
       | Some expr => evalExpression expr
       end
    in
    insertEnvironment name value
  end.
