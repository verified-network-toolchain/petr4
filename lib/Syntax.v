Require Import String.
Require Import  Coq.Lists.List.

Class Monad (M : Type -> Type) : Type :=
  { mret : forall {A}, A -> M A;
    mbind : forall {A B}, M A -> (A -> M B) -> M B
  }.

(* Adapted from coq-ext-lib *)
(* https://github.com/coq-community/coq-ext-lib/blob/v8.5/theories/Structures/Monad.v*)
Module MonadNotation.

  Delimit Scope monad_scope with monad.

  Notation "c >>= f" := (@mbind _ _ _ _ c f) (at level 50, left associativity) : monad_scope.
  Notation "f =<< c" := (@mbind _ _ _ _ c f) (at level 51, right associativity) : monad_scope.

  Notation "x <- c1 ;; c2" := (@mbind _ _ _ _ c1 (fun x => c2))
    (at level 100, c1 at next level, right associativity) : monad_scope.

  Notation "e1 ;; e2" := (_ <- e1%monad ;; e2%monad)%monad
    (at level 100, right associativity) : monad_scope.

  Notation "'let*' x ':=' c1 'in' c2" := (@mbind _ _ _ _ c1 (fun x => c2))
    (at level 61, c1 at next level, right associativity) : monad_scope.

End MonadNotation.
Import MonadNotation.

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
  | BoolExpression (b : bool)
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

with value :=

with lvalue :=
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

Inductive environment :=.

Definition updateEnvironment : string -> value -> environment -> option environment.
Admitted.

Definition updateLvalue : lvalue -> value -> environment -> option environment.
Admitted.

Definition insertEnvironment : string -> value -> environment -> option environment.
Admitted.

Definition pushScope : environment -> environment.
Admitted.

Definition popScope : environment -> environment.
Admitted.

Inductive exception :=
| Reject
| Exit
| Internal.

Definition interp_monad (A: Type) :=
  environment -> (A + exception) * environment.

Definition interp_return (A: Type) (a: A) : interp_monad A :=
  fun env => (inl a, env).

Definition interp_fail {A: Type} (exn: exception) : interp_monad A :=
  fun env => (inr exn, env).

Definition interp_bind (A B: Type) (c: interp_monad A) (f: A -> interp_monad B) : interp_monad B :=
  fun env =>
    let (res, env') := c env in
    match res with
    | inl a => f a env'
    | inr exn => (inr exn, env')
    end.

Global Instance interp_monad_inst : Monad interp_monad :=
  { mret := interp_return;
    mbind := interp_bind
  }.

Definition liftEnvFn (f : environment -> option environment) : interp_monad unit :=
  fun env =>
    match f env with
    | Some env' => mret tt env'
    | None => interp_fail Internal env
    end.

Definition mapEnv (f : environment -> environment) : interp_monad unit :=
  fun env => mret tt (f env).

Definition defaultValue (A: type) : value.
Admitted.

Definition evalLvalue (expr: expression) : interp_monad lvalue.
Admitted.

Definition evalExpression (expr: expression) : interp_monad value.
Admitted.

Open Scope monad.

Fixpoint evalBlock (blk: block) : interp_monad unit :=
  match blk with
  | BlockCons stmt rest =>
    evalStatement stmt;;
    evalBlock rest
  | BlockEmpty => mret tt
  end

with evalStatement (stmt: statement) : interp_monad unit :=
  match stmt with
  | MethodCall func type_args args =>
    (* TODO *)
    mret tt
  | Assignment lhs rhs =>
    let* lval := evalLvalue lhs in
    let* val := evalExpression rhs in
    liftEnvFn (updateLvalue lval val)
  | BlockStatement block =>
    mapEnv pushScope;;
    evalBlock block;;
    mapEnv popScope
  | StatementConstant type name init =>
    let* value := evalExpression init in
    liftEnvFn (insertEnvironment name value)
  | StatementVariable type name init =>
    let* value :=
       match init with
       | None => mret (defaultValue type)
       | Some expr => evalExpression expr
       end
    in
    liftEnvFn (insertEnvironment name value)
  end
.
