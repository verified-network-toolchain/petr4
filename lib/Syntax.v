Require Import String.
Require Import  Coq.Lists.List.
Require Import Coq.FSets.FMapList.
Require Import Coq.Structures.OrderedTypeEx.

Module Import MStr := FMapList.Make(String_as_OT).

Class Monad (M : Type -> Type) : Type :=
  { mret : forall {A}, A -> M A;
    mbind : forall {A B}, M A -> (A -> M B) -> M B
  }.

(* Adapted from coq-ext-lib *)
(* https://github.com/coq-community/coq-ext-lib/blob/v8.5/theories/Structures/Monad.v*)
Module MonadNotation.

  Declare Scope monad_scope.
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
Open Scope monad.

Definition option_ret (A: Type) (a: A) := Some a.
Definition option_bind (A B: Type) (c: option A) (f: A -> option B) : option B :=
  match c with
  | Some a => f a
  | None => None
  end.

Global Instance option_monad_inst : Monad option :=
  { mret := option_ret;
    mbind := option_bind;
  }.

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

Inductive value :=
  | ValBool (b: bool)
  | ValInt (n: nat)
  | ValString (s: string)
  | ValArray (arr: list value)
  (* I would rather this was MStr.t value but that is not a strictly
  positive definition. The difference is that [Raw.t value] is
  basically list (string * value) while MStr.t value is a dependent
  record { raw: MStr.Raw.t; sorted: Sorted ...} which includes a proof
  that the list [raw] is sorted. *)
  | ValRecord (fs: MStr.Raw.t value)
.

Inductive lvalue :=
  | LValName (var: string)
  | LValMember (base: lvalue) (member: string)
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

Definition scope := MStr.t value.
Definition environment := list scope.

Definition updateScope (key: string) (val: value) (bindings: scope) : option scope :=
  MStr.find key bindings;;
  mret (MStr.add key val (MStr.remove key bindings)).

Definition insertScope (key: string) (val: value) (bindings: scope) : option scope :=
  MStr.find key bindings;;
  mret (MStr.add key val bindings).

Fixpoint updateEnvironment (key: string) (val: value) (env: environment) : option environment :=
  match env with
  | inner :: rest =>
    if MStr.find key inner
    then let* inner' := updateScope key val inner in
         mret (inner' :: rest)
    else let* rest' := updateEnvironment key val rest in
         mret (inner :: rest')
  | nil => None
  end.

Fixpoint insertEnvironment (key: string) (val: value) (env: environment) : option environment :=
  match env with
  | inner :: rest =>
    let* inner' := insertScope key val inner in
    mret (inner' :: rest)
  | nil => None
  end.

Definition findScope (key: string) (bindings: scope) : option value :=
  MStr.find key bindings.
  
Fixpoint findEnvironment (key: string) (env: environment) : option value :=
  match env with
  | inner :: rest =>
    match MStr.find key inner with
    | Some v => Some v
    | None => findEnvironment key rest
    end
  | nil => None
  end.

Definition pushScope (env: environment) :=
  MStr.empty _ :: env.

Definition popScope (env: environment) : option environment :=
  match env with
  | _ :: rest => Some rest
  | nil => None
  end.

Fixpoint findLvalue (lval: lvalue) (env: environment) : option value :=
  match lval with
  | LValName var =>
    findEnvironment var env
  | LValMember lval' member =>
    let* val := findLvalue lval' env in
    match val with
    | ValRecord map =>
      Raw.find member map
    | _ => None
    end
  end.

Fixpoint assocUpdate {A: Type} (key: string) (val: A) (map: list (string * A)) : option (list (string * A)) :=
  match map with
  | (s, v) :: map' =>
    if String_as_OT.eq_dec s key
    then mret ((key, val) :: map')
    else let* map' := assocUpdate key val map' in
         mret ((s, v) :: map')
  | nil => None
  end.

Definition updateMember (obj: value) (member: string) (val: value) : option value :=
  match obj with
  | ValRecord map =>
    let* map' := assocUpdate member val map in
    mret (ValRecord map')
  | _ => None
  end.

Fixpoint updateLvalue (lval: lvalue) (val: value) (env: environment) : option environment :=
  match lval with
  | LValName var =>
    updateEnvironment var val env
  | LValMember lval' member =>
    let* obj := findLvalue lval' env in
    let* obj' := updateMember obj member val in
    updateLvalue lval' obj' env
  end.

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

Fixpoint evalExpression (expr: expression) : interp_monad value :=
  match expr with
  | BoolExpression value => mret (ValBool value)
  | IntExpression value => mret (ValInt value)
  | StringExpression value => mret(ValString value)
  | ArrayAccess array index =>
    let* index' := evalExpression index in
    let* array' := evalExpression array in
    match (array', index') with
    | (ValArray array'', ValInt index'') =>
      match List.nth_error array'' index'' with
      | Some v => mret v
      | None => interp_fail Reject
      end
    | _ => interp_fail Internal
    end
  | _ => mret (ValBool false)
  end
.

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
    liftEnvFn popScope
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
  end.
