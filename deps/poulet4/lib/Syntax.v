Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bvector.

(* Require Import Monads.Monad.
Require Import Monads.Option.
Require Import Monads.State. *)

Require Import Info.
Require Import Typed.

(* Open Scope monad. *)

Definition P4String := Types.P4String.
Definition P4Int := Types.P4Int.

Inductive MethodPrototype :=
  (* annotations, name, params *)
  | ProtoConstructor (info: Info) (annotations: list Annotation) (name: P4String)
                     (params: list P4Parameter)
  (* annotations, return, name, type_params, params *)
  | ProtoAbstractMethod (info: Info) (annotations: list Annotation) (ret: P4Type)
                        (name: P4String)(type_params: list P4String)
                        (params: list P4Parameter)
  (* annotations, return, name, type_params, params *)
  | ProtoMethod (info: Info) (annotations: list Annotation) (ret: P4Type)
                (name: P4String) (type_params: list P4String)
                (params: list P4Parameter).

Inductive KeyValue :=
  | MkKeyValue (info: Info) (key: P4String) (value: Expression)
with ExpressionPreT :=
  | ExpBool (b: bool)
  | ExpInt (_: P4Int)
  | ExpString (_: P4String)
  | ExpName (_: Types.name)
  (* array, index *)
  | ExpArrayAccess (array: Expression) (index: Expression)
  (* bits, lo [int] , hi [int] *)
  | ExpBitStringAccess (bits: Expression) (lo: Expression) (hi: Expression)
  | ExpList (value: list Expression)
  | ExpRecord (entries: list KeyValue)
  | ExpUnaryOp (op: Types.OpUni) (arg: Expression)
  | ExpBinaryOp (op: Types.OpBin) (args: (Expression * Expression))
  | ExpCast (typ: P4Type) (expr: Expression)
  | ExpTypeMember (typ: Types.name) (name: P4String)
  | ExpErrorMember (_: P4String)
  | ExpExpressionMember (expr: Expression) (name: P4String)
  (* cond, tru, fls *)
  | ExpTernary (cond: Expression) (tru: Expression) (fls: Expression)
  (* func, type_args, args *)
  | ExpFunctionCall (func: Expression) (type_args: list P4Type)
                     (args: list (option Expression))
  (* type, args *)
  | ExpNamelessInstantiation (typ: P4Type) (args: list Expression)
  | ExpDontCare
  (* expr, mask *)
  | ExpMask (expr: Expression) (mask: Expression)
  (* lo, hi *)
  | ExpRange (lo: Expression) (hi: Expression)
with Expression :=
  (* expr, typ, dir*)
  | MkExpression (info: Info) (expr: ExpressionPreT) (typ: P4Type) (dir: direction).

Inductive MatchPreT :=
  | MatchDontCare
  | MatchExpression (expr: Expression).
Inductive Match :=
  | MkMatch (info: Info) (expr: MatchPreT) (typ: P4Type).

Inductive TablePreActionRef :=
  (* annotations, name, args *)
  | MkTablePreActionRef (annotations: list Annotation) (name: Types.name)
                        (args: list (option Expression)).
Inductive TableActionRef :=
  (* action, type *)
  | MkTableActionRef (info: Info) (action: TablePreActionRef)
                     (typ: Typed.P4Type).


Inductive TableKey :=
  (* annotations, key, match_kind *)
  | MkTableKey (info: Info) (annotations: list Annotation) (key: list Expression)
               (match_kind: P4String).

Inductive TableEntry :=
  (* annotations, matches, action *)
  | MkTableEntry (info: Info) (annotations: list Annotation) (matches: list Match)
                 (action: TableActionRef).

Inductive TableProperty :=
  (* annotations, const, name, value *)
  | MkTableProperty (info: Info) (annotations: list Annotation) (const: bool)
                    (name: P4String) (value: Expression).

Inductive StatementSwitchLabel :=
  | StatSwLabDefault (info: Info)
  | StatSwLabName (info: Info) (_: P4String).

Inductive DeclarationField :=
| MkDeclarationField (info: Info) (annotations: list Annotation) (typ: P4Type)
                     (name: P4String).

Definition ValueLoc := string.

Inductive ValueTable :=
  (* name, keys, actions, default_action, const_entries *)
| MkValTable (name: string) (keys: list TableKey)
             (actions: list TableActionRef) (default_action: TableActionRef)
             (const_entries: list TableEntry).

Definition Env_env binding := list (list (string * binding)).

Inductive Env_EvalEnv :=
  | MkEnv_EvalEnv (vs: Env_env ValueLoc) (typ: Env_env P4Type) (namespace: string).

Inductive StatementSwitchCase :=
  (* label, code *)
  | StatSwCaseAction (info: Info) (label: StatementSwitchLabel) (code: Block)
  (* label *)
  | StatSwCaseFallThrough (info: Info) (label: StatementSwitchLabel)
with StatementPreT :=
  (* func, type_args, args *)
  | StatMethodCall (func: Expression) (type_args: list P4Type)
                    (args: list (option Expression))
  (* lhs, rhs *)
  | StatAssignment (lhs: Expression) (rhs: Expression)
  (* typ, args *)
  | StatDirectApplication (typ: P4Type) (args: list Expression)
  (* cond, tru, fls *)
  | StatConditional (cond: Expression) (tru: Statement) (fls: option Statement)
  | StatBlock (block: Block)
  | StatExit
  | StatEmpty
  | StatReturn (expr: option Expression)
  (* expr, cases *)
  | StatSwitch (expr: Expression) (cases: list StatementSwitchCase)
  | StatConstant (annotations: list Annotation) (typ: P4Type)
                 (name: P4String) (value: Value)
  | StatVariable (annotations: list Annotation) (typ: P4Type)
                 (name: P4String) (init: option Expression)
  | StatInstantiation (annotations: list Annotation) (typ: P4Type)
                      (args: list Expression) (name: P4String) (init: option Block)
with Statement :=
  | MkStatement (info: Info) (stmt: StatementPreT) (typ: StmType)
with Block :=
  | BlockEmpty (info: Info) (annotations: list Annotation)
  | BlockCons (statement: Statement) (rest: Block)
with ParserCase :=
  (* matches, next *)
  | MkParserCase (info: Info) (matches: list Match) (next: P4String)
with ParserTransition :=
  (* next *)
  | ParserDirect (info: Info) (next: P4String)
  (* exprs, cases *)
  | ParserSelect (info: Info) (exprs: list Expression) (cases: list ParserCase)
with ParserState :=
  (* annotations, name, statements, transition *)
  | MkParserState (info: Info) (annotations: list Annotation) (name: P4String)
                   (statements: list Statement) (transition: ParserTransition)
with Declaration :=
  (* annotations, typ, name, value *)
  | DeclConstant (info: Info) (annotations: list Annotation) (typ: P4Type)
                  (name: P4String) (value: Value)
  (* annotations, typ, args, name, init *)
  | DeclInstantiation (info: Info) (annotations: list Annotation) (typ: P4Type)
                       (args: list Expression) (name: P4String) (init: option Block)
  (* annotations, name, typ_params, params, constructor_params, locals,
     states *)
  | DeclParser (info: Info) (annotations: list Annotation) (name: P4String)
                (type_params: list P4String) (params: list P4Parameter)
                (constructor_params: list P4Parameter)
                (locals: list Declaration) (states: list ParserState)

  (* annotations, name, typ_params, params, constructor_params, locals,
     apply *)
  | DeclControl (info: Info) (annotations: list Annotation) (name: P4String)
                 (type_params: list P4String) (params: list P4Parameter)
                 (constructor_params: list P4Parameter) (locals: list Declaration)
                 (apply: Block)
  (* return, name, typ_params, params, body *)
  | DeclFunction (info: Info) (ret: P4Type) (name: P4String)
                  (type_params: list P4String) (params: list P4Parameter) (body: Block)
  (* annotations, return, name, typ_params, params *)
  | DeclExternFunction (info: Info) (annotations: list Annotation) (ret: P4Type)
                        (name: P4String) (type_params: list P4String)
                        (params: list P4Parameter)
  (* annotations, typ, name, init *)
  | DeclVariable (info: Info) (annotations: list Annotation) (typ: P4Type)
                  (name: P4String) (init: option Expression)
  (* annotations, typ, size, name *)
  | DeclValueSet (info: Info) (annotations: list Annotation) (typ: P4Type)
                  (size: Expression) (name: P4String)
  (* annotations, name, data_params, ctrl_params, body *)
  | DeclAction (info: Info) (annotations: list Annotation) (name: P4String)
                (data_params: list P4Parameter) (ctrl_params: list P4Parameter)
                (body: Block)
  (* annotations, name, key, actions, entries, default_action, size,
     custom_properties *)
  | DeclTable (info: Info) (annotations: list Annotation) (name: P4String)
               (key: list TableKey) (actions: list TableActionRef)
               (entries: option (list TableEntry))
               (default_action: option TableActionRef) (size: option P4Int)
               (custom_properties: list TableProperty)
  (* annotations, name, fields *)
  | DeclHeader (info: Info) (annotations: list Annotation) (name: P4String)
                (fields: list DeclarationField)
  (* annotations, name, fields *)
  | DeclHeaderUnion (info: Info) (annotations: list Annotation) (name: P4String)
                     (fields: list DeclarationField)
  (* annotations, name, fields *)
  | DeclStruct (info: Info) (annotations: list Annotation) (name: P4String)
                (fields: list DeclarationField)
  | DeclError (info: Info) (members: list P4String)
  (* members *)
  | DeclMatchKind (info: Info) (members: list P4String)
  (* annotations, name, members *)
  | DeclEnum (info: Info) (annotations: list Annotation) (name: P4String)
              (members: list P4String)
  (* annotations, typ, name, members *)
  | DeclSerializableEnum (info: Info) (annotations: list Annotation) (typ: P4Type)
                          (name: P4String) (members: list (P4String * Expression))
  (* annotations, name, typ_params, methods *)
  | DeclExternObject (info: Info) (annotations: list Annotation) (name: P4String)
                      (type_params: list P4String) (methods: list MethodPrototype)
  (* annotations, name, typ_or_decl *)
  | DeclTypeDef (info: Info) (annotations: list Annotation) (name: P4String)
                 (typ_or_decl: (P4Type + Declaration))
  (* annotations, name, typ_or_decl *)
  | DeclNewType (info: Info) (annotations: list Annotation) (name: P4String)
                 (typ_or_decl: (P4Type + Declaration))
  (* annotations, name, typ_params, params *)
  | DeclControlType (info: Info) (annotations: list Annotation) (name: P4String)
                     (type_params: list P4String) (params: list P4Parameter)
  (* annotations, name, typ_params, params *)
  | DeclParserType (info: Info) (annotations: list Annotation) (name: P4String)
                    (type_params: list P4String) (params: list P4Parameter)
  (* annotations, name, typ_params, params *)
  | DeclPackageType (info: Info) (annotations: list Annotation) (name: P4String)
                     (type_params: list P4String) (params: list P4Parameter)
with Value :=
  | ValNull
  | ValBool (_: bool)
  | ValInteger (_: Z)
  (* widh, value *)
  | ValBit (width: nat) (value: Bvector width)
  (* width, value *)
  | ValInt (width: nat) (value: Bvector width)
  (* max, width, value *)
  | ValVarbit (max: nat) (width: nat) (value: Bvector width)
  | ValString (_: string)
  | ValTuple (_: list Value)
  | ValRecord (_: list (string * Value))
  | ValSet (_: ValueSet)
  | ValError (_: string)
  | ValMatchKind (_: string)
  (* scope, params, body *)
  | ValFun (scope: Env_EvalEnv) (params: list P4Parameter) (body: Block)
  (* name, caller *)
  | ValBuiltinFun (name: string) (caller: ValueLvalue)
  (* scope, params, body *)
  | ValAction (scope: Env_EvalEnv) (params: list P4Parameter) (body: Block)
  | ValStruct (fields: list (string * Value))
  (* fields, is_valid *)
  | ValHeader (fields: list (string * Value)) (is_valid: bool)
  | ValUnion (fields: list (string * Value))
  (* headers, size, next *)
  | ValStack (headers: list Value) (size: nat) (next: nat)
  (* typ_name, enum_name *)
  | ValEnumField (typ_name: string) (enum_name: string)
  (* typ_name, enum_name, value *)
  | ValSenumField (typ_name: string) (enum_name: string) (value: Value)
  | ValSenum (_: list (string * Value))
  (* loc, obj_name *)
  | ValRuntime (loc: ValueLoc) (obj_name: string)
  | ValParser (_: ValueParser)
  | ValControl (_: ValueControl)
  (* params, args *)
  | ValPackage (params: list P4Parameter) (args: list (string * ValueLoc))
  | ValTable (_: ValueTable)
  (* name, caller, params*)
  | ValExternFun (name: string) (caller: option (ValueLoc * string))
                   (params: list P4Parameter)
  | ValExternObj (_: list (string * list P4Parameter))
with ValueSet :=
  (* width, value *)
  | ValSetSingleton (width: nat) (value: Z)
  | ValSetUniversal
  (* value, mask *)
  | ValSetMask (value: Value) (mask: Value)
  (* lo, hi *)
  | ValSetRange (lo: Value) (hi: Value)
  | ValSetProd (_: list ValueSet)
  (* width, nbits, value *)
  | ValSetLpm (width: Value) (nbits: nat) (value: Value)
  (* size, members, sets *)
  | ValSetValueSet (size: Value) (members: list (list Match))
                   (sets: list ValueSet)
with ValuePreLvalue :=
  | ValLeftName (name: Types.name)
  (* expr, name *)
  | ValLeftMember (expr: ValueLvalue) (name: string)
  (* expr, msb, lsb *)
  | ValLeftBitAccess (expr: ValueLvalue) (msb: nat) (lsb: nat)
  (* expr, idx *)
  | ValLeftArrayAccess (expr: ValueLvalue) (idx: nat)
with ValueLvalue :=
  | MkValueLvalue (lvalue: ValuePreLvalue) (typ: P4Type)
with ValueParser :=
  (* scope, constructor_params, params, locals, states *)
  | MkValueParser (scope: Env_EvalEnv) (constructor_params: list P4Parameter)
                    (params: list P4Parameter) (locals: list Declaration)
                    (states: list ParserState)
with ValueControl :=
  (* scope, constructor_params, params, locals, apply *)
  | MkValueControl (scope: Env_EvalEnv) (constructor_params: list P4Parameter)
                     (params: list P4Parameter) (locals: list Declaration)
                     (apply: Block).

(* Molly: Value_pkt, Value_entries, Value_vset, Value_ctrl, Value_signal
          omitted*)

Inductive Env_CheckerEnv :=
  MkEnv_CheckerEnv (typ: Env_env P4Type) (typ_of: Env_env (P4Type * direction))
                   (const: Env_env Value).

Inductive program := Program (_: list Declaration).

