Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bvector.

Require Import Info.
Require Import Typed.

Section Syntax.

  Context (tags_t: Type).

  Inductive P4String :=
  | MkP4String (tags: tags_t) (s: string).

  Inductive P4Int :=
  | MkP4Int (tags: tags_t) (value: Z) (width_signed: option (nat * bool)).

  Inductive MethodPrototype :=
  | ProtoConstructor (tags: tags_t) (name: P4String)
                     (params: list P4Parameter)
  | ProtoAbstractMethod (tags: tags_t) (ret: P4Type)
                        (name: P4String)(type_params: list P4String)
                        (params: list P4Parameter)
  | ProtoMethod (tags: tags_t) (ret: P4Type)
                (name: P4String) (type_params: list P4String)
                (params: list P4Parameter).

  Inductive OpUni : Type :=
  | Not
  | BitNot
  | UMinus.

  Inductive OpBin : Type :=
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
  | Or.

  Inductive KeyValue :=
  | MkKeyValue (tags: tags_t) (key: P4String) (value: Expression)
  with ExpressionPreT :=
  | ExpBool (b: bool)
  | ExpInt (_: P4Int)
  | ExpString (_: P4String)
  | ExpName (_: Typed.name)
  | ExpArrayAccess (array: Expression) (index: Expression)
  | ExpBitStringAccess (bits: Expression) (lo: Expression) (hi: Expression)
  | ExpList (value: list Expression)
  | ExpRecord (entries: list KeyValue)
  | ExpUnaryOp (op: OpUni) (arg: Expression)
  | ExpBinaryOp (op: OpBin) (args: (Expression * Expression))
  | ExpCast (typ: P4Type) (expr: Expression)
  | ExpTypeMember (typ: Typed.name) (name: P4String)
  | ExpErrorMember (_: P4String)
  | ExpExpressionMember (expr: Expression) (name: P4String)
  | ExpTernary (cond: Expression) (tru: Expression) (fls: Expression)
  | ExpFunctionCall (func: Expression) (type_args: list P4Type)
                    (args: list (option Expression))
  | ExpNamelessInstantiation (typ: P4Type) (args: list Expression)
  | ExpDontCare
  | ExpMask (expr: Expression) (mask: Expression)
  | ExpRange (lo: Expression) (hi: Expression)
  with Expression :=
  | MkExpression (tags: tags_t) (expr: ExpressionPreT) (typ: P4Type) (dir: direction).

  Inductive MatchPreT :=
  | MatchDontCare
  | MatchExpression (expr: Expression).
  Inductive Match :=
  | MkMatch (tags: tags_t) (expr: MatchPreT) (typ: P4Type).

  Inductive TablePreActionRef :=
  | MkTablePreActionRef (name: Typed.name)
                        (args: list (option Expression)).
  Inductive TableActionRef :=
  | MkTableActionRef (tags: tags_t) (action: TablePreActionRef)
                     (typ: Typed.P4Type).

  Inductive TableKey :=
  | MkTableKey (tags: tags_t)  (key: list Expression)
               (match_kind: P4String).

  Inductive TableEntry :=
  | MkTableEntry (tags: tags_t)  (matches: list Match)
                 (action: TableActionRef).

  Inductive TableProperty :=
  | MkTableProperty (tags: tags_t)  (const: bool)
                    (name: P4String) (value: Expression).

  Inductive StatementSwitchLabel :=
  | StatSwLabDefault (tags: tags_t)
  | StatSwLabName (tags: tags_t) (_: P4String).

  Inductive DeclarationField :=
  | MkDeclarationField (tags: tags_t)  (typ: P4Type)
                       (name: P4String).

  Definition ValueLoc := string.

  Inductive ValueTable :=
  | MkValTable (name: string) (keys: list TableKey)
               (actions: list TableActionRef) (default_action: TableActionRef)
               (const_entries: list TableEntry).

  Definition Env_env binding := list (list (string * binding)).

  Inductive Env_EvalEnv :=
  | MkEnv_EvalEnv (vs: Env_env ValueLoc) (typ: Env_env P4Type) (namespace: string).

  Inductive StatementSwitchCase :=
  | StatSwCaseAction (tags: tags_t) (label: StatementSwitchLabel) (code: Block)
  | StatSwCaseFallThrough (tags: tags_t) (label: StatementSwitchLabel)
  with StatementPreT :=
  | StatMethodCall (func: Expression) (type_args: list P4Type)
                   (args: list (option Expression))
  | StatAssignment (lhs: Expression) (rhs: Expression)
  | StatDirectApplication (typ: P4Type) (args: list Expression)
  | StatConditional (cond: Expression) (tru: Statement) (fls: option Statement)
  | StatBlock (block: Block)
  | StatExit
  | StatEmpty
  | StatReturn (expr: option Expression)
  | StatSwitch (expr: Expression) (cases: list StatementSwitchCase)
  | StatConstant  (typ: P4Type)
                 (name: P4String) (value: Value)
  | StatVariable  (typ: P4Type)
                 (name: P4String) (init: option Expression)
  | StatInstantiation  (typ: P4Type)
                      (args: list Expression) (name: P4String) (init: option Block)
  with Statement :=
  | MkStatement (tags: tags_t) (stmt: StatementPreT) (typ: StmType)
  with Block :=
  | BlockEmpty (tags: tags_t) 
  | BlockCons (statement: Statement) (rest: Block)
  with ParserCase :=
  | MkParserCase (tags: tags_t) (matches: list Match) (next: P4String)
  with ParserTransition :=
  | ParserDirect (tags: tags_t) (next: P4String)
  | ParserSelect (tags: tags_t) (exprs: list Expression) (cases: list ParserCase)
  with ParserState :=
  | MkParserState (tags: tags_t)  (name: P4String)
                  (statements: list Statement) (transition: ParserTransition)
  with Declaration :=
  | DeclConstant (tags: tags_t)  (typ: P4Type)
                 (name: P4String) (value: Value)
  | DeclInstantiation (tags: tags_t)  (typ: P4Type)
                      (args: list Expression) (name: P4String) (init: option Block)
  | DeclParser (tags: tags_t)  (name: P4String)
               (type_params: list P4String) (params: list P4Parameter)
               (constructor_params: list P4Parameter)
               (locals: list Declaration) (states: list ParserState)

  | DeclControl (tags: tags_t)  (name: P4String)
                (type_params: list P4String) (params: list P4Parameter)
                (constructor_params: list P4Parameter) (locals: list Declaration)
                (apply: Block)
  | DeclFunction (tags: tags_t) (ret: P4Type) (name: P4String)
                 (type_params: list P4String) (params: list P4Parameter) (body: Block)
  | DeclExternFunction (tags: tags_t)  (ret: P4Type)
                       (name: P4String) (type_params: list P4String)
                       (params: list P4Parameter)
  | DeclVariable (tags: tags_t)  (typ: P4Type)
                 (name: P4String) (init: option Expression)
  | DeclValueSet (tags: tags_t)  (typ: P4Type)
                 (size: Expression) (name: P4String)
  | DeclAction (tags: tags_t)  (name: P4String)
               (data_params: list P4Parameter) (ctrl_params: list P4Parameter)
               (body: Block)
  | DeclTable (tags: tags_t)  (name: P4String)
              (key: list TableKey) (actions: list TableActionRef)
              (entries: option (list TableEntry))
              (default_action: option TableActionRef) (size: option P4Int)
              (custom_properties: list TableProperty)
  | DeclHeader (tags: tags_t)  (name: P4String)
               (fields: list DeclarationField)
  | DeclHeaderUnion (tags: tags_t)  (name: P4String)
                    (fields: list DeclarationField)
  | DeclStruct (tags: tags_t)  (name: P4String)
               (fields: list DeclarationField)
  | DeclError (tags: tags_t) (members: list P4String)
  | DeclMatchKind (tags: tags_t) (members: list P4String)
  | DeclEnum (tags: tags_t)  (name: P4String)
             (members: list P4String)
  | DeclSerializableEnum (tags: tags_t)  (typ: P4Type)
                         (name: P4String) (members: list (P4String * Expression))
  | DeclExternObject (tags: tags_t)  (name: P4String)
                     (type_params: list P4String) (methods: list MethodPrototype)
  | DeclTypeDef (tags: tags_t)  (name: P4String)
                (typ_or_decl: (P4Type + Declaration))
  | DeclNewType (tags: tags_t)  (name: P4String)
                (typ_or_decl: (P4Type + Declaration))
  | DeclControlType (tags: tags_t)  (name: P4String)
                    (type_params: list P4String) (params: list P4Parameter)
  | DeclParserType (tags: tags_t)  (name: P4String)
                   (type_params: list P4String) (params: list P4Parameter)
  | DeclPackageType (tags: tags_t)  (name: P4String)
                    (type_params: list P4String) (params: list P4Parameter)

  with Value :=
  | ValNull
  | ValBool (_: bool)
  | ValInteger (_: Z)
  | ValBit (width: nat) (value: Bvector width)
  | ValInt (width: nat) (value: Bvector width)
  | ValVarbit (max: nat) (width: nat) (value: Bvector width)
  | ValString (_: string)
  | ValTuple (_: list Value)
  | ValRecord (_: list (string * Value))
  | ValSet (_: ValueSet)
  | ValError (_: string)
  | ValMatchKind (_: string)
  | ValFun (scope: Env_EvalEnv) (params: list P4Parameter) (body: Block)
  | ValBuiltinFun (name: string) (caller: ValueLvalue)
  | ValAction (scope: Env_EvalEnv) (params: list P4Parameter) (body: Block)
  | ValStruct (fields: list (string * Value))
  | ValHeader (fields: list (string * Value)) (is_valid: bool)
  | ValUnion (fields: list (string * Value))
  | ValStack (headers: list Value) (size: nat) (next: nat)
  | ValEnumField (typ_name: string) (enum_name: string)
  | ValSenumField (typ_name: string) (enum_name: string) (value: Value)
  | ValSenum (_: list (string * Value))
  | ValRuntime (loc: ValueLoc) (obj_name: string)
  | ValParser (_: ValueParser)
  | ValControl (_: ValueControl)
  | ValPackage (params: list P4Parameter) (args: list (string * ValueLoc))
  | ValTable (_: ValueTable)
  | ValExternFun (name: string) (caller: option (ValueLoc * string))
                 (params: list P4Parameter)
  | ValExternObj (_: list (string * list P4Parameter))
  with ValueSet :=
  | ValSetSingleton (width: nat) (value: Z)
  | ValSetUniversal
  | ValSetMask (value: Value) (mask: Value)
  | ValSetRange (lo: Value) (hi: Value)
  | ValSetProd (_: list ValueSet)
  | ValSetLpm (width: Value) (nbits: nat) (value: Value)
  | ValSetValueSet (size: Value) (members: list (list Match))
                   (sets: list ValueSet)
  with ValuePreLvalue :=
  | ValLeftName (name: Typed.name)
  | ValLeftMember (expr: ValueLvalue) (name: string)
  | ValLeftBitAccess (expr: ValueLvalue) (msb: nat) (lsb: nat)
  | ValLeftArrayAccess (expr: ValueLvalue) (idx: nat)
  with ValueLvalue :=
  | MkValueLvalue (lvalue: ValuePreLvalue) (typ: P4Type)
  with ValueParser :=
  | MkValueParser (scope: Env_EvalEnv) (constructor_params: list P4Parameter)
                  (params: list P4Parameter) (locals: list Declaration)
                  (states: list ParserState)
  with ValueControl :=
  | MkValueControl (scope: Env_EvalEnv) (constructor_params: list P4Parameter)
                   (params: list P4Parameter) (locals: list Declaration)
                   (apply: Block).

  (* Molly: Value_pkt, Value_entries, Value_vset, Value_ctrl, Value_signal
          omitted*)

  Inductive Env_CheckerEnv :=
    MkEnv_CheckerEnv (typ: Env_env P4Type) (typ_of: Env_env (P4Type * direction))
                     (const: Env_env Value).

  Inductive program := Program (_: list Declaration).

End Syntax.
