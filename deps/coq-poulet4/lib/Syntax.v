Require Import Coq.Lists.List.
Require Import Coq.Numbers.BinNums.

Require Import Petr4.Info.
Require Import Petr4.Typed.
Require Petr4.String.
Require Petr4.P4String.
Require Petr4.P4Int.
Require Import Petr4.Utils.

Section Syntax.

  Context {tags_t: Type}.
  Notation P4String := (P4String.t tags_t).
  Notation P4Int := (P4Int.t tags_t).

  Inductive MethodPrototype :=
  | ProtoConstructor (tags: tags_t) (name: P4String)
                     (params: list (@P4Parameter tags_t))
  | ProtoAbstractMethod (tags: tags_t) (ret: @P4Type tags_t)
                        (name: P4String) (type_params: list P4String)
                        (params: list (@P4Parameter tags_t))
  | ProtoMethod (tags: tags_t) (ret: @P4Type tags_t)
                (name: P4String) (type_params: list P4String)
                (params: list (@P4Parameter tags_t)).

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
  | ExpName (_: @Typed.name tags_t)
  | ExpArrayAccess (array: Expression) (index: Expression)
  | ExpBitStringAccess (bits: Expression) (lo: N) (hi: N)
  | ExpList (value: list Expression)
  | ExpRecord (entries: list KeyValue)
  | ExpUnaryOp (op: OpUni) (arg: Expression)
  | ExpBinaryOp (op: OpBin) (args: (Expression * Expression))
  | ExpCast (typ: @P4Type tags_t) (expr: Expression)
  | ExpTypeMember (typ: @Typed.name tags_t) (name: P4String)
  | ExpErrorMember (_: P4String)
  | ExpExpressionMember (expr: Expression) (name: P4String)
  | ExpTernary (cond: Expression) (tru: Expression) (fls: Expression)
  | ExpFunctionCall (func: Expression) (type_args: list (@P4Type tags_t))
                    (args: list (option Expression))
  | ExpNamelessInstantiation (typ: @P4Type tags_t) (args: list Expression)
  | ExpDontCare
  | ExpMask (expr: Expression) (mask: Expression)
  | ExpRange (lo: Expression) (hi: Expression)
  with Expression :=
  | MkExpression (tags: tags_t) (expr: ExpressionPreT) (typ: @P4Type tags_t) (dir: direction).

  Inductive MatchPreT :=
  | MatchDontCare
  | MatchExpression (expr: Expression).

  Inductive Match :=
  | MkMatch (tags: tags_t) (expr: MatchPreT) (typ: @P4Type tags_t).

  Inductive TablePreActionRef :=
  | MkTablePreActionRef (name: @Typed.name tags_t)
                        (args: list (option Expression)).

  Inductive TableActionRef :=
  | MkTableActionRef (tags: tags_t) (action: TablePreActionRef)
                     (typ: @Typed.P4Type tags_t).

  Inductive TableKey :=
  | MkTableKey (tags: tags_t)  (key: Expression)
               (match_kind: P4String).

  Inductive TableEntry :=
  | MkTableEntry (tags: tags_t)  (matches: list Match)
                 (action: TableActionRef).

  Inductive TableProperty :=
  | MkTableProperty (tags: tags_t)  (const: bool)
                    (name: P4String) (value: Expression).

  Inductive ValueBase :=
  | ValBaseNull
  | ValBaseBool (_: bool)
  | ValBaseInteger (_: Z)
  | ValBaseBit (width: nat) (value: Z)
  | ValBaseInt (width: nat) (value: Z)
  | ValBaseVarbit (max: nat) (width: nat) (value: Z)
  | ValBaseString (_: P4String)
  | ValBaseTuple (_: list ValueBase)
  | ValBaseRecord (_: list (P4String * ValueBase))
  | ValBaseSet (_: ValueSet)
  | ValBaseError (_: P4String)
  | ValBaseMatchKind (_: P4String)
  | ValBaseStruct (fields: list (P4String * ValueBase))
  | ValBaseHeader (fields: list (P4String * ValueBase)) (is_valid: bool)
  | ValBaseUnion (fields: list (P4String * ValueBase))
  | ValBaseStack (headers: list ValueBase) (size: nat) (next: nat)
  | ValBaseEnumField (typ_name: P4String) (enum_name: P4String)
  | ValBaseSenumField (typ_name: P4String) (enum_name: P4String) (value: ValueBase)
  | ValBaseSenum (_: list (P4String * ValueBase))
  with ValueSet :=
  | ValSetSingleton (width: nat) (value: Z)
  | ValSetUniversal
  | ValSetMask (value: ValueBase) (mask: ValueBase)
  | ValSetRange (lo: ValueBase) (hi: ValueBase)
  | ValSetProd (_: list ValueSet)
  | ValSetLpm (width: ValueBase) (nbits: nat) (value: ValueBase)
  | ValSetValueSet (size: ValueBase) (members: list (list Match))
                   (sets: list ValueSet).

  Inductive StatementSwitchLabel :=
  | StatSwLabDefault (tags: tags_t)
  | StatSwLabName (tags: tags_t) (_: P4String).

  Inductive StatementSwitchCase :=
  | StatSwCaseAction (tags: tags_t)
                     (label: StatementSwitchLabel)
                     (code: Block)
  | StatSwCaseFallThrough (tags: tags_t)
                          (label: StatementSwitchLabel)
  with StatementPreT :=
  | StatMethodCall (func: Expression)
                   (type_args: list (@P4Type tags_t))
                   (args: list (option Expression))
  | StatAssignment (lhs: Expression)
                   (rhs: Expression)
  | StatDirectApplication (typ: @P4Type tags_t)
                          (args: list Expression)
  | StatConditional (cond: Expression)
                    (tru: Statement)
                    (fls: option Statement)
  | StatBlock (block: Block)
  | StatExit
  | StatEmpty
  | StatReturn (expr: option Expression)
  | StatSwitch (expr: Expression)
               (cases: list StatementSwitchCase)
  | StatConstant  (typ: @P4Type tags_t)
                  (name: P4String) (value: ValueBase)
  | StatVariable  (typ: @P4Type tags_t)
                  (name: P4String) (init: option Expression)
  | StatInstantiation  (typ: @P4Type tags_t)
                       (args: list Expression)
                       (name: P4String)
                       (init: option Block)
  with Statement :=
  | MkStatement (tags: tags_t)
                (stmt: StatementPreT)
                (typ: StmType)
  with Block :=
  | BlockEmpty (tags: tags_t)
  | BlockCons (statement: Statement)
              (rest: Block).

  Section statement_rec.
    Context
      {PStatementSwitchCase: StatementSwitchCase -> Type}
      {PStatementSwitchCaseList: list StatementSwitchCase -> Type}
      {PStatementPreT: StatementPreT -> Type}
      {PStatement: Statement -> Type}
      {PStatementMaybe: option Statement -> Type}
      {PBlock: Block -> Type}
      {PBlockMaybe: option Block -> Type}
    .

    Hypotheses
      (HStatSwCaseAction: forall tags label code,
                          PBlock code ->
                          PStatementSwitchCase
                            (StatSwCaseAction tags label code))
      (HStatSwCaseFallThrough: forall tags label,
                               PStatementSwitchCase
                                (StatSwCaseFallThrough tags label))
      (HStatementSwitchCaseListNil: PStatementSwitchCaseList nil)
      (HStatementSwitchCaseListCons: forall s l,
                                     PStatementSwitchCase s ->
                                     PStatementSwitchCaseList l ->
                                     PStatementSwitchCaseList (s :: l))
      (HStatMethodCall: forall func type_args args,
                        PStatementPreT (StatMethodCall func type_args args))
      (HStatAssignment: forall lhs rhs,
                        PStatementPreT (StatAssignment lhs rhs))
      (HStatDirectApplication: forall typ args,
                               PStatementPreT
                                (StatDirectApplication typ args))
      (HStatConditional: forall cond tru fls,
                         PStatement tru ->
                         PStatementMaybe fls ->
                         PStatementPreT (StatConditional cond tru fls))
      (HStatBlock: forall block,
                   PBlock block ->
                   PStatementPreT (StatBlock block))
      (HStatExit: PStatementPreT StatExit)
      (HStatEmpty: PStatementPreT StatEmpty)
      (HStatReturn: forall expr, PStatementPreT (StatReturn expr))
      (HStatSwitch: forall expr cases,
                    PStatementSwitchCaseList cases ->
                    PStatementPreT (StatSwitch expr cases))
      (HStatConstant: forall typ name value,
                      PStatementPreT (StatConstant typ name value))
      (HStatVariable: forall typ name init,
                      PStatementPreT (StatVariable typ name init))
      (HStatInstantiation: forall typ args name init,
                           PBlockMaybe init ->
                           PStatementPreT
                            (StatInstantiation typ args name init))
      (HMkStatement: forall tags stmt typ,
                     PStatementPreT stmt ->
                     PStatement (MkStatement tags stmt typ))
      (HStatementMaybeNone: PStatementMaybe None)
      (HStatementMaybeSome: forall s,
                            PStatement s ->
                            PStatementMaybe (Some s))
      (HBlockEmpty: forall tags, PBlock (BlockEmpty tags))
      (HBlockCons: forall stmt rest,
                   PStatement stmt ->
                   PBlock rest ->
                   PBlock (BlockCons stmt rest))
      (HBlockMaybeNone: PBlockMaybe None)
      (HBlockMaybeSome: forall b, PBlock b -> PBlockMaybe (Some b))
    .

    Fixpoint statement_rec (s: Statement) : PStatement s :=
      match s with
      | MkStatement tags s' typ =>
        HMkStatement tags s' typ (statement_pre_t_rec s')
      end
    with statement_pre_t_rec (s: StatementPreT) : PStatementPreT s :=
      match s with
      | StatMethodCall func type_args args =>
        HStatMethodCall func type_args args
      | StatAssignment lhs rhs =>
        HStatAssignment lhs rhs
      | StatDirectApplication typ args =>
        HStatDirectApplication typ args
      | StatConditional cond tru fls =>
        HStatConditional cond tru fls
          (statement_rec tru)
          (option_rec (PStatement)
                      (PStatementMaybe)
                      (HStatementMaybeNone)
                      (HStatementMaybeSome)
                      (statement_rec)
                      fls)
      | StatBlock block =>
        HStatBlock block (block_rec block)
      | StatExit =>
        HStatExit
      | StatEmpty =>
        HStatEmpty
      | StatReturn expr =>
        HStatReturn expr
      | StatSwitch expr cases =>
        HStatSwitch expr cases
          (list_rec (PStatementSwitchCase)
                    (PStatementSwitchCaseList)
                    (HStatementSwitchCaseListNil)
                    (HStatementSwitchCaseListCons)
                    (statement_switch_case_rec)
                    cases)
      | StatConstant typ name value =>
        HStatConstant typ name value
      | StatVariable typ name init =>
        HStatVariable typ name init
      | StatInstantiation typ args name init =>
        HStatInstantiation typ args name init
          (option_rec (PBlock)
                      (PBlockMaybe)
                      (HBlockMaybeNone)
                      (HBlockMaybeSome)
                      (block_rec)
                      init)
      end
    with statement_switch_case_rec
      (s: StatementSwitchCase)
      : PStatementSwitchCase s
    :=
      match s with
      | StatSwCaseAction tags label code =>
        HStatSwCaseAction tags label code (block_rec code)
      | StatSwCaseFallThrough tags label =>
        HStatSwCaseFallThrough tags label
      end
    with block_rec (b: Block) : PBlock b :=
      match b with
      | BlockEmpty tags =>
        HBlockEmpty tags
      | BlockCons stmt rest =>
        HBlockCons stmt rest (statement_rec stmt) (block_rec rest)
      end
    .
  End statement_rec.

  Inductive ParserCase :=
  | MkParserCase (tags: tags_t) (matches: list Match) (next: P4String).

  Inductive ParserTransition :=
  | ParserDirect (tags: tags_t) (next: P4String)
  | ParserSelect (tags: tags_t) (exprs: list Expression) (cases: list ParserCase).

  Inductive ParserState :=
  | MkParserState (tags: tags_t)  (name: P4String)
                  (statements: list Statement) (transition: ParserTransition).

  Inductive DeclarationField :=
  | MkDeclarationField (tags: tags_t)  (typ: @P4Type tags_t)
                       (name: P4String).

  Inductive Declaration :=
  | DeclConstant (tags: tags_t)  (typ: @P4Type tags_t)
                 (name: P4String) (value: ValueBase)
  | DeclInstantiation (tags: tags_t)  (typ: @P4Type tags_t)
                      (args: list Expression) (name: P4String) (init: option Block)
  | DeclParser (tags: tags_t)  (name: P4String)
               (type_params: list P4String) (params: list (@P4Parameter tags_t))
               (constructor_params: list (@P4Parameter tags_t))
               (locals: list Declaration) (states: list ParserState)
  | DeclControl (tags: tags_t)  (name: P4String)
                (type_params: list P4String) (params: list (@P4Parameter tags_t))
                (constructor_params: list (@P4Parameter tags_t)) (locals: list Declaration)
                (apply: Block)
  | DeclFunction (tags: tags_t) (ret: @P4Type tags_t) (name: P4String)
                 (type_params: list P4String) (params: list (@P4Parameter tags_t)) (body: Block)
  | DeclExternFunction (tags: tags_t)  (ret: @P4Type tags_t)
                       (name: P4String) (type_params: list P4String)
                       (params: list (@P4Parameter tags_t))
  | DeclVariable (tags: tags_t)  (typ: @P4Type tags_t)
                 (name: P4String) (init: option Expression)
  | DeclValueSet (tags: tags_t)  (typ: @P4Type tags_t)
                 (size: Expression) (name: P4String)
  | DeclAction (tags: tags_t)  (name: P4String)
               (data_params: list (@P4Parameter tags_t)) (ctrl_params: list (@P4Parameter tags_t))
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
  | DeclSerializableEnum (tags: tags_t)  (typ: @P4Type tags_t)
                         (name: P4String) (members: list (P4String * Expression))
  | DeclExternObject (tags: tags_t)  (name: P4String)
                     (type_params: list P4String) (methods: list MethodPrototype)
  | DeclTypeDef (tags: tags_t)  (name: P4String)
                (typ_or_decl: (@P4Type tags_t + Declaration))
  | DeclNewType (tags: tags_t)  (name: P4String)
                (typ_or_decl: (@P4Type tags_t + Declaration))
  | DeclControlType (tags: tags_t)  (name: P4String)
                    (type_params: list P4String) (params: list (@P4Parameter tags_t))
  | DeclParserType (tags: tags_t)  (name: P4String)
                   (type_params: list P4String) (params: list (@P4Parameter tags_t))
  | DeclPackageType (tags: tags_t)  (name: P4String)
                    (type_params: list P4String) (params: list (@P4Parameter tags_t)).

  Definition ValueLoc := P4String.

  Inductive ValueTable :=
  | MkValTable (name: P4String) (keys: list TableKey)
               (actions: list TableActionRef) (default_action: TableActionRef)
               (const_entries: list TableEntry).

  Definition Env_env binding := list (list (P4String * binding)).

  Inductive Env_EvalEnv :=
  | MkEnv_EvalEnv (vs: Env_env ValueLoc) (typ: Env_env (@P4Type tags_t)) (namespace: P4String).

  Record ExternMethod :=
    { name: P4String;
      typ: @FunctionType tags_t }.

  Record ExternMethods :=
    { type_params: list P4String;
      methods: list ExternMethod }.

  Inductive ValuePreLvalue :=
  | ValLeftName (name: @Typed.name tags_t)
  | ValLeftMember (expr: ValueLvalue) (name: P4String)
  | ValLeftBitAccess (expr: ValueLvalue) (msb: nat) (lsb: nat)
  | ValLeftArrayAccess (expr: ValueLvalue) (idx: nat)
  with ValueLvalue :=
  | MkValueLvalue (lvalue: ValuePreLvalue) (typ: @P4Type tags_t).

  Inductive ValueFunctionImplementation :=
  | ValFuncImplUser (scope: Env_EvalEnv) (body: Block)
  | ValFuncImplExtern (name: P4String) (caller: option (ValueLoc * P4String))
  | ValFuncImplBuiltin (name: P4String) (caller: ValueLvalue).

  Inductive ValueObject :=
  | ValObjParser (scope: Env_EvalEnv)
                 (constructor_params: list (@P4Parameter tags_t))
                 (params: list (@P4Parameter tags_t)) (locals: list Declaration)
                 (states: list ParserState)
  | ValObjTable (_: ValueTable)
  | ValObjControl (scope: Env_EvalEnv)
                  (constructor_params: list (@P4Parameter tags_t))
                  (params: list (@P4Parameter tags_t)) (locals: list Declaration)
                  (apply: Block)
  | ValObjPackage (args: list (P4String * ValueLoc))
  | ValObjRuntime (loc: ValueLoc) (obj_name: P4String)
  | ValObjFun (params: list (@P4Parameter tags_t)) (impl: ValueFunctionImplementation)
  | ValObjAction (scope: Env_EvalEnv) (params: list (@P4Parameter tags_t)) (body: Block)
  | ValObjPacket (bits: list bool).

  Inductive ValueConstructor :=
  | ValConsParser (scope: Env_EvalEnv) (constructor_params: list (@P4Parameter tags_t))
                  (params: list (@P4Parameter tags_t)) (locals: list Declaration)
                  (states: list ParserState)
  | ValConsTable (_: ValueTable)
  | ValConsControl (scope: Env_EvalEnv) (constructor_params: list (@P4Parameter tags_t))
                   (params: list (@P4Parameter tags_t)) (locals: list Declaration)
                   (apply: Block)
  | ValConsPackage (params: list (@P4Parameter tags_t)) (args: list (P4String * ValueLoc))
  | ValConsExternObj (_: list (P4String * list (@P4Parameter tags_t))).

  Inductive Value :=
  | ValBase (_: ValueBase)
  | ValObj (_: ValueObject)
  | ValCons (_: ValueConstructor)
  | ValLvalue (_: ValueLvalue).

  Inductive program := Program (_: list Declaration).

End Syntax.
