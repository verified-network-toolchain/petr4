Require Import Coq.Lists.List.
Require Import Coq.Numbers.BinNums.
Require Import Coq.Strings.String.

From Poulet4.P4light.Syntax Require Import
  Info Typed P4String P4Int Value.
Require Import Poulet4.Utils.Utils.

Section Syntax.

  Context {tags_t: Type}.
  Notation P4String := (P4String.t tags_t).
  Notation P4Int := (P4Int.t tags_t).

  Variant MethodPrototype :=
  | ProtoConstructor (tags: tags_t) (name: P4String)
                     (params: list (@P4Parameter tags_t))
  | ProtoAbstractMethod (tags: tags_t) (ret: @P4Type tags_t)
                        (name: P4String) (type_params: list P4String)
                        (params: list (@P4Parameter tags_t))
  | ProtoMethod (tags: tags_t) (ret: @P4Type tags_t)
                (name: P4String) (type_params: list P4String)
                (params: list (@P4Parameter tags_t)).

  Variant OpUni : Type :=
  | Not
  | BitNot
  | UMinus.

  Variant OpBin : Type :=
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

  Variant Locator :=
  | LGlobal (p: list string)
  | LInstance (p: list string).

  Definition NoLocator := LGlobal nil.

  (* Variant KeyValue :=
  | MkKeyValue (tags: tags_t) (key: P4String) (value: Expression) *)
  Inductive ExpressionPreT :=
  | ExpBool (b: bool)
  | ExpInt (_: P4Int)
  | ExpString (_: P4String)
  | ExpName (_: @Typed.name tags_t) (loc: Locator)
  | ExpArrayAccess (array: Expression) (index: Expression)
  | ExpBitStringAccess (bits: Expression) (lo: N) (hi: N)
  | ExpList (value: list Expression)
  | ExpRecord (entries: P4String.AList tags_t Expression)
  | ExpUnaryOp (op: OpUni) (arg: Expression)
  | ExpBinaryOp (op: OpBin) (arg1: Expression) (arg2: Expression)
  | ExpCast (typ: @P4Type tags_t) (expr: Expression)
  | ExpTypeMember (typ: P4String) (name: P4String)
  | ExpErrorMember (_: P4String)
  | ExpExpressionMember (expr: Expression) (name: P4String)
  | ExpTernary (cond: Expression) (tru: Expression) (fls: Expression)
  | ExpFunctionCall (func: Expression) (type_args: list (@P4Type tags_t))
                    (args: list (option Expression))
  | ExpNamelessInstantiation (typ: @P4Type tags_t) (args: list Expression)
  | ExpDontCare
  with Expression :=
  | MkExpression (tags: tags_t) (expr: ExpressionPreT) (typ: @P4Type tags_t) (dir: direction).

  Section Match.
    Context {T VS : Type}.
    
    Variant MatchPreT :=
      | MatchDontCare
      | MatchMask (expr: VS) (mask: VS)
      | MatchRange (lo: VS) (hi: VS)
      | MatchCast (typ: T) (expr: VS).

    Variant Match :=
      | MkMatch (tags: tags_t) (expr: MatchPreT) (typ: T).
  End Match.
  Global Arguments MatchPreT : clear implicits.
  Global Arguments Match : clear implicits.

  Inductive ValueSet :=
  | ValSetSingleton (value: (@ValueBase bool))
  | ValSetUniversal
  | ValSetMask (value: (@ValueBase bool)) (mask: (@ValueBase bool))
  | ValSetRange (lo: (@ValueBase bool)) (hi: (@ValueBase bool))
  | ValSetProd (_: list ValueSet)
  | ValSetLpm (nbits: N) (value: (@ValueBase bool))
  | ValSetValueSet (size: N) (members: list (list (Match (@P4Type tags_t) ValueSet))) (sets: list ValueSet).
        
  Variant TablePreActionRef :=
  | MkTablePreActionRef (name: @Typed.name tags_t)
                        (args: list (option Expression)).

  Variant TableActionRef :=
  | MkTableActionRef (tags: tags_t) (action: TablePreActionRef)
                     (typ: @Typed.P4Type tags_t).

  Variant TableKey :=
  | MkTableKey (tags: tags_t)  (key: Expression)
               (match_kind: P4String).

  Variant TableEntry :=
  | MkTableEntry (tags: tags_t)  (matches: list (Match (@P4Type tags_t) ValueSet))
                 (action: TableActionRef).

  Variant TableProperty :=
  | MkTableProperty (tags: tags_t)  (const: bool)
                    (name: P4String) (value: Expression).

  Variant StatementSwitchLabel :=
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
                          (func_typ: @P4Type tags_t)
                          (args: list (option Expression))
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
                  (name: P4String) (value: Expression)
                  (loc: Locator)
  | StatVariable  (typ: @P4Type tags_t)
                  (name: P4String) (init: option Expression)
                  (loc: Locator)
  | StatInstantiation  (typ: @P4Type tags_t)
                       (args: list Expression)
                       (name: P4String)
                       (init: list Initializer)
  with Statement :=
  | MkStatement (tags: tags_t)
                (stmt: StatementPreT)
                (typ: StmType)
  with Block :=
  | BlockEmpty (tags: tags_t)
  | BlockCons (statement: Statement)
              (rest: Block)
  with Initializer :=
  | InitFunction (tags: tags_t) (ret: @P4Type tags_t) (name: P4String)
                 (type_params: list P4String) (params: list (@P4Parameter tags_t)) (body: Block)
  | InitInstantiation (tags: tags_t)  (typ: @P4Type tags_t)
                      (args: list Expression) (name: P4String) (init: list Initializer).

  Definition ExpressionPreT_of_Expression
    '(MkExpression _ e _ _ : Expression) : ExpressionPreT := e.
  
  Section MatchMap.
    Context {A B U V : Type}.
    Variable f : A -> B.
    Variable g : U -> V.

    Definition map_MatchPreT (m : MatchPreT A U) : MatchPreT B V :=
      match m with
      | MatchDontCare => MatchDontCare
      | MatchMask u1 u2 => MatchMask (g u1) (g u2)
      | MatchRange u1 u2 => MatchRange (g u1) (g u2)
      | MatchCast a u => MatchCast (f a) (g u)
      end.

    Definition map_Match '(MkMatch i m a : Match A U) : Match B V :=
      MkMatch i (map_MatchPreT m) (f a).
  End MatchMap.
  
  Section statement_rec.
    Context
      {PStatementSwitchCase: StatementSwitchCase -> Type}
      {PStatementSwitchCaseList: list StatementSwitchCase -> Type}
      {PStatementPreT: StatementPreT -> Type}
      {PStatement: Statement -> Type}
      {PStatementMaybe: option Statement -> Type}
      {PBlock: Block -> Type}
      {PBlockMaybe: option Block -> Type}
      {PInitializer: Initializer -> Type}
      {PInitializerList: list Initializer -> Type}
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
      (HStatDirectApplication: forall typ func_typ args,
                               PStatementPreT
                                (StatDirectApplication typ func_typ args))
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
      (HStatConstant: forall typ name value loc,
                      PStatementPreT (StatConstant typ name value loc))
      (HStatVariable: forall typ name init loc,
                      PStatementPreT (StatVariable typ name init loc))
      (HInitFunction: forall tags ret name type_params params body,
                      PBlock body ->
                      PInitializer (InitFunction tags ret name type_params params body))
      (HInitInstantiation: forall tags typ args name init,
                           PInitializerList init ->
                           PInitializer (InitInstantiation tags typ args name init))
      (HInitializerListNil: PInitializerList nil)
      (HInitializerListCons: forall s l,
                             PInitializer s ->
                             PInitializerList l ->
                             PInitializerList (s :: l))
      (HStatInstantiation: forall typ args name init,
                           PInitializerList init ->
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
      | StatDirectApplication typ func_typ args =>
        HStatDirectApplication typ func_typ args
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
      | StatConstant typ name value loc =>
        HStatConstant typ name value loc
      | StatVariable typ name init loc =>
        HStatVariable typ name init loc
      | StatInstantiation typ args name init =>
        HStatInstantiation typ args name init
          (list_rec (PInitializer)
                    (PInitializerList)
                    (HInitializerListNil)
                    (HInitializerListCons)
                    (initializer_rec)
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
    with initializer_rec
      (i: Initializer)
      : PInitializer i
    :=
      match i with
      | InitFunction tags ret name type_params params body =>
        HInitFunction tags ret name type_params params body (block_rec body)
      | InitInstantiation tags typ args name init =>
        HInitInstantiation tags typ args name init
          (list_rec (PInitializer)
                    (PInitializerList)
                    (HInitializerListNil)
                    (HInitializerListCons)
                    (initializer_rec)
                    init)
      end.
  End statement_rec.

  Variant ParserCase :=
    | MkParserCase (tags: tags_t) (matches: list (Match (@P4Type tags_t) ValueSet)) (next: P4String).

  Variant ParserTransition :=
  | ParserDirect (tags: tags_t) (next: P4String)
  | ParserSelect (tags: tags_t) (exprs: list Expression) (cases: list ParserCase).

  Variant ParserState :=
  | MkParserState (tags: tags_t)  (name: P4String)
                  (statements: list Statement) (transition: ParserTransition).

  Variant DeclarationField :=
  | MkDeclarationField (tags: tags_t)  (typ: @P4Type tags_t)
                       (name: P4String).

  Inductive Declaration :=
  | DeclConstant (tags: tags_t)  (typ: @P4Type tags_t)
                 (name: P4String) (value: Expression)
  | DeclInstantiation (tags: tags_t)  (typ: @P4Type tags_t)
                      (args: list Expression) (name: P4String) (init: list Declaration)
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
                 (size: N) (name: P4String)
  | DeclAction (tags: tags_t)  (name: P4String)
               (data_params: list (@P4Parameter tags_t)) (ctrl_params: list (@P4Parameter tags_t))
               (body: Block)
  | DeclTable (tags: tags_t)  (name: P4String)
              (key: list TableKey) (actions: list TableActionRef)
              (entries: option (list TableEntry))
              (default_action: option TableActionRef) (size: option N)
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
                         (name: P4String) (members: P4String.AList tags_t Expression)
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

  Record ExternMethod :=
    { name: P4String;
      typ: @FunctionType tags_t }.

  Record ExternMethods :=
    { type_params: list P4String;
      methods: list ExternMethod;
      abst_methods: list ExternMethod }.

  Variant program := Program (_: list Declaration).

End Syntax.
