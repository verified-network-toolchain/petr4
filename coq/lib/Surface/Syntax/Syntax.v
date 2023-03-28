Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

From Coq Require Import Numbers.BinNums Classes.EquivDec.

From Poulet4.P4light.Syntax Require P4String P4Int.


Section Syntax.

  Context {tags_t: Type}.
  Notation P4String := (P4String.t tags_t).
  Notation P4Int := (P4Int.t tags_t).

  Variant direction :=
  | In
  | Out
  | InOut
  | Directionless.

  Variant variableTyp :=
  | TypVariable (variable: P4String).

  Variant functionKind :=
  | FunParser
  | FunControl
  | FunExtern
  | FunTable
  | FunAction
  | FunFunction
  | FunBuiltin.

  Variant uniOp : Type :=
  | Not
  | BitNot
  | UMinus.

  Variant binOp : Type :=
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
(*add info, and option type. initially have none for type. *)
  Inductive surfaceTyp := 
  | TypBool
  | TypError
  | TypMatchKind
  | TypInteger
  | TypString
  | TypInt            (width: N)
  | TypBit            (width: N)
  | TypVarBit         (width: N)
  | TypIdentifier     (name: P4String)
  | TypSpecialization (base: surfaceTyp)
                      (args: list surfaceTyp)
  | TypHeaderStack    (typ: surfaceTyp)
                      (size: N)
  | TypTuple          (types: list surfaceTyp).

  Variant functionTyp :=
  | TypSurface (typ: surfaceTyp)
  | TypVoid
  | TypVar     (variable: variableTyp).

  Inductive declaredTyp :=
  | TypHeader      (type_params: list variableTyp) (*needs to represent both before and after inference. *)
                   (fields: P4String.AList tags_t surfaceTyp)
  | TypHeaderUnion (type_params: list variableTyp)
                   (fields: P4String.AList tags_t surfaceTyp)
  | TypStruct      (type_params: list variableTyp)
                   (fields: P4String.AList tags_t surfaceTyp)
  | TypEnum        (name: P4String)
                   (typ: option surfaceTyp)
                   (members: list P4String)
  | TypParser      (type_params: list variableTyp)
                   (parameters: list parameter)
  | TypControl     (type_params: list variableTyp)
                   (parameters: list parameter)
  | TypPackage     (type_params: list variableTyp)
                   (wildcard_params: list P4String)
                   (parameters: list parameter)
  with parameter :=
  | Param (dir: direction)
          (typ: surfaceTyp)
          (default_value: option expression)
          (variable: P4String)
  with expressionPreT :=
  | ExpBool                   (b: bool)
  | ExpString                 (s: P4String)
  | ExpInt                    (i: P4Int)
  (* | ExpSignedInt (*how come neither p4light nor surface has this*) *)
  (* | ExpBitString (*how come neither p4light nor surface has this*) *)
  | ExpName                   (name: P4String) (*why would it be typed.name?*)
  | ExpArrayAccess            (array: expression)
                              (index: expression)
  | ExpBitStringAccess        (bits: expression)
                              (lo: expression)
                              (high: expression)
  | ExpList                   (value: list expression)
  | ExpRecord                 (entries: P4String.AList tags_t expression)
  | ExpUnaryOp                (op: uniOp)
                              (arg: expression)
  | ExpBinaryOp               (op: binOp)
                              (arg1: expression)
                              (arg2: expression)
  | ExpCast                   (typ: typ) (*this is different from p4 spec.*)
                              (expr: expression)
  | ExpTypeMember             (typ: P4String)
                              (mem: P4String)
  | ExpErrorMember            (mem: P4String)
  | ExpExpressionMember       (expr: expression)
                              (mem: P4String)
  | ExpTernary                (cond: expression)
                              (tru: expression)
                              (fls: expression)
  | ExpFunctionCall           (func: expression)
                              (type_args: list surfaceTyp) (*can the IR have any type variables?*)
                              (args: list argument)
  | ExpAnonymousInstantiation (typ: surfaceTyp)
                              (args: list argument)
  | ExpBitmask                (expr: expression)
                              (mask: expression)
  | ExpRange                  (low: expression)
                              (high: expression)
  with expression :=
  | MkExpression (tags: tags_t)
                 (expr: expressionPreT)
                 (* (typ: typ) *)
                 (* (dir: direction) *)
  with argument :=
  | ExpArg      (value: expression) 
  | KeyValueArg (key: P4String)
                (value: expression)
  | MissingArg (*can the IR  have any missing?*)
  with synthesizedTyp :=
  | TypFunction    (type_params: list variableTyp)
                   (parameters: list parameter)
                   (kind: functionKind)
                   (ret: functionTyp)
  | TypSet         (typ: surfaceTyp)
  | TypExtern      (extern_name: P4String)
  | TypRecord      (type_params: list variableTyp)
                   (fields: P4String.AList tags_t surfaceTyp)
  | TypNewTyp      (name: P4String)
                   (typ: surfaceTyp)
  | TypAction      (data_params: list parameter)
                   (ctrl_params: list parameter)
  | TypConstructor (type_params: list variableTyp)
                   (wildcard_params: list P4String)
                   (params: list parameter)
                   (ret: functionTyp)
  | TypTable       (result_typ_name: P4String)
  with typ :=
  | TypeSurface (typ: surfaceTyp)
  | TypeDeclared (typ: declaredTyp) 
  | TypeSynthesized (typ: synthesizedTyp).
  (* | TypVoid. *)

  Variant stmtSwitchLabel :=
  | StmtSwitchLabelDefault (tags: tags_t)
  | StmtSwitchLabelName    (tags: tags_t)
                           (label: P4String).

  Inductive stmtSwitchCases :=
  | StmtSwitchCaseAction      (tags: tags_t)
                              (lable: stmtSwitchLabel)
                              (code: block)
  | StmtSwitchCaseFallThrough (tags: tags_t)
                              (lable: stmtSwitchLabel)
  with statementPreT := (*not sure why surface.ml has declaration in statements and p4light has variable and instantiation in it.*)
  | StmtMethodCall        (func: expression)
                          (type_args: list surfaceTyp)
                          (args: list argument)
  | StmtAssignment        (lhs: expression)
                          (rhs: expression)
  | StmtdirectApplication (typ: surfaceTyp)
                          (args: list argument)
  | StmtConditional       (cond: expression)
                          (tru: statement)
                          (fls: option statement)
  | StmtBlock             (block: block)
  | StmtExit
  | StmtEmpty
  | StmtReturn            (expr: option expression)
  | StmtSwitch            (expr: expression)
                          (cases: list stmtSwitchCases)
  with statement :=
  | MkStatement (tags: tags_t)
                (stmt: statementPreT)
                (* (typ: typ). *)
  with block :=
  | BlockEmpty (tags: tags_t)
  | BlockCons (statement: statement)
              (rest: block).

  Variant tableOrParserMatch :=
  | MatchDefault    (tags: tags_t)
  | MatchDontCare   (tags: tags_t)
  | MatchExpression (tags: tags_t)
                    (expr: expression).

  Variant parserCase :=
  | ParserCase (tags: tags_t)
               (matches: list tableOrParserMatch)
               (next: P4String).

  Variant parserTransition :=
  | ParserDirect (tags: tags_t)
                 (next: P4String)
  | ParserSelect (tags: tags_t)
                 (exprs: list expression)
                 (cases: list parserCase).

  Variant parserState :=
  | ParserState (tags: tags_t)
                (name: P4String)
                (statements: list statement)
                (transistion: parserTransition).

  Variant fieldType :=
  | FieldType (typ: surfaceTyp)
              (field: P4String).

  Variant methodPrototype :=
  | ProtoConstructor    (tags: tags_t)
                        (name: P4String)
                        (params: list parameter)
  | ProtoAbstractMethod (tags: tags_t)
                        (ret_type: surfaceTyp)
                        (name: P4String)
                        (type_params: list P4String)
                        (params: list parameter)
  | ProtoMethod         (tags: tags_t)
                        (ret_type: surfaceTyp)
                        (name: P4String)
                        (type_params: list P4String)
                        (params: list parameter).

  Variant tableKey :=
  | TabKey (tags: tags_t)
           (key: expression)
           (match_kind: P4String).

  Variant actionRef :=
  | TabActionRef (tags: tags_t)
                 (name: P4String) (*it's name in surface.ml.*)
                 (args: list argument).

  Variant tableEntry :=
  | TabEntry (tags: tags_t)
             (matches: list tableOrParserMatch)
             (action: actionRef).

  Variant tableProperty :=
  | TableKey           (tags: tags_t)
                       (keys: list tableKey)
  | TableActions       (tags: tags_t)
                       (actions: list actionRef)
  | TableEntries       (tags: tags_t)
                       (entries: list tableEntry)
  | TableDefaultAction (tags: tags_t)
                       (action: actionRef)
                       (const: bool)
  | TableCustom        (tags: tags_t)
                       (name: P4String)
                       (value: expression)
                       (const: bool).

  Inductive declarationPreT :=
  | DeclConstant         (typ: surfaceTyp)
                         (name: P4String)
                         (value: expression)
  | DeclInstantiation    (typ: surfaceTyp)
                         (args: list argument)
                         (name: P4String)
                         (init: list declaration)
  | DeclParser           (name: P4String)
                         (type_params: list P4String)
                         (params: list parameter)
                         (constructor_params: list parameter)
                         (locals: declaration)
                         (states: list parserState)
  | DeclControl          (name: P4String)
                         (type_params: list P4String)
                         (params: list parameter)
                         (constructor_params: list parameter)
                         (locals: list declaration)
                         (apply: block)
  | DeclFunction         (ret_typ: functionTyp)
                         (name: P4String)
                         (type_params: list P4String)
                         (params: list parameter)
                         (body: block)
  | DeclExternFunction   (ret_type: surfaceTyp)
                         (name: P4String)
                         (type_params: list P4String)
                         (params: list parameter)
  | DeclVariable         (typ: surfaceTyp)
                         (name: P4String)
                         (init: option expression)
  | DeclValueSet         (typ: surfaceTyp)
                         (name: P4String)
                         (size: expression)
  | DeclAction           (name: P4String)
                         (data_params: list parameter)
                         (ctrl_params: list parameter)
                         (body: block)
  | DeclTable            (name: P4String)
                         (props: list tableProperty)
  | DeclHeaderTyp        (name: P4String)
                         (fields: list fieldType)
  | DeclHeaderUnionTyp   (name: P4String)
                         (fields: list fieldType)
  | DeclStructTyp        (name: P4String)
                         (fields: list fieldType)
  | DeclError            (members: list P4String)
  | DeclMatchKind        (members: list P4String)
  | DeclEnumTyp          (name: P4String)
                         (members: list P4String)
  | DeclSerializableEnum (typ: surfaceTyp)
                         (name: P4String)
                         (members: P4String.AList tags_t expression)
  | DeclControlTyp       (name: P4String)
                         (type_params: list P4String)
                         (params: list parameter)
  | DeclParserTyp        (name: P4String)
                         (type_params: list P4String)
                         (params: list parameter)
  | DeclPackageTyp       (name: P4String)
                         (type_params: list P4String)
                         (params: list parameter)
  | DeclExternObject     (name: P4String)
                         (type_params: list P4String)
                         (methods: list methodPrototype)
  | DeclTypeDef          (name: P4String)
                         (typ_or_dcl: (surfaceTyp + declaration))
  | DeclNewType          (name: P4String)
                         (typ_or_dcl: (surfaceTyp + declaration))
  with declaration :=
  | MkDeclaration (tags: tags_t)
                  (decl: declarationPreT).
                  (* (typ: typ). *)


End Syntax. 

