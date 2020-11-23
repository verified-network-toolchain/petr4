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

Inductive ValueBase :=
  | ValBaseNull
  | ValBaseBool (_: bool)
  | ValBaseInteger (_: Z)
  (* widh, value *)
  | ValBaseBit (width: nat) (value: Bvector width)
  (* width, value *)
  | ValBaseInt (width: nat) (value: Bvector width)
  (* max, width, value *)
  | ValBaseVarbit (max: nat) (width: nat) (value: Bvector width)
  | ValBaseString (_: string)
  | ValBaseTuple (_: list ValueBase)
  | ValBaseRecord (_: list (string * ValueBase))
  | ValBaseSet (_: ValueSet)
  | ValBaseError (_: string)
  | ValBaseMatchKind (_: string)
  | ValBaseStruct (fields: list (string * ValueBase))
  (* fields, is_valid *)
  | ValBaseHeader (fields: list (string * ValueBase)) (is_valid: bool)
  | ValBaseUnion (fields: list (string * ValueBase))
  (* headers, size, next *)
  | ValBaseStack (headers: list ValueBase) (size: nat) (next: nat)
  (* typ_name, enum_name *)
  | ValBaseEnumField (typ_name: string) (enum_name: string)
  (* typ_name, enum_name, value *)
  | ValBaseSenumField (typ_name: string) (enum_name: string) (value: ValueBase)
  | ValBaseSenum (_: list (string * ValueBase))
with ValueSet :=
  (* width, value *)
  | ValSetSingleton (width: nat) (value: Z)
  | ValSetUniversal
  (* value, mask *)
  | ValSetMask (value: ValueBase) (mask: ValueBase)
  (* lo, hi *)
  | ValSetRange (lo: ValueBase) (hi: ValueBase)
  | ValSetProd (_: list ValueSet)
  (* width, nbits, value *)
  | ValSetLpm (width: ValueBase) (nbits: nat) (value: ValueBase)
  (* size, members, sets *)
  | ValSetValueSet (size: ValueBase) (members: list (list Match))
                   (sets: list ValueSet).

Inductive StatementSwitchLabel :=
  | StatSwLabDefault (info: Info)
  | StatSwLabName (info: Info) (_: P4String).

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
                 (name: P4String) (value: ValueBase)
  | StatVariable (annotations: list Annotation) (typ: P4Type)
                 (name: P4String) (init: option Expression)
  | StatInstantiation (annotations: list Annotation) (typ: P4Type)
                      (args: list Expression) (name: P4String) (init: option Block)
with Statement :=
  | MkStatement (info: Info) (stmt: StatementPreT) (typ: StmType)
with Block :=
  | BlockEmpty (info: Info) (annotations: list Annotation)
  | BlockCons (statement: Statement) (rest: Block).

Inductive ParserCase :=
  (* matches, next *)
  | MkParserCase (info: Info) (matches: list Match) (next: P4String).

Inductive ParserTransition :=
  (* next *)
  | ParserDirect (info: Info) (next: P4String)
  (* exprs, cases *)
  | ParserSelect (info: Info) (exprs: list Expression) (cases: list ParserCase).

Inductive ParserState :=
  (* annotations, name, statements, transition *)
  | MkParserState (info: Info) (annotations: list Annotation) (name: P4String)
                   (statements: list Statement) (transition: ParserTransition).

Inductive DeclarationField :=
| MkDeclarationField (info: Info) (annotations: list Annotation) (typ: P4Type)
                     (name: P4String).

Inductive Declaration :=
  (* annotations, typ, name, value *)
  | DeclConstant (info: Info) (annotations: list Annotation) (typ: P4Type)
                  (name: P4String) (value: ValueBase)
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
                     (type_params: list P4String) (params: list P4Parameter).


Definition ValueLoc := string.

Inductive ValueTable :=
  (* name, keys, actions, default_action, const_entries *)
| MkValTable (name: string) (keys: list TableKey)
             (actions: list TableActionRef) (default_action: TableActionRef)
             (const_entries: list TableEntry).

Definition Env_env binding := list (list (string * binding)).

Inductive Env_EvalEnv :=
  | MkEnv_EvalEnv (vs: Env_env ValueLoc) (typ: Env_env P4Type) (namespace: string).


Inductive ValuePreLvalue :=
  | ValLeftName (name: Types.name)
  (* expr, name *)
  | ValLeftMember (expr: ValueLvalue) (name: string)
  (* expr, msb, lsb *)
  | ValLeftBitAccess (expr: ValueLvalue) (msb: nat) (lsb: nat)
  (* expr, idx *)
  | ValLeftArrayAccess (expr: ValueLvalue) (idx: nat)
with ValueLvalue :=
  | MkValueLvalue (lvalue: ValuePreLvalue) (typ: P4Type).

Inductive ValueObject :=
  | ValObjParser (scope: Env_EvalEnv)
                 (params: list P4Parameter) (locals: list Declaration)
                 (states: list ParserState)
  | ValObjTable (_: ValueTable)
  | ValObjControl (scope: Env_EvalEnv)
                  (params: list P4Parameter) (locals: list Declaration)
                  (apply: Block)
  | ValObjPackage (args: list (string * ValueLoc))
  | ValObjRuntime (loc: ValueLoc) (obj_name: string)
  | ValObjExternFun (name: string) (caller: option (ValueLoc * string))
                   (params: list P4Parameter)
  | ValObjFun (scope: Env_EvalEnv) (params: list P4Parameter) (body: Block)
  | ValObjBuiltinFun (name: string) (caller: ValueLvalue)
  | ValObjAction (scope: Env_EvalEnv) (params: list P4Parameter) (body: Block).

Inductive ValueConstructor :=
  | ValConsParser (scope: Env_EvalEnv) (constructor_params: list P4Parameter)
                  (params: list P4Parameter) (locals: list Declaration)
                  (states: list ParserState)
  | ValConsTable (_: ValueTable)
  | ValConsControl (scope: Env_EvalEnv) (constructor_params: list P4Parameter)
                   (params: list P4Parameter) (locals: list Declaration)
                   (apply: Block)
  | ValConsPackage (params: list P4Parameter) (args: list (string * ValueLoc))
  | ValConsExternObj (_: list (string * list P4Parameter)).

Inductive Value :=
  | ValBase (_: ValueBase)
  | ValObj (_: ValueObject)
  | ValCons (_: ValueConstructor).


(* Molly: Value_pkt, Value_entries, Value_vset, Value_ctrl, Value_signal
          omitted*)


Inductive program := Program (_: list Declaration).

