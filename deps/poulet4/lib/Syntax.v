Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bvector.

Require Import Monads.Monad.
Require Import Monads.Option.
Require Import Monads.State.

Require Import Info.
Require Import Typed.

Open Scope monad.

(* Molly: not needed since it is defined in Typed.
Definition Annotation := Types.Annotation. *)

Definition P4String := Types.P4String.
Definition P4Int := Types.P4Int.

Inductive MethodPrototype :=
  (* annotations, name, params *)
  | MethProto_Constructor (info: Info) (annotations: list Annotation) (name: P4String)
                          (params: list P4Parameter)
  (* annotations, return, name, type_params, params *)
  | MethProto_AbstractMethod (info: Info) (annotations: list Annotation) (ret: P4Type)
                             (name: P4String)(type_params: list P4String)
                             (params: list P4Parameter)
  (* annotations, return, name, type_params, params *)
  | MethProto_Method (info: Info) (annotations: list Annotation) (ret: P4Type)
                     (name: P4String) (type_params: list P4String)
                     (params: list P4Parameter).

Inductive KeyValue :=
  | MkKeyValue (info: Info) (key: P4String) (value: Expression)
with Expression_pre_t :=
  | Exp_Bool (b: bool)
  | Exp_Int (_: P4Int)
  | Exp_String (_: P4String)
  | Exp_Name (_: Types.name)
  (* array, index *)
  | Exp_ArrayAccess (array: Expression) (index: Expression)
  (* bits, lo [int] , hi [int] *)
  | Exp_BitStringAccess (bits: Expression) (lo: Expression) (hi: Expression)
  | Exp_List (value: list Expression)
  | Exp_Record (entries: list KeyValue)
  | Exp_UnaryOp (op: Types.Op_uni) (arg: Expression)
  | Exp_BinaryOp (op: Types.Op_bin) (args: (Expression * Expression))
  | Exp_Cast (typ: P4Type) (expr: Expression)
  | Exp_TypeMember (typ: Types.name) (name: P4String)
  | Exp_ErrorMember (_: P4String)
  | Exp_ExpressionMember (expr: Expression) (name: P4String)
  (* cond, tru, fls *)
  | Exp_Ternary (cond: Expression) (tru: Expression) (fls: Expression)
  (* func, type_args, args *)
  | Exp_FunctionCall (func: Expression) (type_args: list P4Type)
                     (args: list (option Expression))
  (* type, args *)
  | Exp_NamelessInstantiation (typ: P4Type) (args: list Expression)
  | Exp_DontCare
  (* expr, mask *)
  | Exp_Mask (expr: Expression) (mask: Expression)
  (* lo, hi *)
  | Exp_Range (lo: Expression) (hi: Expression)
with Expression :=
  (* expr, typ, dir*)
  | MkExpression (info: Info) (expr: Expression_pre_t) (typ: P4Type) (dir: direction).

Inductive Match_pre_t :=
  | Match_DontCare
  | Match_Expression (expr: Expression).
Inductive Match :=
  | MkMatch (info: Info) (expr: Match_pre_t) (typ: P4Type).

Inductive Table_pre_action_ref :=
  (* annotations, name, args *)
  | MkTable_pre_action_ref (annotations: list Annotation) (name: Types.name)
                           (args: list (option Expression)).
Inductive Table_action_ref :=
  (* action, type *)
  | MkTable_action_ref (info: Info) (action: Table_pre_action_ref)
                       (typ: Typed.P4Type).


Inductive Table_key :=
  (* annotations, key, match_kind *)
  | MkTable_key (info: Info) (annotations: list Annotation) (key: list Expression)
                (match_kind: P4String).

Inductive Table_entry :=
  (* annotations, matches, action *)
  | MkTable_entry (info: Info) (annotations: list Annotation) (matches: list Match)
                  (action: Table_action_ref).

Inductive Table_property :=
  (* annotations, const, name, value *)
  | MkTable_property (info: Info) (annotations: list Annotation) (const: bool)
                     (name: P4String) (value: Expression).

Inductive Statement_switch_label :=
  | StatSwLab_Default (info: Info)
  | StatSwLab_Name (info: Info) (_: P4String).

Inductive Declaration_field :=
| MkDeclaration_field (info: Info) (annotations: list Annotation) (typ: P4Type)
                      (name: P4String).

Definition Value_loc := string.

Inductive Value_vtable :=
  (* name, keys, actions, default_action, const_entries *)
| ValVTable (name: string) (keys: list Table_key)
            (actions: list Table_action_ref) (default_action: Table_action_ref)
            (const_entries: list Table_entry).

Definition Env_env binding := list (list (string * binding)).

Inductive Env_EvalEnv :=
  | MkEnv_EvalEnv (vs: Env_env Value_loc) (typ: Env_env P4Type) (namespace: string).

Inductive Statement_switch_case :=
  (* label, code *)
  | StatSwCase_Action (info: Info) (label: Statement_switch_label) (code: Block)
  (* label *)
  | StatSwCase_FallThrough (info: Info) (label: Statement_switch_label)
with Statement_pre_t :=
  (* func, type_args, args *)
  | Stat_MethodCall (func: Expression) (type_args: list P4Type)
                    (args: list (option Expression))
  (* lhs, rhs *)
  | Stat_Assignment (lhs: Expression) (rhs: Expression)
  (* typ, args *)
  | Stat_DirectApplication (typ: P4Type) (args: list Expression)
  (* cond, tru, fls *)
  | Stat_Conditional (cond: Expression) (tru: Statement) (fls: option Statement)
  | Stat_BlockStatement (block: Block)
  | Stat_Exit
  | Stat_EmptyStatement
  | Stat_Return (expr: option Expression)
  (* expr, cases *)
  | Stat_Switch (expr: Expression) (cases: list Statement_switch_case)
  | Stat_Constant (info: Info) (annotations: list Annotation) (typ: P4Type)
                  (name: P4String) (value: Value_value)
  | Stat_Variable (info: Info) (annotations: list Annotation) (typ: P4Type)
                  (name: P4String) (init: option Expression)
with Statement :=
  | MkStatement (info: Info) (stmt: Statement_pre_t) (typ: StmType)
with Block :=
  | BlockEmpty (info: Info) (annotations: list Annotation)
  | BlockCons (statement: Statement) (rest: Block)
with Parser_case :=
  (* matches, next *)
  | MkParser_case (info: Info) (matches: list Match) (next: P4String)
with Parser_transition :=
  (* next *)
  | Parse_Direct (info: Info) (next: P4String)
  (* exprs, cases *)
  | Parse_Select (info: Info) (exprs: list Expression) (cases: list Parser_case)
with Parser_state :=
  (* annotations, name, statements, transition *)
  | MkParser_state (info: Info) (annotations: list Annotation) (name: P4String)
                   (statements: list Statement) (transition: Parser_transition)
with Declaration :=
  (* annotations, typ, name, value *)
  | Decl_Constant (info: Info) (annotations: list Annotation) (typ: P4Type)
                  (name: P4String) (value: Value_value)
  (* annotations, typ, args, name, init *)
  | Decl_Instantiation (info: Info) (annotations: list Annotation) (typ: P4Type)
                       (args: list Expression) (name: P4String) (init: option Block)
  (* annotations, name, typ_params, params, constructor_params, locals,
     states *)
  | Decl_Parser (info: Info) (annotations: list Annotation) (name: P4String)
                (type_params: list P4String) (params: list P4Parameter)
                (constructor_params: list P4Parameter)
                (locals: list Declaration) (states: list Parser_state)

  (* annotations, name, typ_params, params, constructor_params, locals,
     apply *)
  | Decl_Control (info: Info) (annotations: list Annotation) (name: P4String)
                 (type_params: list P4String) (params: list P4Parameter)
                 (constructor_params: list P4Parameter) (locals: list Declaration)
                 (apply: Block)
  (* return, name, typ_params, params, body *)
  | Decl_Function (info: Info) (ret: P4Type) (name: P4String)
                  (type_params: list P4String) (params: list P4Parameter) (body: Block)
  (* annotations, return, name, typ_params, params *)
  | Decl_ExternFunction (info: Info) (annotations: list Annotation) (ret: P4Type)
                        (name: P4String) (type_params: list P4String)
                        (params: list P4Parameter)
  (* annotations, typ, name, init *)
  | Decl_Variable (info: Info) (annotations: list Annotation) (typ: P4Type)
                  (name: P4String) (init: option Expression)
  (* annotations, typ, size, name *)
  | Decl_ValueSet (info: Info) (annotations: list Annotation) (typ: P4Type)
                  (size: Expression) (name: P4String)
  (* annotations, name, data_params, ctrl_params, body *)
  | Decl_Action (info: Info) (annotations: list Annotation) (name: P4String)
                (data_params: list P4Parameter) (ctrl_params: list P4Parameter)
                (body: Block)
  (* annotations, name, key, actions, entries, default_action, size,
     custom_properties *)
  | Decl_Table (info: Info) (annotations: list Annotation) (name: P4String)
               (key: list Table_key) (actions: list Table_action_ref)
               (entries: option (list Table_entry))
               (default_action: option Table_action_ref) (size: option P4Int)
               (custom_properties: list Table_property)
  (* annotations, name, fields *)
  | Decl_Header (info: Info) (annotations: list Annotation) (name: P4String)
                (fields: list Declaration_field)
  (* annotations, name, fields *)
  | Decl_HeaderUnion (info: Info) (annotations: list Annotation) (name: P4String)
                     (fields: list Declaration_field)
  (* annotations, name, fields *)
  | Decl_Struct (info: Info) (annotations: list Annotation) (name: P4String)
                (fields: list Declaration_field)
  | Decl_Error (info: Info) (members: list P4String)
  (* members *)
  | Decl_MatchKind (info: Info) (members: list P4String)
  (* annotations, name, members *)
  | Decl_Enum (info: Info) (annotations: list Annotation) (name: P4String)
              (members: list P4String)
  (* annotations, typ, name, members *)
  | Decl_SerializableEnum (info: Info) (annotations: list Annotation) (typ: P4Type)
                          (name: P4String) (members: list (P4String * Expression))
  (* annotations, name, typ_params, methods *)
  | Decl_ExternObject (info: Info) (annotations: list Annotation) (name: P4String)
                      (type_params: list P4String) (methods: list MethodPrototype)
  (* annotations, name, typ_or_decl *)
  | Decl_TypeDef (info: Info) (annotations: list Annotation) (name: P4String)
                 (typ_or_decl: (P4Type + Declaration))
  (* annotations, name, typ_or_decl *)
  | Decl_NewType (info: Info) (annotations: list Annotation) (name: P4String)
                 (typ_or_decl: (P4Type + Declaration))
  (* annotations, name, typ_params, params *)
  | Decl_ControlType (info: Info) (annotations: list Annotation) (name: P4String)
                     (type_params: list P4String) (params: list P4Parameter)
  (* annotations, name, typ_params, params *)
  | Decl_ParserType (info: Info) (annotations: list Annotation) (name: P4String)
                    (type_params: list P4String) (params: list P4Parameter)
  (* annotations, name, typ_params, params *)
  | Decl_PackageType (info: Info) (annotations: list Annotation) (name: P4String)
                     (type_params: list P4String) (params: list P4Parameter)
with Value_value :=
  | Val_Null
  | Val_Bool (_: bool)
  | Val_Integer (_: Z)
  (* widh, value *)
  | Val_Bit (width: nat) (value: Bvector width)
  (* width, value *)
  | Val_Int (width: nat) (value: Bvector width)
  (* max, width, value *)
  | Val_Varbit (max: nat) (width: nat) (value: Bvector width)
  | Val_String (_: string)
  | Val_Tuple (_: list Value_value)
  | Val_Record (_: list (string * Value_value))
  | Val_Set (_: Value_set)
  | Val_Error (_: string)
  | Val_MatchKind (_: string)
  (* scope, params, body *)
  | Val_Fun (scope: Env_EvalEnv) (params: list P4Parameter) (body: Block)
  (* name, caller *)
  | Val_BuiltinFun (name: string) (caller: Value_lvalue)
  (* scope, params, body *)
  | Val_Action (scope: Env_EvalEnv) (params: list P4Parameter) (body: Block)
  | Val_Struct (fields: list (string * Value_value))
  (* fields, is_valid *)
  | Val_Header (fields: list (string * Value_value)) (is_valid: bool)
  | Val_Union (fields: list (string * Value_value))
  (* headers, size, next *)
  | Val_Stack (headers: list Value_value) (size: nat) (next: nat)
  (* typ_name, enum_name *)
  | Val_EnumField (typ_name: string) (enum_name: string)
  (* typ_name, enum_name, value *)
  | Val_SenumField (typ_name: string) (enum_name: string) (value: Value_value)
  | Val_Senum (_: list (string * Value_value))
  (* loc, obj_name *)
  | Val_Runtime (loc: Value_loc) (obj_name: string)
  | Val_Parser (_: Value_vparser)
  | Val_Control (_: Value_vcontrol)
  (* params, args *)
  | Val_Package (params: list P4Parameter) (args: list (string * Value_loc))
  | Val_Table (_: Value_vtable)
  (* name, caller, params*)
  | Val_ExternFun (name: string) (caller: option (Value_loc * string))
                   (params: list P4Parameter)
  | Val_ExternObj (_: list (string * list P4Parameter))
with Value_set :=
  (* width, value *)
  | ValSet_SSingleton (width: nat) (value: Z)
  | ValSet_SUniversal
  (* value, mask *)
  | ValSet_SMask (value: Value_value) (mask: Value_value)
  (* lo, hi *)
  | ValSet_SRange (lo: Value_value) (hi: Value_value)
  | ValSet_SProd (_: list Value_set)
  (* width, nbits, value *)
  | ValSet_SLpm (width: Value_value) (nbits: nat) (value: Value_value)
  (* size, members, sets *)
  | ValSet_SValueSet (size: Value_value) (members: list (list Match))
                     (sets: list Value_set)
with Value_pre_lvalue :=
  | ValLeft_LName (name: Types.name)
  (* expr, name *)
  | ValLeft_LMember (expr: Value_lvalue) (name: string)
  (* expr, msb, lsb *)
  | ValLeft_LBitAccess (expr: Value_lvalue) (msb: nat) (lsb: nat)
  (* expr, idx *)
  | ValLeft_LArrayAccess (expr: Value_lvalue) (idx: Value_value)
with Value_lvalue :=
  | MkValue_lvalue (lvalue: Value_pre_lvalue) (typ: P4Type)
with Value_vparser :=
  (* scope, constructor_params, params, locals, states *)
  | MkValue_vparser (scope: Env_EvalEnv) (constructor_params: list P4Parameter)
                    (params: list P4Parameter) (locals: list Declaration)
                    (states: list Parser_state)
with Value_vcontrol :=
  (* scope, constructor_params, params, locals, apply *)
  | MkValue_vcontrol (scope: Env_EvalEnv) (constructor_params: list P4Parameter)
                     (params: list P4Parameter) (locals: list Declaration)
                     (apply: Block).

(* Molly: Value_pkt, Value_entries, Value_vset, Value_ctrl, Value_signal
          omitted*)

Inductive Env_CheckerEnv :=
  MkEnv_CheckerEnv (typ: Env_env P4Type) (typ_of: Env_env (P4Type * direction))
                   (const: Env_env Value_value).

Inductive program := Program (_: list Declaration).

