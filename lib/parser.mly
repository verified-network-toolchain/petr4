(* Copyright 2019-present Cornell University
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not
 * use this file except in compliance with the License. You may obtain a copy
 * of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations
 * under the License.
 *)

%{
module Petr4 = struct end
open Poulet4.P4String
open Poulet4.Typed
open Surface
open Core_kernel
open Context

let declare_vars vars = List.iter vars ~f:declare_var
let declare_types types = List.iter types ~f:declare_type

let rec smash_annotations l tok2 =
  match l with 
  | [] ->
     [tok2]
  | [tok1] ->
     if P4info.follows tok1.tags tok2.tags then
       [{tags = P4info.merge tok1.tags tok2.tags; str = tok1.str ^ tok2.str}]
     else
       [tok1; tok2]
  | h::t -> h::smash_annotations t tok2

%}

(*************************** TOKENS *******************************)
%token<P4info.t> END
%token TYPENAME IDENTIFIER
%token<P4string.t> NAME STRING_LITERAL
%token<P4int.t * string> INTEGER
%token<P4info.t> LE GE SHL AND OR NE EQ
%token<P4info.t> PLUS MINUS PLUS_SAT MINUS_SAT MUL DIV MOD
%token<P4info.t> BIT_OR BIT_AND BIT_XOR COMPLEMENT
%token<P4info.t> L_BRACKET R_BRACKET L_BRACE R_BRACE L_ANGLE R_ANGLE R_ANGLE_SHIFT L_PAREN R_PAREN
%token<P4info.t> ASSIGN COLON COMMA QUESTION DOT NOT SEMICOLON
%token<P4info.t> AT PLUSPLUS
%token<P4info.t> DONTCARE
%token<P4info.t> MASK RANGE
%token<P4info.t> TRUE FALSE
%token<P4info.t> ABSTRACT ACTION ACTIONS APPLY BOOL BIT CONST CONTROL DEFAULT
%token<P4info.t> ELSE ENTRIES ENUM ERROR EXIT EXTERN HEADER HEADER_UNION IF IN INOUT
%token<P4info.t> INT KEY SELECT MATCH_KIND OUT PACKAGE PARSER RETURN STATE STRING STRUCT
%token<P4info.t> SWITCH TABLE THEN TRANSITION TUPLE TYPE TYPEDEF VARBIT VALUESET VOID
%token<P4info.t> PRAGMA PRAGMA_END
%token<P4string.t> UNEXPECTED_TOKEN

(********************** PRIORITY AND ASSOCIATIVITY ************************)
%right THEN ELSE   (* Precedence of THEN token is artificial *)
%nonassoc QUESTION
%nonassoc COLON
%left OR
%left AND
%left EQ NE
%left L_ANGLE R_ANGLE LE GE
%left BIT_OR
%left BIT_XOR
%left BIT_AND
%left SHL R_ANGLE_SHIFT
%left PLUSPLUS PLUS MINUS PLUS_SAT MINUS_SAT
%left MUL DIV MOD
%right PREFIX
%nonassoc L_PAREN L_BRACKET
%left DOT


%type <Table.action_ref> actionRef
%start <program> p4program
%start <Declaration.t> variableDeclaration
%start <Declaration.t> typeDeclaration

%%

(********************************** CONTEXTS ***********************************)

push_scope:
| (* empty *)
    { push_scope() }
;

(* Very similar to C++ driver.structure->pushContainerType(...) method *)
push_name:
| n = name
     { push_scope();
       declare_type n;
       n}

push_externName:
| n = externName
    { push_scope();
      declare_type n;
      n}

pop_scope:
| (* empty *)
    { pop_scope() }
;

(*
%inline scoped(X):
| push x = X pop
    { x }
;
*)

go_toplevel:
| (* empty *)
    { go_toplevel () }

go_local:
| (* empty *)
    { go_local () }

%inline toplevel(X):
| go_toplevel x = X go_local
    { x }

(************************************ LISTS **************************************)

(* We re-implement right-recursive versions of these standard functions to
   avoid some shift/reduce conflicts *)

separated_nonempty_list_aux(sep, X):
| x = X
    { [x] }
| xs = separated_nonempty_list_aux(sep, X) sep x = X
    { x::xs }
;

separated_nonempty_list(sep, X):
| rev_list = separated_nonempty_list_aux(sep, X)
    { List.rev rev_list }
;

separated_atLeastTwo_list_aux(sep, X):
| xs = separated_nonempty_list_aux(sep, X) sep x = X
    { x::xs }
;

separated_atLeastTwo_list(sep, X):
| rev_list = separated_atLeastTwo_list_aux(sep, X)
      {List.rev rev_list}
;

separated_list_aux(sep, X):
| (* empty *)
    { [] }
| x = X
    { [x] }
| xs = separated_list_aux(sep, X) sep x = X
    { x::xs }
;

separated_list(sep, X):
| rev_list = separated_list_aux(sep, X)
    { List.rev rev_list }
;

nonempty_list_aux(X):
| x = X
    { [x] }
| xs = nonempty_list_aux(X) x=X
    {x::xs}
;

nonempty_list(X):
| rev_list = nonempty_list_aux(X)
    { List.rev rev_list }
;

list_aux(X):
| (* empty *)
    { [] }
| xs = list_aux(X) x=X
    { x::xs }
;

list(X):
| rev_list = list_aux(X)
    { List.rev rev_list }
;

%inline option(X):
| (* empty *)
    { None   }
| x = X
    { Some x }
;

(**************************** P4-16 GRAMMAR ******************************)

p4program : ds = topDeclarationList END { Program(ds) };

topDeclarationList:
| (* empty *) { [] }
| SEMICOLON ds = topDeclarationList { ds }
| d = topDeclaration ds = topDeclarationList { d :: ds }

topDeclaration:
| c = constantDeclaration
    { declare_var (Declaration.name c);
      c }
| e = externDeclaration
    { e }
| a = actionDeclaration
    { declare_var (Declaration.name a);
      a }
| p = parserDeclaration
    { declare_type (Declaration.name p);
      p }
| c = controlDeclaration
    { declare_type (Declaration.name c);
      c }
| i = instantiation
    { declare_var (Declaration.name i);
      i }
| t = typeDeclaration
    { declare_type (Declaration.name t);
      t }
| e = errorDeclaration
    { (* declare_type (Declaration.name e); *)
      e }
| m = matchKindDeclaration
    { m }
| f = functionDeclaration
    { declare_var (Declaration.name f);
      f }
;

varName:
| id = NAME IDENTIFIER { id }
;

tableKwName:
| info = KEY { {tags=info; str="key"} }
| info = ACTIONS { {tags=info; str="actions"} }
| info = ENTRIES { {tags=info; str="entries"} }
;

nonTableKwName:
| n = varName { n }
| n = NAME TYPENAME { n }
| info = APPLY { {tags=info; str="apply"} }
| info = STATE { {tags=info; str="state"} }
| info = TYPE { {tags=info; str="type"} }
;

nonTypeName:
| n = varName { n }
| n = tableKwName { n }
| info = APPLY { {tags=info; str="apply"} }
| info = STATE { {tags=info; str="state"} }
| info = TYPE { {tags=info; str="type"} }
;

name:
| n = nonTypeName
| n = NAME TYPENAME   { n } ;

%inline optAnnotations:
| (* empty *)  { [] }
| annotations = annotations  { annotations }
;


annotations:
| annotations = nonempty_list(annotation) { annotations }
;

annotation:
| info1 = AT name = name
    { let info2 = name.tags in
      let body = (info2, Annotation.Empty) in 
      (P4info.merge info1 info2,
       Annotation.{ name; body } ) }

| info1 = AT name = name info2 = L_PAREN body = annotationBody info3 = R_PAREN
    { let body = (P4info.merge info2 info3, Annotation.Unparsed(body)) in
      (P4info.merge info1 info3, 
       Annotation.{ name; body }) }

| info1 = AT name = name info2 = L_BRACKET body = expressionList info3 = R_BRACKET
    { let body = (P4info.merge info2 info3, Annotation.Expression(body)) in
      (P4info.merge info1 info3, 
       Annotation.{ name; body }) }

| info1 = AT name = name info2 = L_BRACKET body = kvList info3 = R_BRACKET
    { let body = (P4info.merge info2 info3, Annotation.KeyValue(body)) in
      (P4info.merge info1 info3,
       Annotation.{ name; body }) }

| info1 = PRAGMA name = name body = annotationBody info2 = PRAGMA_END
    { let body = (P4info.merge info2 info2, Annotation.Unparsed(body)) in
       (P4info.merge info1 info2, 
       Annotation.{ name; body }) }
;

annotationBody:
| (* empty *) 
  { [] }
| body1 = annotationBody L_PAREN body2 = annotationBody R_PAREN
  { body1 @ body2 }
| body = annotationBody token = annotationToken
  { smash_annotations body token }
;

annotationToken:
| UNEXPECTED_TOKEN { $1 }
| ABSTRACT         { {tags=$1; str="abstract"} }
| ACTION           { {tags=$1; str="action"} }
| ACTIONS          { {tags=$1; str="actions"} }
| APPLY            { {tags=$1; str="apply"} }
| BOOL             { {tags=$1; str="bool"} }
| BIT              { {tags=$1; str="bit"} }
| CONST            { {tags=$1; str="const"} }
| CONTROL          { {tags=$1; str="control"} }
| DEFAULT          { {tags=$1; str="default"} }
| ELSE             { {tags=$1; str="else"} }
| ENTRIES          { {tags=$1; str="entries"} }
| ENUM             { {tags=$1; str="enum"} }
| ERROR            { {tags=$1; str="error"} }
| EXIT             { {tags=$1; str="exit"} }
| EXTERN           { {tags=$1; str="extern"} }
| FALSE            { {tags=$1; str="false"} }
| HEADER           { {tags=$1; str="header"} }
| HEADER_UNION     { {tags=$1; str="header_union"} }
| IF               { {tags=$1; str="if"} }
| IN               { {tags=$1; str="in"} }
| INOUT            { {tags=$1; str="inout"} }
| INT              { {tags=$1; str="int"} }
| KEY              { {tags=$1; str="key"} }
| MATCH_KIND       { {tags=$1; str="match_kind"} }
| TYPE             { {tags=$1; str="type"} }
| OUT              { {tags=$1; str="out"} }
| PARSER           { {tags=$1; str="parser"} }
| PACKAGE          { {tags=$1; str="package"} }
| PRAGMA           { {tags=$1; str="pragma"} }
| RETURN           { {tags=$1; str="return"} }
| SELECT           { {tags=$1; str="select"} }
| STATE            { {tags=$1; str="state"} }
| STRING           { {tags=$1; str="string"} }
| STRUCT           { {tags=$1; str="struct"} }
| SWITCH           { {tags=$1; str="switch"} }
| TABLE            { {tags=$1; str="table"} }
(* | THIS             { {tags=$1; str="this") } *)
| TRANSITION       { {tags=$1; str="transition"} }
| TRUE             { {tags=$1; str="true"} }
| TUPLE            { {tags=$1; str="tuple"} }
| TYPEDEF          { {tags=$1; str="typedef"} }
| VARBIT           { {tags=$1; str="varbit"} }
| VALUESET         { {tags=$1; str="valueset"} }
| VOID             { {tags=$1; str="void"} }
| DONTCARE         { {tags=$1; str="_"} }
| NAME IDENTIFIER  { $1 }
| NAME TYPENAME    { $1 }
| STRING_LITERAL   { {tags=$1.tags; str = "\"" ^ $1.str ^ "\""} }
| INTEGER          { let (i, str): P4int.t * string = $1 in 
                     {tags=i.tags; str} }
| MASK             { {tags=$1; str="&&&"} }
| RANGE            { {tags=$1; str=".."} }
| SHL              { {tags=$1; str="<<"} }
| AND              { {tags=$1; str="&&"} }
| OR               { {tags=$1; str="||"} }
| EQ               { {tags=$1; str="=="} }
| NE               { {tags=$1; str="!="} }
| GE               { {tags=$1; str=">="} }
| LE               { {tags=$1; str="<="} }
| PLUSPLUS         { {tags=$1; str="++"} }
| PLUS             { {tags=$1; str="+"} }
| PLUS_SAT         { {tags=$1; str="|+|"} }
| MINUS            { {tags=$1; str="-"} }
| MINUS_SAT        { {tags=$1; str="|-|"} }
| MUL              { {tags=$1; str="*"} }
| DIV              { {tags=$1; str="/"} }
| MOD              { {tags=$1; str="%"} }
| BIT_OR           { {tags=$1; str="|"} }
| BIT_AND          { {tags=$1; str="&"} }
| BIT_XOR          { {tags=$1; str="^"} }
| COMPLEMENT       { {tags=$1; str="~"} }
| L_BRACKET        { {tags=$1; str="["} }
| R_BRACKET        { {tags=$1; str="]"} }
| L_BRACE          { {tags=$1; str="{"} }
| R_BRACE          { {tags=$1; str="}"} }
| L_ANGLE          { {tags=$1; str="<"} }
| R_ANGLE          { {tags=$1; str=">"} }
| NOT              { {tags=$1; str="!"} }
| COLON            { {tags=$1; str=":"} }
| COMMA            { {tags=$1; str=","} }
| QUESTION         { {tags=$1; str="?"} }
| DOT              { {tags=$1; str="."} }
| ASSIGN           { {tags=$1; str="="} }
| SEMICOLON        { {tags=$1; str=";"} }
| AT               { {tags=$1; str="@"} }
;

parameterList:
| params = separated_list(COMMA, parameter)
    { let names = List.map ~f:(fun (_,p) -> p.Parameter.variable) params in
      declare_vars names; params }
;

parameter:
| annotations = optAnnotations direction = direction typ = typeRef variable = name
    { let info1 =
        match direction with
        | None -> info typ
        | Some dir -> info dir in
      (P4info.merge info1 variable.tags,
       Parameter.{ annotations; direction; typ; variable; opt_value = None }) }
| annotations = optAnnotations direction = direction typ = typeRef variable = name
   ASSIGN value = expression
    { let info1 =
        match direction with
        | None -> info typ
        | Some dir -> info dir in
      (P4info.merge info1 variable.tags,
       Parameter.{ annotations; direction; typ; variable; opt_value = Some value }) }
;

direction:
| info = IN      { Some (info, Direction.In) }
| info = OUT     { Some (info, Direction.Out) }
| info = INOUT   { Some (info, Direction.InOut) }
| (* empty *)    { None }
;

packageTypeDeclaration:
|  annotations = optAnnotations info1 = PACKAGE
   name = push_name
     type_params = optTypeParameters
     L_PAREN params = parameterList info2 = R_PAREN
     {  (P4info.merge info1 info2,
        Declaration.PackageType { annotations; name; type_params; params }) }
;

instantiation:
| annotations = optAnnotations typ = typeRef
    L_PAREN args = argumentList R_PAREN name = name info2 = SEMICOLON
    { (P4info.merge (Surface.info typ) info2,
       Declaration.Instantiation { annotations; typ; args; name; init=None }) }
| annotations = optAnnotations typ = typeRef
    L_PAREN args = argumentList R_PAREN name = name ASSIGN init = objInitializer info2 = SEMICOLON
    { (P4info.merge (Surface.info typ) info2,
       Declaration.Instantiation { annotations; typ; args; name; init=Some init }) }
;

objInitializer:
| L_BRACE statements = list(objDeclaration) R_BRACE 
  { (P4info.merge $1 $3, Block.{ annotations = []; statements }) }
;

objDeclaration:
| decl = functionDeclaration
  { (Surface.info decl, Statement.DeclarationStatement { decl }) }
| decl = instantiation 
  { (Surface.info decl, Statement.DeclarationStatement { decl }) }
;

optConstructorParameters:
| (* empty *) { [] }
| L_PAREN params = parameterList R_PAREN { params }
;

dotPrefix:
| info = DOT { info }
;

(**************************** PARSER ******************************)

parserDeclaration:
| p_type = parserTypeDeclaration constructor_params = optConstructorParameters
    L_BRACE locals = list_aux(parserLocalElement)
    states = nonempty_list(parserState)
    info2 = R_BRACE
    pop_scope
    { let (info1, annotations, name, type_params, params) = p_type in
      let info = P4info.merge info1 info2 in
      let locals = List.rev locals in
      (info, Declaration.Parser { annotations; name; type_params; params; constructor_params; locals; states }) }
;

parserLocalElement:
| c = constantDeclaration { c }
| v = variableDeclaration { v }
| i = instantiation       { i }
| vs = valueSetDeclaration { vs }
;

parserTypeDeclaration:
| annotations = optAnnotations info1 = PARSER
    name = push_name
    type_params = optTypeParameters L_PAREN params = parameterList info2 = R_PAREN
    { let info = P4info.merge info1 info2 in
      (info, annotations, name, type_params, params) }
;

parserState:
|  annotations = optAnnotations info1 = STATE
     name = push_name
       L_BRACE
       statements = list(parserStatement) transition = transitionStatement
       info2 = R_BRACE
     pop_scope
     { (P4info.merge info1 info2, Surface.Parser.{ annotations; name; statements; transition }) }

;

parserStatement:
| s = assignmentOrMethodCallStatement
| s = directApplication
| s = emptyStatement
| s = parserBlockStatement
   { s }
| decl = constantDeclaration
| decl = variableDeclaration
  { (Surface.info decl, Statement.DeclarationStatement { decl }) }
;

parserBlockStatement:
|  annotations = optAnnotations
     info1 = L_BRACE statements = list(parserStatement) info2 = R_BRACE
     { let info = P4info.merge info1 info2 in
       let block = (info, Block.{ annotations; statements }) in
       (info, Statement.BlockStatement { block = block }) }
;

transitionStatement:
| (* empty *)
  { let info = P4info.M "Compiler-generated reject transition" in
    (info, Surface.Parser.Direct { next = {tags=info; str="reject"} }) }

| info1 = TRANSITION transition = stateExpression
    { (P4info.merge info1 (Surface.info transition),
       snd transition) }
;

stateExpression:
| next = name info2 = SEMICOLON
    { (P4info.merge next.tags info2,
       Surface.Parser.Direct { next = next }) }
| select = selectExpression
    { select }
;

selectExpression:
| info1 = SELECT L_PAREN exprs = expressionList R_PAREN
    L_BRACE cases = list(selectCase) info2 = R_BRACE
    { (P4info.merge info1 info2,
       Surface.Parser.Select { exprs; cases }) }
;

selectCase:
| matches = keysetExpression COLON next = name info2 = SEMICOLON
  { let info1 = match matches with
      | expr::_ -> info expr
      | _ -> assert false in
    (P4info.merge info1 info2,
     Surface.Parser.{ matches; next }) }
;

keysetExpression:
| exprs = tupleKeysetExpression { exprs }
| expr  = simpleKeysetExpression { [expr] }
;

tupleKeysetExpression:
| L_PAREN exprs = separated_atLeastTwo_list(COMMA, simpleKeysetExpression) R_PAREN
    { exprs }
;

simpleKeysetExpression:
| expr = expression { (Surface.info expr, Match.Expression { expr }) }
| info = DONTCARE { (info, Match.DontCare) }
| info = DEFAULT { (info, Match.Default) }
| expr = expression MASK mask = expression
    { let info = P4info.merge (Surface.info expr) (Surface.info mask) in
      (info, Match.Expression { expr = (info, Expression.Mask { expr; mask }) }) }
| lo = expression RANGE hi = expression
    { let info = P4info.merge (Surface.info lo) (Surface.info hi) in
      (info, Match.Expression {expr = (info, Expression.Range { lo; hi })})}
;

valueSetDeclaration:
| annotations = optAnnotations
    info1 = VALUESET L_ANGLE typ = baseType r_angle
    L_PAREN size = expression R_PAREN name = name info2 = SEMICOLON
| annotations = optAnnotations
    info1 = VALUESET L_ANGLE typ = tupleType r_angle
    L_PAREN size = expression R_PAREN name = name info2 = SEMICOLON
| annotations = optAnnotations
    info1 = VALUESET L_ANGLE typ = typeName r_angle
    L_PAREN size = expression R_PAREN name = name info2 = SEMICOLON
    { (P4info.merge info1 info2,
      Declaration.ValueSet { annotations; typ; size; name } ) }
;

(*************************** CONTROL ************************)

controlDeclaration:
| ct_decl = controlTypeDeclaration constructor_params = optConstructorParameters
    L_BRACE locals = list(controlLocalDeclaration) APPLY apply = controlBody
    info2 = R_BRACE
    pop_scope
    {
      let info1, annotations, name, type_params, params = ct_decl in
      (P4info.merge info1 info2,
       Declaration.Control { annotations; name; type_params; params; constructor_params;
                             locals; apply } ) }
;

controlTypeDeclaration:
|  annotations = optAnnotations info1 = CONTROL
     name = push_name
     type_params = optTypeParameters
     L_PAREN params = parameterList info2 = R_PAREN
     { (P4info.merge info1 info2, annotations, name, type_params, params) }
;

controlLocalDeclaration:
| c = constantDeclaration
    { c }
| a = actionDeclaration
    { declare_var (Declaration.name a); a }
| t = tableDeclaration
    { declare_var (Declaration.name t); t }
| i = instantiation
    { i }
| v = variableDeclaration
    { v }
;

controlBody (* scoped at an upper level *):
| b = blockStatement { b }
;

(*************************** EXTERN *************************)

externDeclaration:
|  annotations = optAnnotations info1 = EXTERN
     name = push_externName
       type_params = optTypeParameters
       L_BRACE methods = list(methodPrototype) info2 = R_BRACE
     pop_scope
     { let type_decl =
         (P4info.merge info1 info2,
          (Declaration.ExternObject { annotations; name; type_params; methods })) in
       declare_type (Declaration.name type_decl);
       type_decl }
|  annotations = optAnnotations info1 = EXTERN
     func = functionPrototype pop_scope info2 = SEMICOLON
     { let (_, return, name, type_params, params) = func in
       let decl =
         (P4info.merge info1 info2,
          Declaration.ExternFunction { annotations; return; name; type_params; params }) in
       declare_var (Declaration.name decl);
       decl }
;

externName:
| n = nonTypeName { declare_type n; n }
(* So that it is declared a typename before constructors are parsed
   Could use midrule instead x) *)
;

functionPrototype:
| typ = typeOrVoid name = name
    push_scope
      type_params = optTypeParameters
      L_PAREN params = parameterList info2 = R_PAREN
    { (P4info.merge (Surface.info typ) info2, typ, name, type_params, params) }
;

methodPrototype:
| annotations = optAnnotations
  func = functionPrototype pop_scope info2 = SEMICOLON
    { let (info1, return, name, type_params, params) = func in
      (P4info.merge info1 info2,
       MethodPrototype.Method { annotations; return; name; type_params; params }) }

| annotations = optAnnotations
  ABSTRACT
  func = functionPrototype pop_scope info2 = SEMICOLON
    { let (info1, return, name, type_params, params) = func in
      (P4info.merge info1 info2,
       MethodPrototype.AbstractMethod { annotations; return; name; type_params; params }) }
| annotations = optAnnotations
  name = name (* NAME TYPENAME *)
    L_PAREN params = parameterList R_PAREN info2 = SEMICOLON
    { (P4info.merge name.tags info2,
      MethodPrototype.Constructor { annotations; name; params }) }
;

(************************** TYPES ****************************)

typeRef:
| t = baseType
| t = typeName
| t = specializedType
| t = headerStackType
| t = tupleType
    { t }
;

namedType:
| t = typeName
| t = specializedType
    { t }
;

prefixedTypeName:
| name = NAME TYPENAME
    { BareName name }
| dotPrefix go_toplevel name = NAME TYPENAME go_local
    { QualifiedName ([], name) }
;

prefixedType:
| name = prefixedTypeName
    { P4name.name_info name, Type.TypeName name }

typeName:
| typ = prefixedType
    { typ }
;

tupleType:
| info1 = TUPLE L_ANGLE elements = typeArgumentList info_r = r_angle
    { (P4info.merge info1 info_r,
       Type.Tuple elements) }
;

headerStackType:
| header = typeName L_BRACKET size = expression info2 = R_BRACKET
    { (P4info.merge (Surface.info header) info2,
       Type.HeaderStack { header; size }) }
;

specializedType:
| base = prefixedType L_ANGLE args = typeArgumentList info_r = r_angle
    { (P4info.merge (Surface.info base) info_r,
      Type.SpecializedType { base; args }) }
;

baseType:
| info = BOOL
    { (info, Type.Bool) }
| info = ERROR
    { (info, Type.Error) }
| info = BIT
    { let width = (info, Expression.Int
                           ({ tags = info;
                              value = Bigint.of_int 1;
                              width_signed = None })) in
      (info, Type.BitType width): Type.t }
| info1 = BIT L_ANGLE value = INTEGER info_r = r_angle
    { let value_int: P4int.t = fst value in 
      let value_info = value_int.tags in
      let width: Expression.t =
        (value_info, Expression.Int value_int) in
      let info: P4info.t = P4info.merge info1 info_r in
      (info, Type.BitType width): Type.t }
| info1 = INT L_ANGLE value = INTEGER info_r = r_angle
     { let value_int: P4int.t = fst value in 
       let value_info = value_int.tags in 
       let width = (value_info, Expression.Int value_int) in
       let info = P4info.merge info1 info_r in
      (info, Type.IntType width): Type.t }

| info1 = VARBIT L_ANGLE value = INTEGER info_r = r_angle
     { let value_int: P4int.t = fst value in 
       let value_info = value_int.tags in
       let max_width = (value_info, Expression.Int value_int) in
       let info = P4info.merge info1 info_r in
      (info, Type.VarBit max_width) }
| info1 = BIT L_ANGLE L_PAREN width = expression R_PAREN info_r = r_angle
    { (P4info.merge info1 info_r,
       Type.BitType width) }
| info1 = INT L_ANGLE L_PAREN width = expression R_PAREN info_r = r_angle
    { (P4info.merge info1 info_r,
       Type.IntType width) }
| info1 = VARBIT L_ANGLE L_PAREN max_width = expression R_PAREN info_r = r_angle
    { (P4info.merge info1 info_r,
       Type.VarBit max_width) }
| info = INT
    { (info, Type.Integer) }
| info = STRING
    { (info, Type.String) }
;

typeOrVoid:
| t = typeRef
  { t }
| info = VOID
  { (info, Type.Void) }
| name = varName
  { (name.tags, Type.TypeName (BareName name)) }    (* may be a type variable *)
;

optTypeParameters:
| (* empty *) { [] }
| L_ANGLE types = separated_list(COMMA, typeParameter) r_angle
    { declare_types types;
      types }
;

typeParameter:
| name = name { name }
;

realTypeArg:
| info = DONTCARE
  { (info, Type.DontCare) }
| t = typeRef
  { t }
;

typeArg:
| info = DONTCARE { (info, Type.DontCare) }
| typ = typeRef { typ }
| name = nonTypeName { (name.tags, Type.TypeName (BareName name)) }
| info = VOID { (info, Type.Void) }
;

typeArgumentList:
| ts = separated_list(COMMA, typeArg) {ts}
;

realTypeArgumentList:
| t = realTypeArg { [t] }
| t = realTypeArg COMMA ts = separated_list(COMMA, typeArg) { t :: ts }
;

typeDeclaration:
| d = derivedTypeDeclaration
| d = typedefDeclaration
| d = packageTypeDeclaration pop_scope SEMICOLON
  { declare_type (Declaration.name d);
    d }
| ctd = controlTypeDeclaration pop_scope SEMICOLON
  { let info, annotations, name, type_params, params = ctd in
    (info,
     Declaration.ControlType { annotations; name; type_params; params } ) }
| ptd = parserTypeDeclaration pop_scope SEMICOLON
  { let info, annotations, name, type_params, params = ptd in
    (info,
     Declaration.ParserType { annotations; name; type_params; params } ) }
;

derivedTypeDeclaration:
| d = headerTypeDeclaration
| d = headerUnionDeclaration
| d = structTypeDeclaration
| d = enumDeclaration
  { d }
;

headerTypeDeclaration:
|  annotations = optAnnotations info1 = HEADER name = name
     L_BRACE fields = list(structField) info2 = R_BRACE
     { (P4info.merge info1 info2,
        Declaration.Header { annotations; name; fields }) }
;

headerUnionDeclaration:
|  annotations = optAnnotations info1 = HEADER_UNION name = name
     L_BRACE fields = list(structField) info2 = R_BRACE
     { (P4info.merge info1 info2,
        Declaration.HeaderUnion { annotations; name; fields }) }
;

structTypeDeclaration:
|  annotations = optAnnotations info1 = STRUCT name = name
     L_BRACE fields = list(structField) info2 = R_BRACE
     { (P4info.merge info1 info2,
        Declaration.Struct { annotations; name; fields }) }
;

structField:
|  annotations = optAnnotations typ = typeRef name = name info2 = SEMICOLON
     { (P4info.merge (Surface.info typ) info2,
        { annotations; typ; name }) : Declaration.field }
;

(* TODO : add support for serializable enums *)
enumDeclaration:
| annotations = optAnnotations info1 = ENUM name = name
    L_BRACE members = identifierList info2 = R_BRACE
    { (P4info.merge info1 info2,
      Declaration.Enum { annotations; name; members }) }
| annotations = optAnnotations info1 = ENUM info2 = BIT L_ANGLE value = INTEGER r_angle
    name = name L_BRACE members = specifiedIdentifierList info4 = R_BRACE
   { let value_int: P4info.t P4int.pre_t = (fst value) in 
     let value_info: P4info.t = value_int.tags in 
     let width = (value_info, Expression.Int value_int) in
     let typ = (P4info.merge info2 info4, Type.BitType width) in
     (P4info.merge info1 info4,
      Declaration.SerializableEnum { annotations; typ; name; members }) }
;

errorDeclaration:
| info1 = ERROR L_BRACE members = identifierList info2 = R_BRACE
    { declare_vars members;
      (P4info.merge info1 info2,
       Declaration.Error { members }) }
;

matchKindDeclaration:
| info1 = MATCH_KIND L_BRACE members = identifierList info2 = R_BRACE
    { declare_vars members;
      (P4info.merge info1 info2,
       Declaration.MatchKind { members }) }
;

identifierList:
| ids = separated_nonempty_list(COMMA, id = name {id})
    { ids };

specifiedIdentifier:
| name = name ASSIGN init = expression
    { (name, init) }

specifiedIdentifierList:
| specIds = separated_nonempty_list(COMMA, specId = specifiedIdentifier { specId })
    { specIds };

typedefDeclaration:
| annotations = optAnnotations info1 = TYPEDEF
    typ = typeRef name = name info2 = SEMICOLON
    { (P4info.merge info1 info2,
       Declaration.TypeDef { annotations; name; typ_or_decl = Left typ } ) }
| annotations = optAnnotations info1 = TYPEDEF
    decl = derivedTypeDeclaration name = name info2 = SEMICOLON
    { (P4info.merge info1 info2,
       Declaration.TypeDef { annotations; name; typ_or_decl = Right decl } ) }
| annotations = optAnnotations info1 = TYPE
    typ = typeRef name = name info2 = SEMICOLON
    { (P4info.merge info1 info2,
       Declaration.NewType { annotations; name; typ_or_decl = Left typ } ) }
| annotations = optAnnotations info1 = TYPE
    decl = derivedTypeDeclaration name = name info2 = SEMICOLON
    { (P4info.merge info1 info2,
       Declaration.NewType { annotations; name; typ_or_decl = Right decl } ) }
;

(*************************** STATEMENTS *************************)

assignmentOrMethodCallStatement:
| func = lvalue L_PAREN args = argumentList R_PAREN info2 = SEMICOLON
    { let type_args = [] in
      (P4info.merge (Surface.info func) info2,
       Statement.MethodCall { func; type_args; args }) }
| func = lvalue L_ANGLE type_args = typeArgumentList r_angle
    L_PAREN args = argumentList R_PAREN info2 = SEMICOLON
    { (P4info.merge (Surface.info func) info2,
       Statement.MethodCall { func; type_args; args }) }
| lhs = lvalue ASSIGN rhs = expression info2 = SEMICOLON
    { (P4info.merge (Surface.info lhs) info2,
      Statement.Assignment { lhs; rhs }) }
;

emptyStatement:
| info = SEMICOLON { (info, Statement.EmptyStatement) }
;

returnStatement:
| info1 = RETURN info2 = SEMICOLON
    { (P4info.merge info1 info2,
       Statement.Return { expr = None }) }
| info1 = RETURN expr = expression info2 = SEMICOLON
    { (P4info.merge info1 info2,
       Statement.Return { expr = Some expr }) }
;

exitStatement:
| info1 = EXIT info2 = SEMICOLON
    { (P4info.merge info1 info2,
       Statement.Exit) }
;

conditionalStatement:
| info1 = IF L_PAREN cond = expression R_PAREN tru = statement ELSE fls = statement
    { let info2 = info fls in
      let fls = Some fls in
      (P4info.merge info1 info2,
       Statement.Conditional { cond; tru; fls }) }
| info1 = IF L_PAREN cond = expression R_PAREN tru = statement   %prec THEN
    { let fls = None in
      (P4info.merge info1 (Surface.info tru),
       Statement.Conditional { cond; tru; fls }) }
;

(* To support direct invocation of a control or parser without instantiation *)
directApplication:
| typ = typeName DOT APPLY L_PAREN args = argumentList R_PAREN info2 = SEMICOLON
    { (P4info.merge (Surface.info typ) info2,
      Statement.DirectApplication { typ; args }) }
;

statement:
| s = assignmentOrMethodCallStatement
| s = directApplication
| s = conditionalStatement
| s = emptyStatement
| s = exitStatement
| s = returnStatement
| s = switchStatement
    { s }
| block = blockStatement
    { (Surface.info block, Statement.BlockStatement { block }) }
;

blockStatement:
|  annotations = optAnnotations
     info1 = L_BRACE
     push_scope
     statements = list(statementOrDeclaration) info2 = R_BRACE
     pop_scope
     { (P4info.merge info1 info2,
       Block.{ annotations; statements }) }
;

switchStatement:
| info1 = SWITCH L_PAREN expr = expression R_PAREN L_BRACE cases = switchCases
  info2 = R_BRACE
    { (P4info.merge info1 info2,
       Statement.Switch { expr; cases }) }
;

switchCases : cases = list(switchCase) { cases } ;

switchCase:
| label = switchLabel COLON code = blockStatement
    { (P4info.merge (Surface.info label) (Surface.info code), Statement.Action { label; code } ) }
| label = switchLabel info2 = COLON
    { (P4info.merge (Surface.info label) info2, Statement.FallThrough { label }) }
;

switchLabel:
| name = name
  { (name.tags, Statement.Name name) }
| info = DEFAULT
  { (info, Statement.Default) }
;

statementOrDeclaration:
| decl = variableDeclaration
| decl = constantDeclaration
| decl = instantiation
  { (Surface.info decl, Statement.DeclarationStatement { decl = decl }) }
| s = statement
  { s }
;

(************ TABLES *************)
tableDeclaration:
|  annotations = optAnnotations
     info1 = TABLE name = name L_BRACE properties = tablePropertyList
     info2 = R_BRACE
     { (P4info.merge info1 info2,
        Declaration.Table { annotations; name; properties }) }
;

tablePropertyList:
| props = nonempty_list(tableProperty) { props }
;

tableProperty:
| info1 = KEY ASSIGN L_BRACE elts = keyElementList info2 = R_BRACE
    { (P4info.merge info1 info2,
       Table.Key { keys = elts }) }
| info1 = ACTIONS ASSIGN L_BRACE acts = actionList info2 = R_BRACE
    { (P4info.merge info1 info2,
       Table.Actions { actions = acts }) }
| info1 = CONST ENTRIES ASSIGN L_BRACE entries = entriesList info2 = R_BRACE
    { (P4info.merge info1 info2,
       Table.Entries { entries = entries }) }
| annos = optAnnotations
    info1 = CONST n = nonTableKwName ASSIGN v = initialValue info2 = SEMICOLON
    { (P4info.merge info1 info2,
       Table.Custom { annotations = annos; const = true; name = n; value = v }) }
| annos = optAnnotations
    n = nonTableKwName ASSIGN v = initialValue info2 = SEMICOLON
    { (P4info.merge n.tags info2,
       Table.Custom { annotations = annos; const = false; name = n; value = v }) }
;

keyElementList: elts = list(keyElement) { elts } ;

keyElement:
| key = expression COLON match_kind = name annotations = optAnnotations
    info2 = SEMICOLON
    { (P4info.merge (Surface.info key) info2,
       Table.{ annotations; key; match_kind }) }
;

actionList:
| (* empty *)
  { [] }
| acts = separated_nonempty_list_aux(SEMICOLON, actionRef) SEMICOLON
    { List.rev acts }
;

entriesList:
| entries = list(entry) { entries }
;

entry:
| matches = keysetExpression
    info1 = COLON act = actionRef annos = optAnnotations info2 = SEMICOLON
    { let info = P4info.merge info1 info2 in
      (info, Table.{ annotations = annos; matches = matches; action = act }) }
;

actionRef:
|  annotations = optAnnotations name = name
     { (name.tags, { annotations; name = BareName name; args = [] }) : Table.action_ref }
|  annotations = optAnnotations name = name L_PAREN args = argumentList
     info2 = R_PAREN
     { (P4info.merge name.tags info2,
        { annotations; name = BareName name; args }) : Table.action_ref }
|  annotations = optAnnotations
   info1 = dotPrefix go_toplevel name = nonTypeName go_local
     { (name.tags, { annotations; name = QualifiedName ([], name); args = [] }) : Table.action_ref }
|  annotations = optAnnotations 
   info1 = dotPrefix go_toplevel name = nonTypeName go_local
   L_PAREN args = argumentList info2 = R_PAREN
     { (P4info.merge name.tags info2,
        { annotations; name = QualifiedName ([], name); args }) : Table.action_ref }
;

(************************* ACTION ********************************)

actionDeclaration:
|  annotations = optAnnotations
     info1 = ACTION name = name L_PAREN params = parameterList R_PAREN
     body = blockStatement
     { (P4info.merge info1 (Surface.info body),
        Declaration.Action { annotations; name; params; body }) }
;

(************************* VARIABLES *****************************)

variableDeclaration:
| annotations = optAnnotations
    typ = typeRef name = name init = optInitialValue info2 = SEMICOLON
    { declare_var name;
      (P4info.merge (Surface.info typ) info2,
       Declaration.Variable { annotations; typ; name; init }) }
;

constantDeclaration:
| annotations = optAnnotations
    info1 = CONST typ = typeRef name = name ASSIGN value = initialValue
    info2 = SEMICOLON
    { (P4info.merge info1 info2,
       Declaration.Constant { annotations; typ; name; value }) }
;

optInitialValue:
| (* empty *) { None }
| ASSIGN v = initialValue { Some v }
;

initialValue:
| v = expression { v }
;

(************************* Expressions ****************************)

functionDeclaration:
| func = functionPrototype body = blockStatement pop_scope
    { let (info1, return, name, type_params, params) = func in
      (P4info.merge info1 (Surface.info body),
       Declaration.Function { return; name; type_params; params; body }) }
;

argumentList: args = separated_list(COMMA, argument) { args } ;

argument:
| value = expression
    { (Surface.info value, Argument.Expression { value }) }
| key = name ASSIGN value = expression
    { (P4info.merge key.tags (Surface.info value),
       Argument.KeyValue { key; value }) }
| info = DONTCARE
    { (info, Argument.Missing) }
;

%inline kvPair:
| key = name ASSIGN value = expression 
  { (P4info.merge key.tags (Surface.info value),
     KeyValue.{ key; value }) }

kvList:
| kvs = separated_nonempty_list(COMMA, kvPair)
  { kvs }
;

expressionList:
| exprs = separated_list(COMMA, expression) 
  { exprs }
;

member:
| n = name { n }
;

prefixedNonTypeName:
| name = nonTypeName
  { (name.tags, Expression.Name (BareName name)) }
| info1 = dotPrefix go_toplevel name = nonTypeName go_local
  { (P4info.merge info1 name.tags,
     Expression.Name (QualifiedName ([], name))) }
;

lvalue:
| expr = prefixedNonTypeName { expr }
| expr = lvalue DOT name = member
    { (P4info.merge (Surface.info expr) name.tags,
       Expression.ExpressionMember { expr; name }) }
| array = lvalue L_BRACKET index = expression info2 = R_BRACKET
    { (P4info.merge (Surface.info array) info2,
       Expression.ArrayAccess { array; index }) }
| bits = lvalue L_BRACKET hi = expression COLON lo = expression
    info2 = R_BRACKET
    { (P4info.merge (Surface.info bits) info2,
       Expression.BitStringAccess { bits; lo; hi }) }
;

expression:
| value = INTEGER
  { let value_int: P4int.t = fst value in 
    let info = value_int.tags in 
    (info, Expression.Int value_int) }
| info1 = TRUE
  { (info1, Expression.True) }
| info1 = FALSE
  { (info1, Expression.False) }
| value = STRING_LITERAL
  { (value.tags, Expression.String value) }
| name = nonTypeName
  { (name.tags, Expression.Name (BareName name)) }
| info1 = dotPrefix go_toplevel name = nonTypeName go_local
  { (P4info.merge info1 name.tags, Expression.Name (QualifiedName ([], name))) }
| array = expression L_BRACKET index = expression info2 = R_BRACKET
  { (P4info.merge (Surface.info array) info2,
     Expression.ArrayAccess { array; index }) }
| bits = expression L_BRACKET hi = expression COLON lo = expression
    info2 = R_BRACKET
  { (P4info.merge (Surface.info bits) info2,
     Expression.BitStringAccess { bits; lo; hi }) }
| info1 = L_BRACE values = expressionList info2 = R_BRACE
  { (P4info.merge info1 info2,
     Expression.List { values }) }
| info1 = L_BRACE entries = kvList info2 = R_BRACE 
  { (P4info.merge info1 info2, 
     Expression.Record { entries }) }
| L_PAREN exp = expression R_PAREN
  { exp }
| info1 = NOT arg = expression %prec PREFIX
  { (P4info.merge info1 (Surface.info arg),
     Expression.UnaryOp { op = (info1, Op.Not); arg }) }
| info1 = COMPLEMENT arg = expression %prec PREFIX
  { (P4info.merge info1 (Surface.info arg),
     Expression.UnaryOp{op = (info1, Op.BitNot); arg }) }
| info1 = MINUS arg = expression %prec PREFIX
  { (P4info.merge info1 (Surface.info arg),
     Expression.UnaryOp{op = (info1, UMinus); arg }) }
| info1 = PLUS exp = expression %prec PREFIX
  { let info2,exp = exp in
    (P4info.merge info1 info2, exp) }
| info1 = L_PAREN typ = typeRef R_PAREN expr = expression %prec PREFIX
  { (P4info.merge info1 (Surface.info expr),
     Expression.Cast { typ; expr }) }
| typ = prefixedTypeName DOT name = member
  { (name.tags,
     Expression.TypeMember { typ; name }) }
| info1 = ERROR DOT name = member
  { (P4info.merge info1 name.tags,
     Expression.ErrorMember name) }
| expr = expression DOT name = member
  { (P4info.merge (Surface.info expr) name.tags,
     Expression.ExpressionMember { expr; name }) }
| arg1 = expression op = binop arg2 = expression
  { (P4info.merge (Surface.info arg1) (Surface.info arg2),
     Expression.BinaryOp { op; args = (arg1, arg2) }) }
| cond = expression QUESTION tru = expression COLON fls = expression
   { (P4info.merge (Surface.info cond) (Surface.info fls),
      Expression.Ternary { cond; tru; fls }) }
| func = expression L_ANGLE type_args = realTypeArgumentList r_angle
    L_PAREN args = argumentList info2 = R_PAREN
   { (P4info.merge (Surface.info func) info2,
      Expression.FunctionCall { func; type_args; args }) }
| func = expression L_PAREN args = argumentList info2 = R_PAREN
   { let type_args = [] in
     (P4info.merge (Surface.info func) info2,
      Expression.FunctionCall { func; type_args; args }) }
| typ = namedType L_PAREN args = argumentList info2 = R_PAREN
   { (P4info.merge (Surface.info typ) info2,
      Expression.NamelessInstantiation { typ; args }) }
;

%inline binop:
| info = MUL
    { (info, Op.Mul) }
| info = DIV
    { (info, Op.Div) }
| info = MOD
    { (info, Op.Mod) }
| info = PLUS
    { (info, Op.Plus) }
| info = PLUS_SAT
    { (info, Op.PlusSat)}
| info = MINUS
    { (info, Op.Minus) }
| info = MINUS_SAT
    { (info, Op.MinusSat) }
| info = SHL
    { (info, Op.Shl) }
| info_r = r_angle info2 = R_ANGLE_SHIFT
    { (P4info.merge info_r info2, Op.Shr) }
| info = LE
    { (info, Op.Le) }
| info = GE
    { (info, Op.Ge) }
| info = L_ANGLE
    { (info, Op.Lt) }
| info_r = r_angle
    { (info_r, Op.Gt) }
| info = NE
    { (info, Op.NotEq) }
| info = EQ
    { (info, Op.Eq) }
| info = BIT_AND
    { (info, Op.BitAnd) }
| info = BIT_XOR
    { (info, Op.BitXor) }
| info = BIT_OR
    { (info, Op.BitOr) }
| info = PLUSPLUS
    { (info, Op.PlusPlus) }
| info = AND
    { (info, Op.And) }
| info = OR
    { (info, Op.Or) }
;

%inline r_angle:
| info_r = R_ANGLE { info_r } 
| info_r = R_ANGLE_SHIFT { info_r }

(* À jour avec le commit 45df9f41a2cf1af56f4fa1cfaa1f586adefd13b7
   de p4-spec; à dotPrefix et listes près *)
