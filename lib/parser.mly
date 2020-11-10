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
module P4Info = Info

open Core_kernel
open Context
open Types

module Info = P4Info

let declare_vars vars = List.iter vars ~f:declare_var
let declare_types types = List.iter types ~f:declare_type

let rec smash_annotations l tok2 =
  match l with 
  | [] ->
     [tok2]
  | [tok1] ->
     let i1,str1 = tok1 in
     let i2,str2 = tok2 in
     Printf.printf "SMASH[%b] \n%s [%s]\n%s [%s]\n\n" (Info.follows i1 i2) (Info.to_string i1) str1 (Info.to_string i2) str2;
     if Info.follows i1 i2 then
       [(Info.merge i1 i2, str1 ^ str2)]
     else
       [tok1; tok2]
  | h::t -> h::smash_annotations t tok2

%}

(*************************** TOKENS *******************************)
%token<Info.t> END
%token TYPENAME IDENTIFIER
%token<Types.P4String.t> NAME STRING_LITERAL
%token<Types.P4Int.t * string> INTEGER
%token<Info.t> LE GE SHL AND OR NE EQ
%token<Info.t> PLUS MINUS PLUS_SAT MINUS_SAT MUL DIV MOD
%token<Info.t> BIT_OR BIT_AND BIT_XOR COMPLEMENT
%token<Info.t> L_BRACKET R_BRACKET L_BRACE R_BRACE L_ANGLE R_ANGLE R_ANGLE_SHIFT L_PAREN R_PAREN
%token<Info.t> ASSIGN COLON COMMA QUESTION DOT NOT SEMICOLON
%token<Info.t> AT PLUSPLUS
%token<Info.t> DONTCARE
%token<Info.t> MASK RANGE
%token<Info.t> TRUE FALSE
%token<Info.t> ABSTRACT ACTION ACTIONS APPLY BOOL BIT CONST CONTROL DEFAULT
%token<Info.t> ELSE ENTRIES ENUM ERROR EXIT EXTERN HEADER HEADER_UNION IF IN INOUT
%token<Info.t> INT KEY SELECT MATCH_KIND OUT PACKAGE PARSER RETURN STATE STRING STRUCT
%token<Info.t> SWITCH TABLE THEN TRANSITION TUPLE TYPE TYPEDEF VARBIT VALUESET VOID
%token<Info.t> PRAGMA PRAGMA_END
%token<Types.P4String.t> UNEXPECTED_TOKEN

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


%start <Types.program> p4program
%start <Types.Declaration.t> variableDeclaration
%start <Types.Declaration.t> typeDeclaration

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
    {List.rev rev_list}
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
| info = KEY { (info, "key") }
| info = ACTIONS { (info, "actions") }
| info = ENTRIES { (info, "entries") }
;

nonTableKwName:
| n = varName { n }
| n = NAME TYPENAME { n }
| info = APPLY { (info, "apply") }
| info = STATE { (info, "state") }
| info = TYPE { (info, "type") }
;

nonTypeName:
| n = varName { n }
| n = tableKwName { n }
| info = APPLY { (info, "apply") }
| info = STATE { (info, "state") }
| info = TYPE { (info, "type") }
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
    { let info2 = info name in
      let body = (info2, Annotation.Empty) in 
      (Info.merge info1 info2,
       Annotation.{ name; body } ) }

| info1 = AT name = name info2 = L_PAREN body = annotationBody info3 = R_PAREN
    { let body = (Info.merge info2 info3, Annotation.Unparsed(body)) in
      (Info.merge info1 info3, 
       Annotation.{ name; body }) }

| info1 = AT name = name info2 = L_BRACKET body = expressionList info3 = R_BRACKET
    { let body = (Info.merge info2 info3, Annotation.Expression(body)) in
      (Info.merge info1 info3, 
       Annotation.{ name; body }) }

| info1 = AT name = name info2 = L_BRACKET body = kvList info3 = R_BRACKET
    { let body = (Info.merge info2 info3, Annotation.KeyValue(body)) in
      (Info.merge info1 info3,
       Annotation.{ name; body }) }

| info1 = PRAGMA name = name body = annotationBody info2 = PRAGMA_END
    { let body = (Info.merge info2 info2, Annotation.Unparsed(body)) in
       (Info.merge info1 info2, 
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
| ABSTRACT         { ($1, "abstract") }
| ACTION           { ($1, "action") }
| ACTIONS          { ($1, "actions") }
| APPLY            { ($1, "apply") }
| BOOL             { ($1, "bool") }
| BIT              { ($1, "bit") }
| CONST            { ($1, "const") }
| CONTROL          { ($1, "control") }
| DEFAULT          { ($1, "default") }
| ELSE             { ($1, "else") }
| ENTRIES          { ($1, "entries") }
| ENUM             { ($1, "enum") }
| ERROR            { ($1, "error") }
| EXIT             { ($1, "exit") }
| EXTERN           { ($1, "extern") }
| FALSE            { ($1, "false") }
| HEADER           { ($1, "header") }
| HEADER_UNION     { ($1, "header_union") }
| IF               { ($1, "if") }
| IN               { ($1, "in") }
| INOUT            { ($1, "inout") }
| INT              { ($1, "int") }
| KEY              { ($1, "key") }
| MATCH_KIND       { ($1, "match_kind") }
| TYPE             { ($1, "type") }
| OUT              { ($1, "out") }
| PARSER           { ($1, "parser") }
| PACKAGE          { ($1, "package") }
| PRAGMA           { ($1, "pragma") }
| RETURN           { ($1, "return") }
| SELECT           { ($1, "select") }
| STATE            { ($1, "state") }
| STRING           { ($1, "string") }
| STRUCT           { ($1, "struct") }
| SWITCH           { ($1, "switch") }
| TABLE            { ($1, "table") }
(* | THIS             { ($1, "this") } *)
| TRANSITION       { ($1, "transition") }
| TRUE             { ($1, "true") }
| TUPLE            { ($1, "tuple") }
| TYPEDEF          { ($1, "typedef") }
| VARBIT           { ($1, "varbit") }
| VALUESET         { ($1, "valueset") }
| VOID             { ($1, "void") }
| DONTCARE         { ($1, "_") }
| NAME IDENTIFIER  { $1 }
| NAME TYPENAME    { $1 }
| STRING_LITERAL   { let info, str = $1 in
                     (info, "\"" ^ str ^ "\"") }
| INTEGER          { let (info,_), str = $1 in 
                     (info, str) }
| MASK             { ($1, "&&&") }
| RANGE            { ($1, "..") }
| SHL              { ($1, "<<") }
| AND              { ($1, "&&") }
| OR               { ($1, "||") }
| EQ               { ($1, "==") }
| NE               { ($1, "!=") }
| GE               { ($1, ">=") }
| LE               { ($1, "<=") }
| PLUSPLUS         { ($1, "++") }
| PLUS             { ($1, "+") }
| PLUS_SAT         { ($1, "|+|") }
| MINUS            { ($1, "-") }
| MINUS_SAT        { ($1, "|-|") }
| MUL              { ($1, "*") }
| DIV              { ($1, "/") }
| MOD              { ($1, "%") }
| BIT_OR           { ($1, "|") }
| BIT_AND          { ($1, "&") }
| BIT_XOR          { ($1, "^") }
| COMPLEMENT       { ($1, "~") }
| L_BRACKET        { ($1, "[") }
| R_BRACKET        { ($1, "]") }
| L_BRACE          { ($1, "{") }
| R_BRACE          { ($1, "}") }
| L_ANGLE          { ($1, "<") }
| R_ANGLE          { ($1, ">") }
| NOT              { ($1, "!") }
| COLON            { ($1, ":") }
| COMMA            { ($1, ",") }
| QUESTION         { ($1, "?") }
| DOT              { ($1, ".") }
| ASSIGN           { ($1, "=") }
| SEMICOLON        { ($1, ";") }
| AT               { ($1, "@") }
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
      (Info.merge info1 (info variable),
       Parameter.{ annotations; direction; typ; variable; opt_value = None }) }
| annotations = optAnnotations direction = direction typ = typeRef variable = name
   ASSIGN value = expression
    { let info1 =
        match direction with
        | None -> info typ
        | Some dir -> info dir in
      (Info.merge info1 (info variable),
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
     {  (Info.merge info1 info2,
        Declaration.PackageType { annotations; name; type_params; params }) }
;

instantiation:
| annotations = optAnnotations typ = typeRef
    L_PAREN args = argumentList R_PAREN name = name info2 = SEMICOLON
    { (Info.merge (info typ) info2,
       Declaration.Instantiation { annotations; typ; args; name; init=None }) }
| annotations = optAnnotations typ = typeRef
    L_PAREN args = argumentList R_PAREN name = name ASSIGN init = objInitializer info2 = SEMICOLON
    { (Info.merge (info typ) info2,
       Declaration.Instantiation { annotations; typ; args; name; init=Some init }) }
;

objInitializer:
| L_BRACE statements = list(objDeclaration) R_BRACE 
  { (Info.merge $1 $3, Block.{ annotations = []; statements }) }
;

objDeclaration:
| decl = functionDeclaration
  { (info decl, Statement.DeclarationStatement { decl }) }
| decl = instantiation 
  { (info decl, Statement.DeclarationStatement { decl }) }
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
    { let open Declaration in
      let (info1, annotations, name, type_params, params) = p_type in
      let info = Info.merge info1 info2 in
      let locals = List.rev locals in
      (info, Parser { annotations; name; type_params; params; constructor_params; locals; states }) }
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
    { let info = Info.merge info1 info2 in
      (info, annotations, name, type_params, params) }
;

parserState:
|  annotations = optAnnotations info1 = STATE
     name = push_name
       L_BRACE
       statements = list(parserStatement) transition = transitionStatement
       info2 = R_BRACE
     pop_scope
     { (Info.merge info1 info2, Parser.{ annotations; name; statements; transition }) }

;

parserStatement:
| s = assignmentOrMethodCallStatement
| s = directApplication
| s = emptyStatement
| s = parserBlockStatement
   { s }
| decl = constantDeclaration
| decl = variableDeclaration
  { (info decl, Statement.DeclarationStatement { decl }) }
;

parserBlockStatement:
|  annotations = optAnnotations
     info1 = L_BRACE statements = list(parserStatement) info2 = R_BRACE
     { let info = Info.merge info1 info2 in
       let block = (info, Block.{ annotations; statements }) in
       (info, Statement.BlockStatement { block = block }) }
;

transitionStatement:
| (* empty *)
  { let info = Info.M "Compiler-generated reject transition" in
    (info, Parser.Direct { next = (info, "reject") }) }

| info1 = TRANSITION transition = stateExpression
    { (Info.merge info1 (info transition),
       snd transition) }
;

stateExpression:
| next = name info2 = SEMICOLON
    { (Info.merge (info next) info2,
       Parser.Direct { next = next }) }
| select = selectExpression
    { select }
;

selectExpression:
| info1 = SELECT L_PAREN exprs = expressionList R_PAREN
    L_BRACE cases = list(selectCase) info2 = R_BRACE
    { (Info.merge info1 info2,
       Parser.Select { exprs; cases }) }
;

selectCase:
| matches = keysetExpression COLON next = name info2 = SEMICOLON
  { let info1 = match matches with
      | expr::_ -> info expr
      | _ -> assert false in
    (Info.merge info1 info2,
     Parser.{ matches; next }) }
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
| expr = expression { (info expr, Match.Expression { expr }) }
| info = DONTCARE { (info, Match.DontCare) }
| info = DEFAULT { (info, Match.Default) }
| expr = expression MASK mask = expression
    { let info = Info.merge (info expr) (info mask) in
      (info, Match.Expression { expr = (info, Expression.Mask { expr; mask }) }) }
| lo = expression RANGE hi = expression
    { let info = Info.merge (info lo) (info hi) in
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
    { (Info.merge info1 info2,
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
      (Info.merge info1 info2,
       Declaration.Control { annotations; name; type_params; params; constructor_params;
                             locals; apply } ) }
;

controlTypeDeclaration:
|  annotations = optAnnotations info1 = CONTROL
     name = push_name
     type_params = optTypeParameters
     L_PAREN params = parameterList info2 = R_PAREN
     { (Info.merge info1 info2, annotations, name, type_params, params) }
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
         (Info.merge info1 info2,
          (Declaration.ExternObject { annotations; name; type_params; methods })) in
       declare_type (Declaration.name type_decl);
       type_decl }
|  annotations = optAnnotations info1 = EXTERN
     func = functionPrototype pop_scope info2 = SEMICOLON
     { let (_, return, name, type_params, params) = func in
       let decl =
         (Info.merge info1 info2,
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
    { (Info.merge (info typ) info2, typ, name, type_params, params) }
;

methodPrototype:
| annotations = optAnnotations
  func = functionPrototype pop_scope info2 = SEMICOLON
    { let (info1, return, name, type_params, params) = func in
      (Info.merge info1 info2,
       MethodPrototype.Method { annotations; return; name; type_params; params }) }

| annotations = optAnnotations
  ABSTRACT
  func = functionPrototype pop_scope info2 = SEMICOLON
    { let (info1, return, name, type_params, params) = func in
      (Info.merge info1 info2,
       MethodPrototype.AbstractMethod { annotations; return; name; type_params; params }) }
| annotations = optAnnotations
  name = name (* NAME TYPENAME *)
    L_PAREN params = parameterList R_PAREN info2 = SEMICOLON
    { (Info.merge (info name) info2,
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
    { name_info name, Type.TypeName name }

typeName:
| typ = prefixedType
    { typ }
;

tupleType:
| info1 = TUPLE L_ANGLE elements = typeArgumentList info_r = r_angle
    { (Info.merge info1 info_r,
       Type.Tuple elements) }
;

headerStackType:
| header = typeName L_BRACKET size = expression info2 = R_BRACKET
    { (Info.merge (info header) info2,
       Type.HeaderStack { header; size }) }
;

specializedType:
| base = prefixedType L_ANGLE args = typeArgumentList info_r = r_angle
    { (Info.merge (info base) info_r,
      Type.SpecializedType { base; args }) }
;

baseType:
| info = BOOL
    { (info, Type.Bool) }
| info = ERROR
    { (info, Type.Error) }
| info = BIT
    { let width = (info, Expression.Int (info, { value = Bigint.of_int 1;
                                                 width_signed = None })) in
      (info, Type.BitType width) }
| info1 = BIT L_ANGLE value = INTEGER info_r = r_angle
    { let value_int = fst value in 
      let value_info = fst value_int in
      let width = (value_info, Expression.Int value_int) in
      let info = Info.merge info1 info_r in
      (info, Type.BitType width) }
| info1 = INT L_ANGLE value = INTEGER info_r = r_angle
     { let value_int = fst value in 
       let value_info = fst value_int in 
       let width = (value_info, Expression.Int value_int) in
       let info = Info.merge info1 info_r in
      (info, Type.IntType width) }

| info1 = VARBIT L_ANGLE value = INTEGER info_r = r_angle
     { let value_int = fst value in 
       let value_info = fst value_int in
       let max_width = (value_info, Expression.Int value_int) in
       let info = Info.merge info1 info_r in
      (info, Type.VarBit max_width) }
| info1 = BIT L_ANGLE L_PAREN width = expression R_PAREN info_r = r_angle
    { (Info.merge info1 info_r,
       Type.BitType width) }
| info1 = INT L_ANGLE L_PAREN width = expression R_PAREN info_r = r_angle
    { (Info.merge info1 info_r,
       Type.IntType width) }
| info1 = VARBIT L_ANGLE L_PAREN max_width = expression R_PAREN info_r = r_angle
    { (Info.merge info1 info_r,
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
  { (info name, Type.TypeName (BareName name)) }    (* may be a type variable *)
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
| name = nonTypeName { (info name, Type.TypeName (BareName name)) }
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
     { (Info.merge info1 info2,
        Declaration.Header { annotations; name; fields }) }
;

headerUnionDeclaration:
|  annotations = optAnnotations info1 = HEADER_UNION name = name
     L_BRACE fields = list(structField) info2 = R_BRACE
     { (Info.merge info1 info2,
        Declaration.HeaderUnion { annotations; name; fields }) }
;

structTypeDeclaration:
|  annotations = optAnnotations info1 = STRUCT name = name
     L_BRACE fields = list(structField) info2 = R_BRACE
     { (Info.merge info1 info2,
        Declaration.Struct { annotations; name; fields }) }
;

structField:
|  annotations = optAnnotations typ = typeRef name = name info2 = SEMICOLON
     { (Info.merge (info typ) info2,
        { annotations; typ; name }) }
;

(* TODO : add support for serializable enums *)
enumDeclaration:
| annotations = optAnnotations info1 = ENUM name = name
    L_BRACE members = identifierList info2 = R_BRACE
    { (Info.merge info1 info2,
      Declaration.Enum { annotations; name; members }) }
| annotations = optAnnotations info1 = ENUM info2 = BIT L_ANGLE value = INTEGER r_angle
    name = name L_BRACE members = specifiedIdentifierList info4 = R_BRACE
   { let value_int = fst value in 
     let value_info = fst value_int in 
     let width = (value_info, Expression.Int value_int) in
     let typ = (Info.merge info2 info4, Type.BitType width) in
     (Info.merge info1 info4,
      Declaration.SerializableEnum { annotations; typ; name; members }) }
;

errorDeclaration:
| info1 = ERROR L_BRACE members = identifierList info2 = R_BRACE
    { declare_vars members;
      (Info.merge info1 info2,
       Declaration.Error { members }) }
;

matchKindDeclaration:
| info1 = MATCH_KIND L_BRACE members = identifierList info2 = R_BRACE
    { declare_vars members;
      (Info.merge info1 info2,
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
    { (Info.merge info1 info2,
       Declaration.TypeDef { annotations; name; typ_or_decl = Left typ } ) }
| annotations = optAnnotations info1 = TYPEDEF
    decl = derivedTypeDeclaration name = name info2 = SEMICOLON
    { (Info.merge info1 info2,
       Declaration.TypeDef { annotations; name; typ_or_decl = Right decl } ) }
| annotations = optAnnotations info1 = TYPE
    typ = typeRef name = name info2 = SEMICOLON
    { (Info.merge info1 info2,
       Declaration.NewType { annotations; name; typ_or_decl = Left typ } ) }
| annotations = optAnnotations info1 = TYPE
    decl = derivedTypeDeclaration name = name info2 = SEMICOLON
    { (Info.merge info1 info2,
       Declaration.NewType { annotations; name; typ_or_decl = Right decl } ) }
;

(*************************** STATEMENTS *************************)

assignmentOrMethodCallStatement:
| func = lvalue L_PAREN args = argumentList R_PAREN info2 = SEMICOLON
    { let type_args = [] in
      (Info.merge (info func) info2,
       Statement.MethodCall { func; type_args; args }) }
| func = lvalue L_ANGLE type_args = typeArgumentList r_angle
    L_PAREN args = argumentList R_PAREN info2 = SEMICOLON
    { (Info.merge (info func) info2,
       Statement.MethodCall { func; type_args; args }) }
| lhs = lvalue ASSIGN rhs = expression info2 = SEMICOLON
    { (Info.merge (info lhs) info2,
      Statement.Assignment { lhs; rhs }) }
;

emptyStatement:
| info = SEMICOLON { (info, Statement.EmptyStatement) }
;

returnStatement:
| info1 = RETURN info2 = SEMICOLON
    { (Info.merge info1 info2,
       Statement.Return { expr = None }) }
| info1 = RETURN expr = expression info2 = SEMICOLON
    { (Info.merge info1 info2,
       Statement.Return { expr = Some expr }) }
;

exitStatement:
| info1 = EXIT info2 = SEMICOLON
    { (Info.merge info1 info2,
       Statement.Exit) }
;

conditionalStatement:
| info1 = IF L_PAREN cond = expression R_PAREN tru = statement ELSE fls = statement
    { let info2 = info fls in
      let fls = Some fls in
      (Info.merge info1 info2,
       Statement.Conditional { cond; tru; fls }) }
| info1 = IF L_PAREN cond = expression R_PAREN tru = statement   %prec THEN
    { let fls = None in
      (Info.merge info1 (info tru),
       Statement.Conditional { cond; tru; fls }) }
;

(* To support direct invocation of a control or parser without instantiation *)
directApplication:
| typ = typeName DOT APPLY L_PAREN args = argumentList R_PAREN info2 = SEMICOLON
    { (Info.merge (info typ) info2,
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
    { (info block, Statement.BlockStatement { block }) }
;

blockStatement:
|  annotations = optAnnotations
     info1 = L_BRACE
     push_scope
     statements = list(statementOrDeclaration) info2 = R_BRACE
     pop_scope
     { (Info.merge info1 info2,
       Block.{ annotations; statements }) }
;

switchStatement:
| info1 = SWITCH L_PAREN expr = expression R_PAREN L_BRACE cases = switchCases
  info2 = R_BRACE
    { (Info.merge info1 info2,
       Statement.Switch { expr; cases }) }
;

switchCases : cases = list(switchCase) { cases } ;

switchCase:
| label = switchLabel COLON code = blockStatement
    { (Info.merge (info label) (info code), Statement.Action { label; code } ) }
| label = switchLabel info2 = COLON
    { (Info.merge (info label) info2, Statement.FallThrough { label }) }
;

switchLabel:
| name = name
  { (info name, Statement.Name name) }
| info = DEFAULT
  { (info, Statement.Default) }
;

statementOrDeclaration:
| decl = variableDeclaration
| decl = constantDeclaration
| decl = instantiation
  { (info decl, Statement.DeclarationStatement { decl = decl }) }
| s = statement
  { s }
;

(************ TABLES *************)
tableDeclaration:
|  annotations = optAnnotations
     info1 = TABLE name = name L_BRACE properties = tablePropertyList
     info2 = R_BRACE
     { (Info.merge info1 info2,
        Declaration.Table { annotations; name; properties }) }
;

tablePropertyList:
| props = nonempty_list(tableProperty) { props }
;

tableProperty:
| info1 = KEY ASSIGN L_BRACE elts = keyElementList info2 = R_BRACE
    { (Info.merge info1 info2,
       Table.Key { keys = elts }) }
| info1 = ACTIONS ASSIGN L_BRACE acts = actionList info2 = R_BRACE
    { (Info.merge info1 info2,
       Table.Actions { actions = acts }) }
| info1 = CONST ENTRIES ASSIGN L_BRACE entries = entriesList info2 = R_BRACE
    { (Info.merge info1 info2,
       Table.Entries { entries = entries }) }
| annos = optAnnotations
    info1 = CONST n = nonTableKwName ASSIGN v = initialValue info2 = SEMICOLON
    { (Info.merge info1 info2,
       Table.Custom { annotations = annos; const = true; name = n; value = v }) }
| annos = optAnnotations
    n = nonTableKwName ASSIGN v = initialValue info2 = SEMICOLON
    { (Info.merge (info n) info2,
       Table.Custom { annotations = annos; const = false; name = n; value = v }) }
;

keyElementList: elts = list(keyElement) { elts } ;

keyElement:
| key = expression COLON match_kind = name annotations = optAnnotations
    info2 = SEMICOLON
    { (Info.merge (info key) info2,
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
    { let info = Info.merge info1 info2 in
      (info, Table.{ annotations = annos; matches = matches; action = act }) }
;

actionRef:
|  annotations = optAnnotations name = name
     { (info name, { annotations; name = BareName name; args = [] }) }
|  annotations = optAnnotations name = name L_PAREN args = argumentList
     info2 = R_PAREN
     { (Info.merge (info name) info2,
        { annotations; name = BareName name; args }) }
|  annotations = optAnnotations
   info1 = dotPrefix go_toplevel name = nonTypeName go_local
     { (info name, { annotations; name = QualifiedName ([], name); args = [] }) }
|  annotations = optAnnotations 
   info1 = dotPrefix go_toplevel name = nonTypeName go_local
   L_PAREN args = argumentList info2 = R_PAREN
     { (Info.merge (info name) info2,
        { annotations; name = QualifiedName ([], name); args }) }
;

(************************* ACTION ********************************)

actionDeclaration:
|  annotations = optAnnotations
     info1 = ACTION name = name L_PAREN params = parameterList R_PAREN
     body = blockStatement
     { (Info.merge info1 (info body),
        Declaration.Action { annotations; name; params; body }) }
;

(************************* VARIABLES *****************************)

variableDeclaration:
| annotations = optAnnotations
    typ = typeRef name = name init = optInitialValue info2 = SEMICOLON
    { declare_var name;
      (Info.merge (info typ) info2,
       Declaration.Variable { annotations; typ; name; init }) }
;

constantDeclaration:
| annotations = optAnnotations
    info1 = CONST typ = typeRef name = name ASSIGN value = initialValue
    info2 = SEMICOLON
    { (Info.merge info1 info2,
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
      (Info.merge info1 (info body),
       Declaration.Function { return; name; type_params; params; body }) }
;

argumentList: args = separated_list(COMMA, argument) { args } ;

argument:
| value = expression
    { (info value, Argument.Expression { value }) }
| key = name ASSIGN value = expression
    { (Info.merge (info key) (info value),
       Argument.KeyValue { key; value }) }
| info = DONTCARE
    { (info, Argument.Missing) }
;

%inline kvPair:
| key = name ASSIGN value = expression 
  { (Info.merge (info key) (info value),
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
  { (info name, Expression.Name (BareName name)) }
| info1 = dotPrefix go_toplevel name = nonTypeName go_local
  { (Info.merge info1 (info name),
     Expression.Name (QualifiedName ([], name))) }
;

lvalue:
| expr = prefixedNonTypeName { expr }
| expr = lvalue DOT name = member
  { (Info.merge (info expr) (info name),
     Expression.ExpressionMember { expr; name }) }
| array = lvalue L_BRACKET index = expression info2 = R_BRACKET
    { (Info.merge (info array) info2,
       Expression.ArrayAccess { array; index }) }
| bits = lvalue L_BRACKET hi = expression COLON lo = expression
    info2 = R_BRACKET
    { (Info.merge (info bits) info2,
       Expression.BitStringAccess { bits; lo; hi }) }
;

expression:
| value = INTEGER
  { let value_int = fst value in 
    let info = fst value_int in 
    (info, Expression.Int value_int) }
| info1 = TRUE
  { (info1, Expression.True) }
| info1 = FALSE
  { (info1, Expression.False) }
| value = STRING_LITERAL
  { (fst value, Expression.String value) }
| name = nonTypeName
  { (info name, Expression.Name (BareName name)) }
| info1 = dotPrefix go_toplevel name = nonTypeName go_local
  { (Info.merge info1 (fst name), Expression.Name (QualifiedName ([], name))) }
| array = expression L_BRACKET index = expression info2 = R_BRACKET
  { (Info.merge (info array) info2,
     Expression.ArrayAccess { array; index }) }
| bits = expression L_BRACKET hi = expression COLON lo = expression
    info2 = R_BRACKET
  { (Info.merge (info bits) info2,
     Expression.BitStringAccess { bits; lo; hi }) }
| info1 = L_BRACE values = expressionList info2 = R_BRACE
  { (Info.merge info1 info2,
     Expression.List { values }) }
| info1 = L_BRACE entries = kvList info2 = R_BRACE 
  { (Info.merge info1 info2, 
     Expression.Record { entries }) }
| L_PAREN exp = expression R_PAREN
  { exp }
| info1 = NOT arg = expression %prec PREFIX
  { (Info.merge info1 (info arg),
     Expression.UnaryOp { op = (info1, Op.Not); arg }) }
| info1 = COMPLEMENT arg = expression %prec PREFIX
  { (Info.merge info1 (info arg),
     Expression.UnaryOp{op = (info1, Op.BitNot); arg }) }
| info1 = MINUS arg = expression %prec PREFIX
  { (Info.merge info1 (info arg),
     Expression.UnaryOp{op = (info1, UMinus); arg }) }
| info1 = PLUS exp = expression %prec PREFIX
  { let info2,exp = exp in
    (Info.merge info1 info2, exp) }
| info1 = L_PAREN typ = typeRef R_PAREN expr = expression %prec PREFIX
  { (Info.merge info1 (info expr),
     Expression.Cast { typ; expr }) }
| typ = prefixedTypeName DOT name = member
  { (info name,
     Expression.TypeMember { typ; name }) }
| info1 = ERROR DOT name = member
  { (Info.merge info1 (info name),
     Expression.ErrorMember name) }
| expr = expression DOT name = member
  { (Info.merge (info expr) (info name),
     Expression.ExpressionMember { expr; name }) }
| arg1 = expression op = binop arg2 = expression
  { (Info.merge (Types.info arg1) (Types.info arg2),
     Expression.BinaryOp { op; args = (arg1, arg2) }) }
| cond = expression QUESTION tru = expression COLON fls = expression
   { (Info.merge (info cond) (info fls),
      Expression.Ternary { cond; tru; fls }) }
| func = expression L_ANGLE type_args = realTypeArgumentList r_angle
    L_PAREN args = argumentList info2 = R_PAREN
   { (Info.merge (info func) info2,
      Expression.FunctionCall { func; type_args; args }) }
| func = expression L_PAREN args = argumentList info2 = R_PAREN
   { let type_args = [] in
     (Info.merge (info func) info2,
      Expression.FunctionCall { func; type_args; args }) }
| typ = namedType L_PAREN args = argumentList info2 = R_PAREN
   { (Info.merge (info typ) info2,
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
    { (Info.merge info_r info2, Op.Shr) }
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
