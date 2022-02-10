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
open Surface
open Core_kernel
open Context
<<<<<<< HEAD
open Types
=======
open P4string
>>>>>>> 62cd2770 (wip fix menhir build errors)

let declare_vars vars = List.iter vars ~f:declare_var
let declare_types types = List.iter types ~f:declare_type

let rec smash_annotations l tok2 =
  match l with 
  | [] ->
     [tok2]
  | [tok1] ->
<<<<<<< HEAD
     let i1,str1 = tok1 in
     let i2,str2 = tok2 in
     if Info.follows i1 i2 then
       [(Info.merge i1 i2, str1 ^ str2)]
=======
     if P4info.follows tok1.tags tok2.tags then
       [{tags = P4info.merge tok1.tags tok2.tags; str = tok1.str ^ tok2.str}]
>>>>>>> 62cd2770 (wip fix menhir build errors)
     else
       [tok1; tok2]
  | h::t -> h::smash_annotations t tok2

%}

(*************************** TOKENS *******************************)
%token<P4info.t> END
%token TYPENAME IDENTIFIER
<<<<<<< HEAD
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
=======
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
>>>>>>> 62cd2770 (wip fix menhir build errors)

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


<<<<<<< HEAD
%start <Types.program> p4program
%start <Types.Declaration.t> variableDeclaration
%start <Types.Declaration.t> typeDeclaration
=======
%type <Table.action_ref> actionRef
%start <Surface.program> p4program
%start <Surface.Declaration.t> variableDeclaration
%start <Surface.Declaration.t> typeDeclaration
>>>>>>> 62cd2770 (wip fix menhir build errors)

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

<<<<<<< HEAD
p4program : ds = topDeclarationList END { Program(ds) };
=======
p4program : ds = topDeclarationList END { Surface.P4lightram(ds) };
>>>>>>> 62cd2770 (wip fix menhir build errors)

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
    { declare_var (Surface.Declaration.name a);
      a }
| p = parserDeclaration
    { declare_type (Surface.Declaration.name p);
      p }
| c = controlDeclaration
    { declare_type (Surface.Declaration.name c);
      c }
| i = instantiation
    { declare_var (Surface.Declaration.name i);
      i }
| t = typeDeclaration
    { declare_type (Surface.Declaration.name t);
      t }
| e = errorDeclaration
    { (* declare_type (Declaration.name e); *)
      e }
| m = matchKindDeclaration
    { m }
| f = functionDeclaration
    { declare_var (Surface.Declaration.name f);
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
<<<<<<< HEAD
    { let info2 = info name in
      let body = (info2, Annotation.Empty) in 
      (Info.merge info1 info2,
       Annotation.{ name; body } ) }
=======
    { let info2 = name.tags in
      let body = (info2, Surface.Annotation.Empty) in 
      (P4info.merge info1 info2,
       Surface.Annotation.{ name; body } ) }
>>>>>>> 62cd2770 (wip fix menhir build errors)

| info1 = AT name = name info2 = L_PAREN body = annotationBody info3 = R_PAREN
    { let body = (P4info.merge info2 info3, Surface.Annotation.Unparsed(body)) in
      (P4info.merge info1 info3, 
       Surface.Annotation.{ name; body }) }

| info1 = AT name = name info2 = L_BRACKET body = expressionList info3 = R_BRACKET
    { let body = (P4info.merge info2 info3, Surface.Annotation.Expression(body)) in
      (P4info.merge info1 info3, 
       Surface.Annotation.{ name; body }) }

| info1 = AT name = name info2 = L_BRACKET body = kvList info3 = R_BRACKET
    { let body = (P4info.merge info2 info3, Surface.Annotation.KeyValue(body)) in
      (P4info.merge info1 info3,
       Surface.Annotation.{ name; body }) }

| info1 = PRAGMA name = name body = annotationBody info2 = PRAGMA_END
    { let body = (P4info.merge info2 info2, Surface.Annotation.Unparsed(body)) in
       (P4info.merge info1 info2, 
       Surface.Annotation.{ name; body }) }
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
    { let names = List.map ~f:(fun (_,p) -> p.Surface.Parameter.variable) params in
      declare_vars names; params }
;

parameter:
| annotations = optAnnotations direction = direction typ = typeRef variable = name
    { let info1 =
        match direction with
<<<<<<< HEAD
        | None -> info typ
        | Some dir -> info dir in
      (Info.merge info1 (info variable),
=======
        | None -> Surface.info typ
        | Some dir -> Surface.info dir in
      (P4info.merge info1 variable.tags,
>>>>>>> 62cd2770 (wip fix menhir build errors)
       Parameter.{ annotations; direction; typ; variable; opt_value = None }) }
| annotations = optAnnotations direction = direction typ = typeRef variable = name
   ASSIGN value = expression
    { let info1 =
        match direction with
<<<<<<< HEAD
        | None -> info typ
        | Some dir -> info dir in
      (Info.merge info1 (info variable),
=======
        | None -> Surface.info typ
        | Some dir -> Surface.info dir in
      (P4info.merge info1 variable.tags,
>>>>>>> 62cd2770 (wip fix menhir build errors)
       Parameter.{ annotations; direction; typ; variable; opt_value = Some value }) }
;

direction:
| info = IN      { Some (info, Surface.Direction.In) }
| info = OUT     { Some (info, Surface.Direction.Out) }
| info = INOUT   { Some (info, Surface.Direction.InOut) }
| (* empty *)    { None }
;

packageTypeDeclaration:
|  annotations = optAnnotations info1 = PACKAGE
   name = push_name
     type_params = optTypeParameters
     L_PAREN params = parameterList info2 = R_PAREN
     {  (P4info.merge info1 info2,
        Surface.Declaration.PackageType { annotations; name; type_params; params }) }
;

instantiation:
| annotations = optAnnotations typ = typeRef
    L_PAREN args = argumentList R_PAREN name = name info2 = SEMICOLON
    { (P4info.merge (Surface.info typ) info2,
       Surface.Declaration.Instantiation { annotations; typ; args; name; init=None }) }
| annotations = optAnnotations typ = typeRef
    L_PAREN args = argumentList R_PAREN name = name ASSIGN init = objInitializer info2 = SEMICOLON
    { (P4info.merge (Surface.info typ) info2,
       Surface.Declaration.Instantiation { annotations; typ; args; name; init=Some init }) }
;

objInitializer:
| L_BRACE statements = list(objDeclaration) R_BRACE 
  { (P4info.merge $1 $3, Surface.Block.{ annotations = []; statements }) }
;

objDeclaration:
| decl = functionDeclaration
  { (Surface.info decl, Surface.Statement.DeclarationStatement { decl }) }
| decl = instantiation 
  { (Surface.info decl, Surface.Statement.DeclarationStatement { decl }) }
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
      (info, Surface.Declaration.Parser { annotations; name; type_params; params; constructor_params; locals; states }) }
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
  { (Surface.info decl, Surface.Statement.DeclarationStatement { decl }) }
;

parserBlockStatement:
|  annotations = optAnnotations
     info1 = L_BRACE statements = list(parserStatement) info2 = R_BRACE
     { let info = P4info.merge info1 info2 in
       let block = (info, Surface.Block.{ annotations; statements }) in
       (info, Surface.Statement.BlockStatement { block = block }) }
;

transitionStatement:
| (* empty *)
<<<<<<< HEAD
  { let info = Info.M "Compiler-generated reject transition" in
    (info, Parser.Direct { next = (info, "reject") }) }
=======
  { let info = P4info.M "Compiler-generated reject transition" in
    (info, Surface.Parser.Direct { next = {tags=info; str="reject"} }) }
>>>>>>> 62cd2770 (wip fix menhir build errors)

| info1 = TRANSITION transition = stateExpression
    { (P4info.merge info1 (Surface.info transition),
       snd transition) }
;

stateExpression:
| next = name info2 = SEMICOLON
<<<<<<< HEAD
    { (Info.merge (info next) info2,
       Parser.Direct { next = next }) }
=======
    { (P4info.merge next.tags info2,
       Surface.Parser.Direct { next = next }) }
>>>>>>> 62cd2770 (wip fix menhir build errors)
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
      | expr::_ -> Surface.info expr
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
| expr = expression { (Surface.info expr, Surface.Match.Expression { expr }) }
| info = DONTCARE { (info, Surface.Match.DontCare) }
| info = DEFAULT { (info, Surface.Match.Default) }
| expr = expression MASK mask = expression
    { let info = P4info.merge (Surface.info expr) (Surface.info mask) in
      (info, Surface.Match.Expression { expr = (info, Surface.Expression.Mask { expr; mask }) }) }
| lo = expression RANGE hi = expression
    { let info = P4info.merge (Surface.info lo) (Surface.info hi) in
      (info, Surface.Match.Expression {expr = (info, Surface.Expression.Range { lo; hi })})}
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
      Surface.Declaration.ValueSet { annotations; typ; size; name } ) }
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
       Surface.Declaration.Control { annotations; name; type_params; params; constructor_params;
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
    { declare_var (Surface.Declaration.name a); a }
| t = tableDeclaration
    { declare_var (Surface.Declaration.name t); t }
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
          (Surface.Declaration.ExternObject { annotations; name; type_params; methods })) in
       declare_type (Surface.Declaration.name type_decl);
       type_decl }
|  annotations = optAnnotations info1 = EXTERN
     func = functionPrototype pop_scope info2 = SEMICOLON
     { let (_, return, name, type_params, params) = func in
       let decl =
         (P4info.merge info1 info2,
          Surface.Declaration.ExternFunction { annotations; return; name; type_params; params }) in
       declare_var (Surface.Declaration.name decl);
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
       Surface.MethodPrototype.Method { annotations; return; name; type_params; params }) }

| annotations = optAnnotations
  ABSTRACT
  func = functionPrototype pop_scope info2 = SEMICOLON
    { let (info1, return, name, type_params, params) = func in
      (P4info.merge info1 info2,
       Surface.MethodPrototype.AbstractMethod { annotations; return; name; type_params; params }) }
| annotations = optAnnotations
  name = name (* NAME TYPENAME *)
    L_PAREN params = parameterList R_PAREN info2 = SEMICOLON
<<<<<<< HEAD
    { (Info.merge (info name) info2,
      MethodPrototype.Constructor { annotations; name; params }) }
=======
    { (P4info.merge name.tags info2,
      Surface.MethodPrototype.Constructor { annotations; name; params }) }
>>>>>>> 62cd2770 (wip fix menhir build errors)
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
    { P4name.BareName name }
| dotPrefix go_toplevel name = NAME TYPENAME go_local
    { P4name.QualifiedName ([], name) }
;

prefixedType:
| name = prefixedTypeName
<<<<<<< HEAD
    { name_info name, Type.TypeName name }
=======
    { P4name.name_info name, Surface.Type.TypeName name }
>>>>>>> 62cd2770 (wip fix menhir build errors)

typeName:
| typ = prefixedType
    { typ }
;

tupleType:
| info1 = TUPLE L_ANGLE elements = typeArgumentList info_r = r_angle
    { (P4info.merge info1 info_r,
       Surface.Type.Tuple elements) }
;

headerStackType:
| header = typeName L_BRACKET size = expression info2 = R_BRACKET
    { (P4info.merge (Surface.info header) info2,
       Surface.Type.HeaderStack { header; size }) }
;

specializedType:
| base = prefixedType L_ANGLE args = typeArgumentList info_r = r_angle
    { (P4info.merge (Surface.info base) info_r,
      Surface.Type.SpecializedType { base; args }) }
;

baseType:
| info = BOOL
    { (info, Surface.Type.Bool) }
| info = ERROR
    { (info, Surface.Type.Error) }
| info = BIT
<<<<<<< HEAD
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
=======
    { let width = (info, Surface.Expression.Int
                           ({ tags = info;
                              value = Bigint.of_int 1;
                              width_signed = None })) in
      (info, Surface.Type.BitType width): Type.t }
| info1 = BIT L_ANGLE value = INTEGER info_r = r_angle
    { let value_int: P4int.t = fst value in 
      let value_info = value_int.tags in
      let width: Expression.t =
        (value_info, Expression.Int value_int) in
      let info: P4info.t = P4info.merge info1 info_r in
      (info, Type.BitType width): Surface.Type.t }
| info1 = INT L_ANGLE value = INTEGER info_r = r_angle
     { let value_int: P4int.t = fst value in 
       let value_info = value_int.tags in 
>>>>>>> 62cd2770 (wip fix menhir build errors)
       let width = (value_info, Expression.Int value_int) in
       let info = P4info.merge info1 info_r in
      (info, Type.IntType width): Type.t }

| info1 = VARBIT L_ANGLE value = INTEGER info_r = r_angle
<<<<<<< HEAD
     { let value_int = fst value in 
       let value_info = fst value_int in
=======
     { let value_int: P4int.t = fst value in 
       let value_info = value_int.tags in
>>>>>>> 62cd2770 (wip fix menhir build errors)
       let max_width = (value_info, Expression.Int value_int) in
       let info = P4info.merge info1 info_r in
      (info, Surface.Type.VarBit max_width) }
| info1 = BIT L_ANGLE L_PAREN width = expression R_PAREN info_r = r_angle
    { (P4info.merge info1 info_r,
       Surface.Type.BitType width) }
| info1 = INT L_ANGLE L_PAREN width = expression R_PAREN info_r = r_angle
    { (P4info.merge info1 info_r,
       Surface.Type.IntType width) }
| info1 = VARBIT L_ANGLE L_PAREN max_width = expression R_PAREN info_r = r_angle
    { (P4info.merge info1 info_r,
       Surface.Type.VarBit max_width) }
| info = INT
    { (info, Surface.Type.Integer) }
| info = STRING
    { (info, Surface.Type.String) }
;

typeOrVoid:
| t = typeRef
  { t }
| info = VOID
  { (info, Surface.Type.Void) }
| name = varName
<<<<<<< HEAD
  { (info name, Type.TypeName (BareName name)) }    (* may be a type variable *)
=======
  { (name.tags, Surface.Type.TypeName (BareName name)) }    (* may be a type variable *)
>>>>>>> 62cd2770 (wip fix menhir build errors)
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
  { (info, Surface.Type.DontCare) }
| t = typeRef
  { t }
;

typeArg:
| info = DONTCARE { (info, Surface.Type.DontCare) }
| typ = typeRef { typ }
<<<<<<< HEAD
| name = nonTypeName { (info name, Type.TypeName (BareName name)) }
| info = VOID { (info, Type.Void) }
=======
| name = nonTypeName { (name.tags, Surface.Type.TypeName (BareName name)) }
| info = VOID { (info, Surface.Type.Void) }
>>>>>>> 62cd2770 (wip fix menhir build errors)
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
  { declare_type (Surface.Declaration.name d);
    d }
| ctd = controlTypeDeclaration pop_scope SEMICOLON
  { let info, annotations, name, type_params, params = ctd in
    (info,
     Surface.Declaration.ControlType { annotations; name; type_params; params } ) }
| ptd = parserTypeDeclaration pop_scope SEMICOLON
  { let info, annotations, name, type_params, params = ptd in
    (info,
     Surface.Declaration.ParserType { annotations; name; type_params; params } ) }
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
        Surface.Declaration.Header { annotations; name; fields }) }
;

headerUnionDeclaration:
|  annotations = optAnnotations info1 = HEADER_UNION name = name
     L_BRACE fields = list(structField) info2 = R_BRACE
     { (P4info.merge info1 info2,
        Surface.Declaration.HeaderUnion { annotations; name; fields }) }
;

structTypeDeclaration:
|  annotations = optAnnotations info1 = STRUCT name = name
     L_BRACE fields = list(structField) info2 = R_BRACE
     { (P4info.merge info1 info2,
        Surface.Declaration.Struct { annotations; name; fields }) }
;

structField:
|  annotations = optAnnotations typ = typeRef name = name info2 = SEMICOLON
     { (P4info.merge (Surface.info typ) info2,
        { annotations; typ; name }) : Surface.Declaration.field }
;

(* TODO : add support for serializable enums *)
enumDeclaration:
| annotations = optAnnotations info1 = ENUM name = name
    L_BRACE members = identifierList info2 = R_BRACE
<<<<<<< HEAD
    { (Info.merge info1 info2,
      Declaration.Enum { annotations; name; members }) }
| annotations = optAnnotations info1 = ENUM typ = baseType
    name = name L_BRACE members = specifiedIdentifierList info4 = R_BRACE
   { (Info.merge info1 (fst typ),
     Declaration.SerializableEnum { annotations; typ; name; members }) }
=======
    { (P4info.merge info1 info2,
      Surface.Declaration.Enum { annotations; name; members }) }
| annotations = optAnnotations info1 = ENUM info2 = BIT L_ANGLE value = INTEGER r_angle
    name = name L_BRACE members = specifiedIdentifierList info4 = R_BRACE
   { let value_int: P4info.t P4int.pre_t = (fst value) in 
     let value_info: P4info.t = value_int.tags in 
     let width = (value_info, Surface.Expression.Int value_int) in
     let typ = (P4info.merge info2 info4, Surface.Type.BitType width) in
     (P4info.merge info1 info4,
      Surface.Declaration.SerializableEnum { annotations; typ; name; members }) }
>>>>>>> 62cd2770 (wip fix menhir build errors)
;

errorDeclaration:
| info1 = ERROR L_BRACE members = identifierList info2 = R_BRACE
    { declare_vars members;
      (P4info.merge info1 info2,
       Surface.Declaration.Error { members }) }
;

matchKindDeclaration:
| info1 = MATCH_KIND L_BRACE members = identifierList info2 = R_BRACE
    { declare_vars members;
      (P4info.merge info1 info2,
       Surface.Declaration.MatchKind { members }) }
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
       Surface.Declaration.TypeDef { annotations; name; typ_or_decl = Left typ } ) }
| annotations = optAnnotations info1 = TYPEDEF
    decl = derivedTypeDeclaration name = name info2 = SEMICOLON
    { (P4info.merge info1 info2,
       Surface.Declaration.TypeDef { annotations; name; typ_or_decl = Right decl } ) }
| annotations = optAnnotations info1 = TYPE
    typ = typeRef name = name info2 = SEMICOLON
    { (P4info.merge info1 info2,
       Surface.Declaration.NewType { annotations; name; typ_or_decl = Left typ } ) }
| annotations = optAnnotations info1 = TYPE
    decl = derivedTypeDeclaration name = name info2 = SEMICOLON
    { (P4info.merge info1 info2,
       Surface.Declaration.NewType { annotations; name; typ_or_decl = Right decl } ) }
;

(*************************** STATEMENTS *************************)

assignmentOrMethodCallStatement:
| func = lvalue L_PAREN args = argumentList R_PAREN info2 = SEMICOLON
    { let type_args = [] in
      (P4info.merge (Surface.info func) info2,
       Surface.Statement.MethodCall { func; type_args; args }) }
| func = lvalue L_ANGLE type_args = typeArgumentList r_angle
    L_PAREN args = argumentList R_PAREN info2 = SEMICOLON
    { (P4info.merge (Surface.info func) info2,
       Surface.Statement.MethodCall { func; type_args; args }) }
| lhs = lvalue ASSIGN rhs = expression info2 = SEMICOLON
    { (P4info.merge (Surface.info lhs) info2,
      Surface.Statement.Assignment { lhs; rhs }) }
;

emptyStatement:
| info = SEMICOLON { (info, Surface.Statement.EmptyStatement) }
;

returnStatement:
| info1 = RETURN info2 = SEMICOLON
    { (P4info.merge info1 info2,
       Surface.Statement.Return { expr = None }) }
| info1 = RETURN expr = expression info2 = SEMICOLON
    { (P4info.merge info1 info2,
       Surface.Statement.Return { expr = Some expr }) }
;

exitStatement:
| info1 = EXIT info2 = SEMICOLON
    { (P4info.merge info1 info2,
       Surface.Statement.Exit) }
;

conditionalStatement:
| info1 = IF L_PAREN cond = expression R_PAREN tru = statement ELSE fls = statement
    { let info2 = Surface.info fls in
      let fls = Some fls in
      (P4info.merge info1 info2,
       Surface.Statement.Conditional { cond; tru; fls }) }
| info1 = IF L_PAREN cond = expression R_PAREN tru = statement   %prec THEN
    { let fls = None in
      (P4info.merge info1 (Surface.info tru),
       Surface.Statement.Conditional { cond; tru; fls }) }
;

(* To support direct invocation of a control or parser without instantiation *)
directApplication:
| typ = typeName DOT APPLY L_PAREN args = argumentList R_PAREN info2 = SEMICOLON
    { (P4info.merge (Surface.info typ) info2,
      Surface.Statement.DirectApplication { typ; args }) }
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
    { (Surface.info block, Surface.Statement.BlockStatement { block }) }
;

blockStatement:
|  annotations = optAnnotations
     info1 = L_BRACE
     push_scope
     statements = list(statementOrDeclaration) info2 = R_BRACE
     pop_scope
     { (P4info.merge info1 info2,
       Surface.Block.{ annotations; statements }) }
;

switchStatement:
| info1 = SWITCH L_PAREN expr = expression R_PAREN L_BRACE cases = switchCases
  info2 = R_BRACE
    { (P4info.merge info1 info2,
       Surface.Statement.Switch { expr; cases }) }
;

switchCases : cases = list(switchCase) { cases } ;

switchCase:
| label = switchLabel COLON code = blockStatement
    { (P4info.merge (Surface.info label) (Surface.info code), Surface.Statement.Action { label; code } ) }
| label = switchLabel info2 = COLON
    { (P4info.merge (Surface.info label) info2, Surface.Statement.FallThrough { label }) }
;

switchLabel:
| name = name
<<<<<<< HEAD
  { (info name, Statement.Name name) }
=======
  { (name.tags, Surface.Statement.Name name) }
>>>>>>> 62cd2770 (wip fix menhir build errors)
| info = DEFAULT
  { (info, Surface.Statement.Default) }
;

statementOrDeclaration:
| decl = variableDeclaration
| decl = constantDeclaration
| decl = instantiation
  { (Surface.info decl, Surface.Statement.DeclarationStatement { decl = decl }) }
| s = statement
  { s }
;

(************ TABLES *************)
tableDeclaration:
|  annotations = optAnnotations
     info1 = TABLE name = name L_BRACE properties = tablePropertyList
     info2 = R_BRACE
     { (P4info.merge info1 info2,
        Surface.Declaration.Table { annotations; name; properties }) }
;

tablePropertyList:
| props = nonempty_list(tableProperty) { props }
;

tableProperty:
| info1 = KEY ASSIGN L_BRACE elts = keyElementList info2 = R_BRACE
    { (P4info.merge info1 info2,
       Surface.Table.Key { keys = elts }) }
| info1 = ACTIONS ASSIGN L_BRACE acts = actionList info2 = R_BRACE
    { (P4info.merge info1 info2,
       Surface.Table.Actions { actions = acts }) }
| info1 = CONST ENTRIES ASSIGN L_BRACE entries = entriesList info2 = R_BRACE
    { (P4info.merge info1 info2,
       Surface.Table.Entries { entries = entries }) }
| annos = optAnnotations
    info1 = CONST n = nonTableKwName ASSIGN v = initialValue info2 = SEMICOLON
    { (P4info.merge info1 info2,
       Surface.Table.Custom { annotations = annos; const = true; name = n; value = v }) }
| annos = optAnnotations
    n = nonTableKwName ASSIGN v = initialValue info2 = SEMICOLON
<<<<<<< HEAD
    { (Info.merge (info n) info2,
       Table.Custom { annotations = annos; const = false; name = n; value = v }) }
=======
    { (P4info.merge n.tags info2,
       Surface.Table.Custom { annotations = annos; const = false; name = n; value = v }) }
>>>>>>> 62cd2770 (wip fix menhir build errors)
;

keyElementList: elts = list(keyElement) { elts } ;

keyElement:
| key = expression COLON match_kind = name annotations = optAnnotations
    info2 = SEMICOLON
    { (P4info.merge (Surface.info key) info2,
       Surface.Table.{ annotations; key; match_kind }) }
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
      (info, Surface.Table.{ annotations = annos; matches = matches; action = act }) }
;

actionRef:
|  annotations = optAnnotations name = name
<<<<<<< HEAD
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
=======
     { (name.tags, { annotations; name = BareName name; args = [] }) : Surface.Table.action_ref }
|  annotations = optAnnotations name = name L_PAREN args = argumentList
     info2 = R_PAREN
     { (P4info.merge name.tags info2,
        { annotations; name = BareName name; args }) : Surface.Table.action_ref }
|  annotations = optAnnotations
   info1 = dotPrefix go_toplevel name = nonTypeName go_local
     { (name.tags, { annotations; name = QualifiedName ([], name); args = [] }) : Surface.Table.action_ref }
|  annotations = optAnnotations 
   info1 = dotPrefix go_toplevel name = nonTypeName go_local
   L_PAREN args = argumentList info2 = R_PAREN
     { (P4info.merge name.tags info2,
        { annotations; name = QualifiedName ([], name); args }) : Surface.Table.action_ref }
>>>>>>> 62cd2770 (wip fix menhir build errors)
;

(************************* ACTION ********************************)

actionDeclaration:
|  annotations = optAnnotations
     info1 = ACTION name = name L_PAREN params = parameterList R_PAREN
     body = blockStatement
     { (P4info.merge info1 (Surface.info body),
        Surface.Declaration.Action { annotations; name; params; body }) }
;

(************************* VARIABLES *****************************)

variableDeclaration:
| annotations = optAnnotations
    typ = typeRef name = name init = optInitialValue info2 = SEMICOLON
    { declare_var name;
      (P4info.merge (Surface.info typ) info2,
       Surface.Declaration.Variable { annotations; typ; name; init }) }
;

constantDeclaration:
| annotations = optAnnotations
    info1 = CONST typ = typeRef name = name ASSIGN value = initialValue
    info2 = SEMICOLON
    { (P4info.merge info1 info2,
       Surface.Declaration.Constant { annotations; typ; name; value }) }
;

optInitialValue:
| (* empty *) { None }
| ASSIGN v = initialValue { Some v }
;

initialValue:
| v = expression { v }
;

(************************* Surface.Expressions ****************************)

functionDeclaration:
| func = functionPrototype body = blockStatement pop_scope
    { let (info1, return, name, type_params, params) = func in
      (P4info.merge info1 (Surface.info body),
       Surface.Declaration.Function { return; name; type_params; params; body }) }
;

argumentList: args = separated_list(COMMA, argument) { args } ;

argument:
| value = expression
    { (Surface.info value, Surface.Argument.Expression { value }) }
| key = name ASSIGN value = expression
<<<<<<< HEAD
    { (Info.merge (info key) (info value),
       Argument.KeyValue { key; value }) }
=======
    { (P4info.merge key.tags (Surface.info value),
       Surface.Argument.KeyValue { key; value }) }
>>>>>>> 62cd2770 (wip fix menhir build errors)
| info = DONTCARE
    { (info, Surface.Argument.Missing) }
;

%inline kvPair:
| key = name ASSIGN value = expression 
<<<<<<< HEAD
  { (Info.merge (info key) (info value),
     KeyValue.{ key; value }) }
=======
  { (P4info.merge key.tags (Surface.info value),
     Surface.KeyValue.{ key; value }) }
>>>>>>> 62cd2770 (wip fix menhir build errors)

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
<<<<<<< HEAD
  { (info name, Expression.Name (BareName name)) }
| info1 = dotPrefix go_toplevel name = nonTypeName go_local
  { (Info.merge info1 (info name),
     Expression.Name (QualifiedName ([], name))) }
=======
  { (name.tags, Surface.Expression.Name (BareName name)) }
| info1 = dotPrefix go_toplevel name = nonTypeName go_local
  { (P4info.merge info1 name.tags,
     Surface.Expression.Name (QualifiedName ([], name))) }
>>>>>>> 62cd2770 (wip fix menhir build errors)
;

lvalue:
| expr = prefixedNonTypeName { expr }
| expr = lvalue DOT name = member
<<<<<<< HEAD
  { (Info.merge (info expr) (info name),
     Expression.ExpressionMember { expr; name }) }
=======
    { (P4info.merge (Surface.info expr) name.tags,
       Surface.Expression.ExpressionMember { expr; name }) }
>>>>>>> 62cd2770 (wip fix menhir build errors)
| array = lvalue L_BRACKET index = expression info2 = R_BRACKET
    { (P4info.merge (Surface.info array) info2,
       Surface.Expression.ArrayAccess { array; index }) }
| bits = lvalue L_BRACKET hi = expression COLON lo = expression
    info2 = R_BRACKET
    { (P4info.merge (Surface.info bits) info2,
       Surface.Expression.BitStringAccess { bits; lo; hi }) }
;

expression:
| value = INTEGER
<<<<<<< HEAD
  { let value_int = fst value in 
    let info = fst value_int in 
    (info, Expression.Int value_int) }
=======
  { let value_int: P4int.t = fst value in 
    let info = value_int.tags in 
    (info, Surface.Expression.Int value_int) }
>>>>>>> 62cd2770 (wip fix menhir build errors)
| info1 = TRUE
  { (info1, Surface.Expression.True) }
| info1 = FALSE
  { (info1, Surface.Expression.False) }
| value = STRING_LITERAL
<<<<<<< HEAD
  { (fst value, Expression.String value) }
| name = nonTypeName
  { (info name, Expression.Name (BareName name)) }
| info1 = dotPrefix go_toplevel name = nonTypeName go_local
  { (Info.merge info1 (fst name), Expression.Name (QualifiedName ([], name))) }
=======
  { (value.tags, Surface.Expression.String value) }
| name = nonTypeName
  { (name.tags, Surface.Expression.Name (BareName name)) }
| info1 = dotPrefix go_toplevel name = nonTypeName go_local
  { (P4info.merge info1 name.tags, Surface.Expression.Name (QualifiedName ([], name))) }
>>>>>>> 62cd2770 (wip fix menhir build errors)
| array = expression L_BRACKET index = expression info2 = R_BRACKET
  { (P4info.merge (Surface.info array) info2,
     Surface.Expression.ArrayAccess { array; index }) }
| bits = expression L_BRACKET hi = expression COLON lo = expression
    info2 = R_BRACKET
  { (P4info.merge (Surface.info bits) info2,
     Surface.Expression.BitStringAccess { bits; lo; hi }) }
| info1 = L_BRACE values = expressionList info2 = R_BRACE
  { (P4info.merge info1 info2,
     Surface.Expression.List { values }) }
| info1 = L_BRACE entries = kvList info2 = R_BRACE 
  { (P4info.merge info1 info2, 
     Surface.Expression.Record { entries }) }
| L_PAREN exp = expression R_PAREN
  { exp }
| info1 = NOT arg = expression %prec PREFIX
  { (P4info.merge info1 (Surface.info arg),
     Surface.Expression.UnaryOp { op = (info1, Surface.Op.Not); arg }) }
| info1 = COMPLEMENT arg = expression %prec PREFIX
  { (P4info.merge info1 (Surface.info arg),
     Surface.Expression.UnaryOp{op = (info1, Surface.Op.BitNot); arg }) }
| info1 = MINUS arg = expression %prec PREFIX
  { (P4info.merge info1 (Surface.info arg),
     Surface.Expression.UnaryOp{op = (info1, UMinus); arg }) }
| info1 = PLUS exp = expression %prec PREFIX
  { let info2,exp = exp in
    (P4info.merge info1 info2, exp) }
| info1 = L_PAREN typ = typeRef R_PAREN expr = expression %prec PREFIX
  { (P4info.merge info1 (Surface.info expr),
     Surface.Expression.Cast { typ; expr }) }
| typ = prefixedTypeName DOT name = member
<<<<<<< HEAD
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
=======
  { (name.tags,
     Surface.Expression.TypeMember { typ; name }) }
| info1 = ERROR DOT name = member
  { (P4info.merge info1 name.tags,
     Surface.Expression.ErrorMember name) }
| expr = expression DOT name = member
  { (P4info.merge (Surface.info expr) name.tags,
     Surface.Expression.ExpressionMember { expr; name }) }
| arg1 = expression op = binop arg2 = expression
  { (P4info.merge (Surface.info arg1) (Surface.info arg2),
     Surface.Expression.BinaryOp { op; args = (arg1, arg2) }) }
>>>>>>> 62cd2770 (wip fix menhir build errors)
| cond = expression QUESTION tru = expression COLON fls = expression
   { (P4info.merge (Surface.info cond) (Surface.info fls),
      Surface.Expression.Ternary { cond; tru; fls }) }
| func = expression L_ANGLE type_args = realTypeArgumentList r_angle
    L_PAREN args = argumentList info2 = R_PAREN
   { (P4info.merge (Surface.info func) info2,
      Surface.Expression.FunctionCall { func; type_args; args }) }
| func = expression L_PAREN args = argumentList info2 = R_PAREN
   { let type_args = [] in
     (P4info.merge (Surface.info func) info2,
      Surface.Expression.FunctionCall { func; type_args; args }) }
| typ = namedType L_PAREN args = argumentList info2 = R_PAREN
   { (P4info.merge (Surface.info typ) info2,
      Surface.Expression.NamelessInstantiation { typ; args }) }
;

%inline binop:
| info = MUL
    { (info, Surface.Op.Mul) }
| info = DIV
    { (info, Surface.Op.Div) }
| info = MOD
    { (info, Surface.Op.Mod) }
| info = PLUS
    { (info, Surface.Op.Plus) }
| info = PLUS_SAT
    { (info, Surface.Op.PlusSat)}
| info = MINUS
    { (info, Surface.Op.Minus) }
| info = MINUS_SAT
    { (info, Surface.Op.MinusSat) }
| info = SHL
    { (info, Surface.Op.Shl) }
| info_r = r_angle info2 = R_ANGLE_SHIFT
    { (P4info.merge info_r info2, Surface.Op.Shr) }
| info = LE
    { (info, Surface.Op.Le) }
| info = GE
    { (info, Surface.Op.Ge) }
| info = L_ANGLE
    { (info, Surface.Op.Lt) }
| info_r = r_angle
    { (info_r, Surface.Op.Gt) }
| info = NE
    { (info, Surface.Op.NotEq) }
| info = EQ
    { (info, Surface.Op.Eq) }
| info = BIT_AND
    { (info, Surface.Op.BitAnd) }
| info = BIT_XOR
    { (info, Surface.Op.BitXor) }
| info = BIT_OR
    { (info, Surface.Op.BitOr) }
| info = PLUSPLUS
    { (info, Surface.Op.PlusPlus) }
| info = AND
    { (info, Surface.Op.And) }
| info = OR
    { (info, Surface.Op.Or) }
;

%inline r_angle:
| info_r = R_ANGLE { info_r } 
| info_r = R_ANGLE_SHIFT { info_r }

(* À jour avec le commit 45df9f41a2cf1af56f4fa1cfaa1f586adefd13b7
   de p4-spec; à dotPrefix et listes près *)
