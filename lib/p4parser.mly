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
open Poulet4.Typed
open Poulet4.P4String
open Surface
open Core
open Context

let declare_vars vars = List.iter vars ~f:(fun s -> declare_var s false)
let declare_types types = List.iter types ~f:(fun s -> declare_type s false)

let rec smash_annotations (l: P4string.t list) (tok2: P4string.t) : P4string.t list =
  match l with 
  | [] ->
     [tok2]
  | [tok1] ->
     if P4info.follows tok1.tags tok2.tags then
       [{tags = P4info.merge tok1.tags tok2.tags;
         str = tok1.str ^ tok2.str}]
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
%token<P4info.t> L_BRACKET R_BRACKET L_BRACE R_BRACE L_ANGLE L_ANGLE_ARGS R_ANGLE R_ANGLE_SHIFT L_PAREN R_PAREN
%token<P4info.t> ASSIGN COLON COMMA QUESTION DOT NOT SEMICOLON
%token<P4info.t> AT PLUSPLUS
%token<P4info.t> DONTCARE
%token<P4info.t> MASK RANGE
%token<P4info.t> TRUE FALSE
%token<P4info.t> ABSTRACT ACTION ACTIONS APPLY BOOL BIT CONST CONTROL DEFAULT DEFAULT_ACTION
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
%nonassoc L_PAREN L_BRACKET L_ANGLE_ARGS
%left DOT


%start <Surface.program> p4program
%start <Surface.Declaration.t> variableDeclaration
%start <Surface.Declaration.t> typeDeclaration

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
       declare_type n false;
       n}

push_externName:
| n = externName
    { push_scope();
      declare_type n false;
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
    { declare_var (Declaration.name c) (Declaration.has_type_params c);
      c }
| e = externDeclaration
    { e }
| a = actionDeclaration
    { declare_var (Declaration.name a) false;
      a }
| p = parserDeclaration
    { declare_type (Declaration.name p) (Declaration.has_type_params p);
      p }
| c = controlDeclaration
    { declare_type (Declaration.name c) (Declaration.has_type_params c);
      c }
| i = instantiation
    { declare_var (Declaration.name i) false;
      i }
| t = typeDeclaration
    { declare_type (Declaration.name t) (Declaration.has_type_params t);
      t }
| e = errorDeclaration
    { (* declare_type (Declaration.name e) false; *)
      e }
| m = matchKindDeclaration
    { m }
| f = functionDeclaration
    { declare_var (Declaration.name f) (Declaration.has_type_params f);
      f }
;

varName:
| id = NAME IDENTIFIER { id }
;

tableKwName:
| info = KEY { { str = "key"; tags = info} }
| info = ACTIONS { { str = "actions"; tags = info} }
| info = ENTRIES { { str = "entries"; tags = info} }
;

nonTableKwName:
| n = varName { n }
| n = NAME TYPENAME { n }
| info = APPLY { { str = "apply"; tags = info} }
| info = STATE { { str = "state"; tags = info} }
| info = TYPE { { str = "type"; tags = info} }
;

nonTypeName:
| n = varName { n }
| n = tableKwName { n }
| info = APPLY { { str = "apply"; tags = info} }
| info = STATE { { str = "state"; tags = info} }
| info = TYPE { { str = "type"; tags = info} }
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

  (* reminder. name : P4string *)
annotation:
| info1 = AT name = name
    { let info2 = name.tags in
      let body = Annotation.Empty {tags = info2} in 
      let info' = P4info.merge info1 info2 in 
       Annotation.{ name; body; tags = info' } }

| info1 = AT name = name info2 = L_PAREN body = annotationBody info3 = R_PAREN
    { let tags = P4info.merge info2 info3 in
      let body = Annotation.Unparsed {str = body; tags} in
      let tags' = P4info.merge info1 info3 in 
       Annotation.{ name; body; tags = tags' } }

| info1 = AT name = name info2 = L_BRACKET body = expressionList info3 = R_BRACKET
    { let tags = P4info.merge info2 info3 in 
      let body = Annotation.Expression {exprs = body; tags} in
      let tags' = P4info.merge info1 info3 in
       Annotation.{ name; body; tags = tags' } }

| info1 = AT name = name info2 = L_BRACKET body = kvList info3 = R_BRACKET
    { let tags = P4info.merge info2 info3 in 
      let body = Annotation.KeyValue {k_v = body; tags} in
      let tags' = P4info.merge info1 info3 in
       Annotation.{ name; body; tags = tags' } }

| info1 = PRAGMA name = name body = annotationBody info2 = PRAGMA_END
    { let body = Annotation.Unparsed {str = body; tags = info2} in
      let tags = P4info.merge info1 info2 in
       Annotation.{ name; body; tags } }
;

annotationBody:
| (* empty *) 
  { [] }
| body1 = annotationBody L_PAREN body2 = annotationBody R_PAREN
  { body1 @ body2 }
| body = annotationBody token = annotationToken
  { (*ENSURE! not sure if this is correct!!*) smash_annotations body token }
;

annotationToken:
| UNEXPECTED_TOKEN { $1 }
| ABSTRACT         { {tags = $1; str = "abstract"} }
| ACTION           { {tags = $1; str = "action"} }
| ACTIONS          { {tags = $1; str = "actions"} }
| APPLY            { {tags = $1; str = "apply"} }
| BOOL             { {tags = $1; str = "bool"} }
| BIT              { {tags = $1; str = "bit"} }
| CONST            { {tags = $1; str = "const"} }
| CONTROL          { {tags = $1; str = "control"} }
| DEFAULT          { {tags = $1; str = "default"} }
| ELSE             { {tags = $1; str = "else"} }
| ENTRIES          { {tags = $1; str = "entries"} }
| ENUM             { {tags = $1; str = "enum"} }
| ERROR            { {tags = $1; str = "error"} }
| EXIT             { {tags = $1; str = "exit"} }
| EXTERN           { {tags = $1; str = "extern"} }
| FALSE            { {tags = $1; str = "false"} }
| HEADER           { {tags = $1; str = "header"} }
| HEADER_UNION     { {tags = $1; str = "header_union"} }
| IF               { {tags = $1; str = "if"} }
| IN               { {tags = $1; str = "in"} }
| INOUT            { {tags = $1; str = "inout"} }
| INT              { {tags = $1; str = "int"} }
| KEY              { {tags = $1; str = "key"} }
| MATCH_KIND       { {tags = $1; str = "match_kind"} }
| TYPE             { {tags = $1; str = "type"} }
| OUT              { {tags = $1; str = "out"} }
| PARSER           { {tags = $1; str = "parser"} }
| PACKAGE          { {tags = $1; str = "package"} }
| PRAGMA           { {tags = $1; str = "pragma"} }
| RETURN           { {tags = $1; str = "return"} }
| SELECT           { {tags = $1; str = "select"} }
| STATE            { {tags = $1; str = "state"} }
| STRING           { {tags = $1; str = "string"} }
| STRUCT           { {tags = $1; str = "struct"} }
| SWITCH           { {tags = $1; str = "switch"} }
| TABLE            { {tags = $1; str = "table"} }
(* | THIS             { ($1, "this") } *)
| TRANSITION       { {tags = $1; str = "transition"} }
| TRUE             { {tags = $1; str = "true"} }
| TUPLE            { {tags=$1; str="tuple"} }
| TYPEDEF          { {tags=$1; str="typedef"} }
| VARBIT           { {tags=$1; str="varbit"} }
| VALUESET         { {tags=$1; str="valueset"} }
| VOID             { {tags = $1; str = "void"} }
| DONTCARE         { {tags = $1; str = "_"} }
| NAME IDENTIFIER  { $1 }
| NAME TYPENAME    { $1 }
| STRING_LITERAL   { let info, str = $1.tags, $1.str in
                     {tags = info; str = "\"" ^ str ^ "\""} }
| INTEGER          { let p4int : P4int.t = fst $1 in
                     let str : string = snd $1 in
                     {tags = p4int.tags; str = str} }
| MASK             { {tags = $1; str = "&&&"} }
| RANGE            { {tags = $1; str = ".."} }
| SHL              { {tags = $1; str = "<<"} }
| AND              { {tags = $1; str = "&&"} }
| OR               { {tags = $1; str = "||"} }
| EQ               { {tags = $1; str = "=="} }
| NE               { {tags = $1; str = "!="} }
| GE               { {tags = $1; str = ">="} }
| LE               { {tags = $1; str = "<="} }
| PLUSPLUS         { {tags = $1; str = "++"} }
| PLUS             { {tags = $1; str = "+"} } 
| PLUS_SAT         { {tags = $1; str = "|+|"} }
| MINUS            { {tags = $1; str = "-"} }
| MINUS_SAT        { {tags = $1; str = "|-|"} }
| MUL              { {tags = $1; str = "*"} }
| DIV              { {tags = $1; str = "/"} }
| MOD              { {tags = $1; str = "%"} }
| BIT_OR           { {tags = $1; str = "|"} }
| BIT_AND          { {tags = $1; str = "&"} }
| BIT_XOR          { {tags = $1; str = "^"} }
| COMPLEMENT       { {tags = $1; str = "~"} }
| L_BRACKET        { {tags = $1; str = "["} }
| R_BRACKET        { {tags = $1; str = "]"} }
| L_BRACE          { {tags = $1; str = "{"} }
| R_BRACE          { {tags = $1; str = "}"} }
| L_ANGLE          { {tags = $1; str = "<"} }
| R_ANGLE          { {tags = $1; str =">"} }
| NOT              { {tags =$1; str ="!"} }
| COLON            { {tags = $1; str =":"} }
| COMMA            { {tags = $1; str = ","} }
| QUESTION         { {tags = $1; str = "?"} }
| DOT              { {tags = $1; str = "."} }
| ASSIGN           { {tags = $1; str = "="} }
| SEMICOLON        { {tags = $1; str =";"} }
| AT               { {tags = $1; str = "@"} }
;

  (* reminder. variables are of P4string*)
parameterList:
| params = separated_list(COMMA, parameter)
    { let names = List.map ~f:(fun (p : Parameter.t) -> p.Parameter.variable) params in
      declare_vars names; params }
;

parameter:
| annotations = optAnnotations direction = direction typ = typeRef variable = name
    { let info1 =
        match direction with
        | None -> Type.tags typ
        | Some dir -> Direction.tags dir in
      let info' = P4info.merge info1 variable.tags in
       Parameter.{ annotations; direction; typ; variable; opt_value = None; tags = info' } }
| annotations = optAnnotations direction = direction typ = typeRef variable = name
   ASSIGN value = expression
    { let info1 =
        match (direction : Direction.t option) with
        | None -> Type.tags typ
        | Some dir -> Direction.tags dir in
      let info' = P4info.merge info1 variable.tags in
       Parameter.{ annotations; direction; typ; variable; opt_value = Some value; tags = info' } }
;

direction:
| info = IN      { Some (Direction.In {tags = info}) }
| info = OUT     { Some (Direction.Out {tags = info}) }
| info = INOUT   { Some (Direction.InOut {tags = info}) }
| (* empty *)    { None }
;

packageTypeDeclaration:
|  annotations = optAnnotations info1 = PACKAGE
   name = push_name
     type_params = optTypeParameters
     L_PAREN params = parameterList info2 = R_PAREN
     {  let info' = P4info.merge info1 info2 in
        Declaration.PackageType { annotations; name; type_params; params; tags = info' } }
;

instantiation:
| annotations = optAnnotations typ = typeRef
    L_PAREN args = argumentList R_PAREN name = name info2 = SEMICOLON
    { let info' = P4info.merge (Type.tags typ) info2 in
       Declaration.Instantiation { annotations; typ; args; name; init=None; tags = info'  } }
| annotations = optAnnotations typ = typeRef
    L_PAREN args = argumentList R_PAREN name = name ASSIGN init = objInitializer info2 = SEMICOLON
    { let info' = P4info.merge (Type.tags typ) info2 in
       Declaration.Instantiation { annotations; typ; args; name; init=Some init; tags = info' } }
;

objInitializer:
| L_BRACE statements = list(objDeclaration) R_BRACE 
  { let info' = P4info.merge $1 $3 in
    Block.{ annotations = []; statements; tags = info' } }
;

objDeclaration:
| decl = functionDeclaration
  { let tags = Declaration.tags decl in
    Statement.DeclarationStatement { decl; tags } }
| decl = instantiation 
  { let tags = Declaration.tags decl in
    Statement.DeclarationStatement { decl; tags } }
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
      let tags = P4info.merge info1 info2 in
      let locals = List.rev locals in
      Parser { annotations; name; type_params; params; constructor_params; locals; states; tags } }
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
     { let tags = P4info.merge info1 info2 in
       Parser.{ annotations; name; statements; transition; tags } }

;

parserStatement:
| s = assignmentOrMethodCallStatement
| s = directApplication
| s = emptyStatement
| s = parserBlockStatement
   { s }
| decl = constantDeclaration
| decl = variableDeclaration
  { let tags = Declaration.tags decl in
    Statement.DeclarationStatement { decl; tags } }
;

parserBlockStatement:
|  annotations = optAnnotations
     info1 = L_BRACE statements = list(parserStatement) info2 = R_BRACE
     { let tags = P4info.merge info1 info2 in
       let block = Block.{ annotations; statements; tags } in
       Statement.BlockStatement { block = block; tags } }
;

transitionStatement:
| (* empty *)
  { let tags = P4info.M "Compiler-generated reject transition" in
    Parser.Direct { next = {tags; str = "reject"}; tags } }

| info1 = TRANSITION transition = stateExpression
    { (*let tags = P4info.merge info1 (tags transition)
       snd transition)*)
      (* ENSURE! not sure what's the type of transition but I'm guessing it's 'a ptransition.*)
      Parser.update_transition_tags transition (P4info.merge info1 (Parser.transition_tags transition)) }
;

stateExpression:
| next = name info2 = SEMICOLON
    { let tags = P4info.merge next.tags info2 in
       Parser.Direct { next = next; tags } }
| select = selectExpression
    { select }
;

selectExpression:
| info1 = SELECT L_PAREN exprs = expressionList R_PAREN
    L_BRACE cases = list(selectCase) info2 = R_BRACE
    { let tags = P4info.merge info1 info2 in
       Parser.Select { exprs; cases; tags } }
;

selectCase:
| matches = keysetExpression COLON next = name info2 = SEMICOLON
  { let info1 = match (matches : Match.t list) with
      | expr::_ -> Match.tags expr
      | _ -> assert false in
    let tags = P4info.merge info1 info2 in
     Parser.{ matches; next; tags } }
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
| expr = expression { let tags = Expression.tags expr in
                      Match.Expression { expr; tags } }
| info = DONTCARE { Match.DontCare {tags = info} }
| info = DEFAULT { Match.Default {tags = info} }
| expr = expression MASK mask = expression
    { let tags = P4info.merge (Expression.tags expr) (Expression.tags mask) in
      Match.Expression { expr = Expression.Mask { expr; mask; tags }; tags } }
| lo = expression RANGE hi = expression
    { let tags = P4info.merge (Expression.tags lo) (Expression.tags hi) in
      Match.Expression {expr = Expression.Range { lo; hi; tags }; tags}}
;

valueSetDeclaration:
| annotations = optAnnotations
    info1 = VALUESET l_angle typ = baseType r_angle
    L_PAREN size = expression R_PAREN name = name info2 = SEMICOLON
| annotations = optAnnotations
    info1 = VALUESET l_angle typ = tupleType r_angle
    L_PAREN size = expression R_PAREN name = name info2 = SEMICOLON
| annotations = optAnnotations
    info1 = VALUESET l_angle typ = typeName r_angle
    L_PAREN size = expression R_PAREN name = name info2 = SEMICOLON
    { let tags = P4info.merge info1 info2 in
      Declaration.ValueSet { annotations; typ; size; name; tags }  }
;

(*************************** CONTROL ************************)

controlDeclaration:
| ct_decl = controlTypeDeclaration constructor_params = optConstructorParameters
    L_BRACE locals = list(controlLocalDeclaration) APPLY apply = controlBody
    info2 = R_BRACE
    pop_scope
    {
      let info1, annotations, name, type_params, params = ct_decl in
      let tags = P4info.merge info1 info2 in
       Declaration.Control { annotations; name; type_params; params; constructor_params;
                             locals; apply; tags }  }
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
    { declare_var (Declaration.name a) false; a }
| t = tableDeclaration
    { declare_var (Declaration.name t) false; t }
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
     { let tags = P4info.merge info1 info2 in
       let type_decl =
          (Declaration.ExternObject { annotations; name; type_params; methods; tags }) in
       declare_type name (Declaration.has_type_params type_decl);
       type_decl }
|  annotations = optAnnotations info1 = EXTERN
     func = functionPrototype pop_scope info2 = SEMICOLON
     { let (_, return, name, type_params, params) = func in
       let tags = P4info.merge info1 info2 in
       let decl =
          Declaration.ExternFunction { annotations; return; name; type_params; params; tags } in
       declare_var name (Declaration.has_type_params decl);
       decl }
;

externName:
| n = nonTypeName { declare_type n false; n }
(* So that it is declared a typename before constructors are parsed
   Could use midrule instead x) *)
;

functionPrototype:
| typ = typeOrVoid name = name
    push_scope
      type_params = optTypeParameters
      L_PAREN params = parameterList info2 = R_PAREN
    { (P4info.merge (Type.tags typ) info2, typ, name, type_params, params) }
;

methodPrototype:
| annotations = optAnnotations
  func = functionPrototype pop_scope info2 = SEMICOLON
    { let (info1, return, name, type_params, params) = func in
      let tags = P4info.merge info1 info2 in
       MethodPrototype.Method { annotations; return; name; type_params; params; tags } }

| annotations = optAnnotations
  ABSTRACT
  func = functionPrototype pop_scope info2 = SEMICOLON
    { let (info1, return, name, type_params, params) = func in
      let tags = P4info.merge info1 info2 in
       MethodPrototype.AbstractMethod { annotations; return; name; type_params; params; tags } }
| annotations = optAnnotations
  name = name (* NAME TYPENAME *) (* reminder. name : P4string*)
    L_PAREN params = parameterList R_PAREN info2 = SEMICOLON
    { let tags = P4info.merge (name.tags) info2 in
      MethodPrototype.Constructor { annotations; name; params; tags } }
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
    { let tags = P4name.name_tags name in
       Type.TypeName {tags ; name = name} }

typeName:
| typ = prefixedType
    { typ }
;

tupleType:
| info1 = TUPLE l_angle elements = typeArgumentList info_r = r_angle
    { let tags = P4info.merge info1 info_r in
       Type.Tuple {tags; xs = elements} }
;

headerStackType:
| header = typeName L_BRACKET size = expression info2 = R_BRACKET
    { let tags = P4info.merge (Type.tags header) info2 in
       Type.HeaderStack { header; size; tags } }
;

specializedType:
| base = prefixedType l_angle args = typeArgumentList info_r = r_angle
    { let tags = P4info.merge (Type.tags base) info_r in
      Type.SpecializedType { base; args; tags } }
;

baseType:
| info = BOOL
    { Type.Bool {tags = info} }
| info = ERROR
    { Type.Error {tags = info} }
| info = BIT
    { let width = Expression.Int {x = { value = Bigint.of_int 1;
                                        width_signed = None;
                                        tags = info};
                                  tags = info} in
      Type.BitType {expr = width; tags = info} }
| info1 = BIT l_angle value = INTEGER info_r = r_angle
    { let value_int : P4int.t = fst value in 
      let value_info = value_int.tags in
      let width = Expression.Int {x = value_int; tags = value_info} in
      let tags = P4info.merge info1 info_r in
      Type.BitType {tags; expr = width} }
| info1 = INT l_angle value = INTEGER info_r = r_angle
     { let value_int : P4int.t = fst value in 
       let value_info = value_int.tags in 
       let width = Expression.Int {tags = value_info; x = value_int} in
       let tags = P4info.merge info1 info_r in
      Type.IntType {tags; expr = width} }

| info1 = VARBIT l_angle value = INTEGER info_r = r_angle 
     { let value_int : P4int.t = fst value in 
       let value_info = value_int.tags in
       let max_width = Expression.Int {tags = value_info; x = value_int} in
       let tags = P4info.merge info1 info_r in
      Type.VarBit {tags; expr = max_width} }
| info1 = BIT l_angle L_PAREN width = expression R_PAREN info_r = r_angle
    { let tags = P4info.merge info1 info_r in
       Type.BitType {tags; expr = width} }
| info1 = INT l_angle L_PAREN width = expression R_PAREN info_r = r_angle
    { let tags = P4info.merge info1 info_r in
       Type.IntType {tags; expr = width} }
| info1 = VARBIT l_angle L_PAREN max_width = expression R_PAREN info_r = r_angle
    { let tags = P4info.merge info1 info_r in
       Type.VarBit {expr = max_width; tags} }
| info = INT
    { Type.Integer {tags = info} }
| info = STRING
    { Type.String {tags = info} }
;

typeOrVoid:
| t = typeRef
  { t }
| info = VOID
  { Type.Void {tags = info} }
| name = varName
  { let tags : P4info.t = name.tags in
    Type.TypeName {tags; name = BareName name } }    (* may be a type variable *)
;

optTypeParameters:
| (* empty *) { [] }
| l_angle types = separated_list(COMMA, typeParameter) r_angle
    { declare_types types;
      types }
;

typeParameter:
| name = name { name }
;

realTypeArg:
| info = DONTCARE
  { Type.DontCare {tags = info} }
| t = typeRef
  { t }
;

typeArg:
| info = DONTCARE { Type.DontCare {tags = info} }
| typ = typeRef { typ }
| name = nonTypeName
    { let tags : P4info.t = name.tags in
      Type.TypeName {tags; name = BareName name} }
| info = VOID { Type.Void {tags = info} }
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
  { d }
| ctd = controlTypeDeclaration pop_scope SEMICOLON
  { let tags, annotations, name, type_params, params = ctd in
    Declaration.ControlType { annotations; name; type_params; params; tags } }
| ptd = parserTypeDeclaration pop_scope SEMICOLON
  { let tags, annotations, name, type_params, params = ptd in
    Declaration.ParserType { annotations; name; type_params; params; tags } }
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
     { let tags = P4info.merge info1 info2 in 
        Declaration.Header { annotations; name; fields; tags } }
;

headerUnionDeclaration:
|  annotations = optAnnotations info1 = HEADER_UNION name = name
     L_BRACE fields = list(structField) info2 = R_BRACE
     { let tags = P4info.merge info1 info2 in
        Declaration.HeaderUnion { annotations; name; fields; tags } }
;

structTypeDeclaration:
|  annotations = optAnnotations info1 = STRUCT name = name
     L_BRACE fields = list(structField) info2 = R_BRACE
     { let tags = P4info.merge info1 info2 in 
        Declaration.Struct { annotations; name; fields; tags } }
;

structField:
|  annotations = optAnnotations typ = typeRef name = name info2 = SEMICOLON
     { let tags = P4info.merge (Type.tags typ) info2 in
       { tags; annotations; typ; name } : Declaration.field }
;

(* TODO : add support for serializable enums *)
enumDeclaration:
| annotations = optAnnotations info1 = ENUM name = name
    L_BRACE members = identifierList info2 = R_BRACE
    { let tags = P4info.merge info1 info2 in
      Declaration.Enum { annotations; name; members; tags } }
| annotations = optAnnotations info1 = ENUM typ = baseType
    name = name L_BRACE members = specifiedIdentifierList info4 = R_BRACE
   { let tags = P4info.merge info1 (Type.tags typ) in
     Declaration.SerializableEnum { annotations; typ; name; members; tags } }
;

errorDeclaration:
| info1 = ERROR L_BRACE members = identifierList info2 = R_BRACE
    { declare_vars members;
      let tags = P4info.merge info1 info2 in 
       Declaration.Error { members; tags } }
;

matchKindDeclaration:
| info1 = MATCH_KIND L_BRACE members = identifierList info2 = R_BRACE
    { declare_vars members;
       let tags = P4info.merge info1 info2 in
       Declaration.MatchKind { members; tags } }
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
    { let tags = P4info.merge info1 info2 in 
       Declaration.TypeDef { annotations; name; typ_or_decl = Left typ; tags }  }
| annotations = optAnnotations info1 = TYPEDEF
    decl = derivedTypeDeclaration name = name info2 = SEMICOLON
    { let tags = P4info.merge info1 info2 in
       Declaration.TypeDef { annotations; name; typ_or_decl = Right decl; tags }  }
| annotations = optAnnotations info1 = TYPE
    typ = typeRef name = name info2 = SEMICOLON
    { let tags = P4info.merge info1 info2 in 
       Declaration.NewType { annotations; name; typ_or_decl = Left typ; tags }  }
| annotations = optAnnotations info1 = TYPE
    decl = derivedTypeDeclaration name = name info2 = SEMICOLON
    { let tags = P4info.merge info1 info2 in 
       Declaration.NewType { annotations; name; typ_or_decl = Right decl; tags }  }
;

(*************************** STATEMENTS *************************)

assignmentOrMethodCallStatement:
| func = lvalue L_PAREN args = argumentList R_PAREN info2 = SEMICOLON
    { let type_args = [] in
      let tags = P4info.merge (Expression.tags func) info2 in 
       Statement.MethodCall { func; type_args; args; tags } }
| func = lvalue l_angle type_args = typeArgumentList r_angle
    L_PAREN args = argumentList R_PAREN info2 = SEMICOLON
    { let tags = P4info.merge (Expression.tags func) info2 in
       Statement.MethodCall { func; type_args; args; tags } }
| lhs = lvalue ASSIGN rhs = expression info2 = SEMICOLON
    { let tags = P4info.merge (Expression.tags lhs) info2 in 
      Statement.Assignment { lhs; rhs; tags } }
;

emptyStatement:
| info = SEMICOLON { Statement.EmptyStatement {tags = info} }
;

returnStatement:
| info1 = RETURN info2 = SEMICOLON
    { let tags = P4info.merge info1 info2 in 
       Statement.Return { expr = None; tags } }
| info1 = RETURN expr = expression info2 = SEMICOLON
    { let tags = P4info.merge info1 info2 in
       Statement.Return { expr = Some expr; tags } }
;

exitStatement:
| info1 = EXIT info2 = SEMICOLON
    { let tags = P4info.merge info1 info2 in
       Statement.Exit {tags} }
;

conditionalStatement:
| info1 = IF L_PAREN cond = expression R_PAREN tru = statement ELSE fls = statement
    { let info2 = Statement.tags fls in
      let fls = Some fls in
      let tags = P4info.merge info1 info2 in
       Statement.Conditional { cond; tru; fls; tags } }
| info1 = IF L_PAREN cond = expression R_PAREN tru = statement   %prec THEN
    { let fls = None in
      let tags = P4info.merge info1 (Statement.tags tru) in
       Statement.Conditional { cond; tru; fls; tags } }
;

(* To support direct invocation of a control or parser without instantiation *)
directApplication:
| typ = typeName DOT APPLY L_PAREN args = argumentList R_PAREN info2 = SEMICOLON
    { let tags = P4info.merge (Type.tags typ) info2 in
      Statement.DirectApplication { typ; args; tags } }
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
    { Statement.BlockStatement { tags = block.Block.tags; block } }
;

blockStatement:
|  annotations = optAnnotations
     info1 = L_BRACE
     push_scope
     statements = list(statementOrDeclaration) info2 = R_BRACE
     pop_scope
     { let tags = P4info.merge info1 info2 in 
       Block.{ tags; annotations; statements } }
;

switchStatement:
| info1 = SWITCH L_PAREN expr = expression R_PAREN L_BRACE cases = switchCases
  info2 = R_BRACE
    { let tags = P4info.merge info1 info2 in
       Statement.Switch { expr; cases; tags } }
;

switchCases : cases = list(switchCase) { cases } ;

switchCase:
| label = switchLabel COLON code = blockStatement
    { let tags = P4info.merge (Statement.tags_label label) code.Block.tags in
       Statement.Action { label; code; tags } }
| label = switchLabel info2 = COLON
    { let tags = P4info.merge (Statement.tags_label label) info2 in
      Statement.FallThrough { label; tags } }
;

switchLabel:
| name = name
  { let tags = name.tags in
    Statement.Name {name; tags} }
| info = DEFAULT
  { Statement.Default {tags = info} }
;

statementOrDeclaration:
| decl = variableDeclaration
| decl = constantDeclaration
| decl = instantiation
  { let tags = Declaration.tags decl in
    Statement.DeclarationStatement { decl; tags } }
| s = statement
  { s }
;

(************ TABLES *************)
tableDeclaration:
|  annotations = optAnnotations
     info1 = TABLE name = name L_BRACE properties = tablePropertyList
     info2 = R_BRACE
     { let tags = P4info.merge info1 info2 in
        Declaration.Table { annotations; name; properties; tags } }
;

tablePropertyList:
| props = nonempty_list(tableProperty) { props }
;

tableProperty:
| info1 = KEY ASSIGN L_BRACE elts = keyElementList info2 = R_BRACE
    { let tags = P4info.merge info1 info2 in
       Table.Key { keys = elts; tags } }
| info1 = ACTIONS ASSIGN L_BRACE acts = actionList info2 = R_BRACE
    { let tags = P4info.merge info1 info2 in
       Table.Actions { actions = acts; tags } }
| info1 = CONST ENTRIES ASSIGN L_BRACE entries = entriesList info2 = R_BRACE
    { let tags = P4info.merge info1 info2 in
       Table.Entries { entries = entries; tags } }
| info1 = CONST DEFAULT_ACTION ASSIGN act = actionRef info2 = SEMICOLON
    { let tags = P4info.merge info1 info2 in
      Table.DefaultAction {tags; action = act; const = true} }
| info1 = DEFAULT_ACTION ASSIGN act = actionRef info2 = SEMICOLON
    { let tags = P4info.merge info1 info2 in
      Table.DefaultAction {tags; action = act; const = false} }
| annos = optAnnotations
    info1 = CONST n = nonTableKwName ASSIGN v = initialValue info2 = SEMICOLON
    { let tags = P4info.merge info1 info2 in
       Table.Custom { annotations = annos; const = true; name = n; value = v; tags } }
| annos = optAnnotations
    n = nonTableKwName ASSIGN v = initialValue info2 = SEMICOLON
    { let tags = P4info.merge n.tags info2 in
       Table.Custom { annotations = annos; const = false; name = n; value = v; tags } }
;

keyElementList: elts = list(keyElement) { elts } ;

keyElement:
| key = expression COLON match_kind = name annotations = optAnnotations
    info2 = SEMICOLON
    { let tags = P4info.merge (Expression.tags key) info2 in
       Table.{ annotations; key; match_kind; tags } }
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
      Table.{ annotations = annos; matches = matches; action = act; tags = info } }
;

actionRef:
|  annotations = optAnnotations name = name
     { let tags = name.tags in
       { annotations; name = BareName name; args = []; tags } }
|  annotations = optAnnotations name = name L_PAREN args = argumentList
     info2 = R_PAREN
     { let tags = P4info.merge (name.tags) info2 in
        { annotations; name = BareName name; args; tags } }
|  annotations = optAnnotations
   info1 = dotPrefix go_toplevel name = nonTypeName go_local
     { let tags = name.tags in
       { annotations; name = QualifiedName ([], name); args = []; tags } }
|  annotations = optAnnotations 
   info1 = dotPrefix go_toplevel name = nonTypeName go_local
   L_PAREN args = argumentList info2 = R_PAREN
     { let tags = P4info.merge name.tags info2 in
        { annotations; name = QualifiedName ([], name); args; tags } }
;

(************************* ACTION ********************************)

actionDeclaration:
|  annotations = optAnnotations
     info1 = ACTION name = name L_PAREN params = parameterList R_PAREN
     body = blockStatement
     { let tags = P4info.merge info1 body.Block.tags in
        Declaration.Action { annotations; name; params; body; tags } }
;

(************************* VARIABLES *****************************)

variableDeclaration:
| annotations = optAnnotations
    typ = typeRef name = name init = optInitialValue info2 = SEMICOLON
    { declare_var name false;
      let tags = P4info.merge (Type.tags typ) info2 in
       Declaration.Variable { annotations; typ; name; init; tags } }
;

constantDeclaration:
| annotations = optAnnotations
    info1 = CONST typ = typeRef name = name ASSIGN value = initialValue
    info2 = SEMICOLON
    { let tags = P4info.merge info1 info2 in
       Declaration.Constant { annotations; typ; name; value; tags } }
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
      let tags = P4info.merge info1 body.Block.tags in
       Declaration.Function { return; name; type_params; params; body; tags } }
;

argumentList: args = separated_list(COMMA, argument) { args } ;

argument:
| value = expression
    { let tags = Expression.tags value in
      Argument.Expression { value; tags } }
| key = name ASSIGN value = expression
    { let tags = P4info.merge key.tags (Expression.tags value) in
       Argument.KeyValue { key; value; tags } }
| info = DONTCARE
    { Argument.Missing {tags = info} }
;

%inline kvPair:
| key = name ASSIGN value = expression 
  { let tags = P4info.merge key.tags (Expression.tags value) in
     KeyValue.{ key; value; tags } }

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
  { let tags = name.tags in
    Expression.Name {name = BareName name; tags } }
| info1 = dotPrefix go_toplevel name = nonTypeName go_local
  { let tags = P4info.merge info1 name.tags in
     Expression.Name {name = QualifiedName ([], name); tags } }
;

lvalue:
| expr = prefixedNonTypeName { expr }
| expr = lvalue DOT name = member
  { let tags = P4info.merge (Expression.tags expr) name.tags in
     Expression.ExpressionMember { expr; name; tags } }
| array = lvalue L_BRACKET index = expression info2 = R_BRACKET
    { let tags = P4info.merge (Expression.tags array) info2 in
       Expression.ArrayAccess { array; index; tags } }
| bits = lvalue L_BRACKET hi = expression COLON lo = expression
    info2 = R_BRACKET
    { let tags = P4info.merge (Expression.tags bits) info2 in
       Expression.BitStringAccess { bits; lo; hi; tags } }
;

expression:
| value = INTEGER
  { let value_int : P4int.t = fst value in 
    let tags = value_int.tags in 
    Expression.Int {x = value_int; tags} }
| info1 = TRUE
  { Expression.True {tags = info1} }
| info1 = FALSE
  { Expression.False {tags = info1} }
| value = STRING_LITERAL
  { let tags = value.tags in
    Expression.String {tags; str = value } }
| name = nonTypeName
  { let tags = name.tags in
     Expression.Name {name = BareName name; tags} }
| info1 = dotPrefix go_toplevel name = nonTypeName go_local
  { let tags = P4info.merge info1 name.tags in
    Expression.Name {name = QualifiedName ([], name); tags} }
| array = expression L_BRACKET index = expression info2 = R_BRACKET
  { let tags = P4info.merge (Expression.tags array) info2 in
     Expression.ArrayAccess { array; index; tags } }
| bits = expression L_BRACKET hi = expression COLON lo = expression
    info2 = R_BRACKET
  { let tags = P4info.merge (Expression.tags bits) info2 in
     Expression.BitStringAccess { bits; lo; hi; tags } }
| info1 = L_BRACE values = expressionList info2 = R_BRACE
  { let tags = P4info.merge info1 info2 in
     Expression.List { values; tags } }
| info1 = L_BRACE entries = kvList info2 = R_BRACE 
  { let tags = P4info.merge info1 info2 in 
     Expression.Record { entries; tags } }
| L_PAREN exp = expression R_PAREN
  { exp }
| info1 = NOT arg = expression %prec PREFIX
  { let tags = P4info.merge info1 (Expression.tags arg) in
     Expression.UnaryOp { op = Op.Not {tags = info1}; arg; tags } }
| info1 = COMPLEMENT arg = expression %prec PREFIX
  { let tags = P4info.merge info1 (Expression.tags arg) in
     Expression.UnaryOp{op = Op.BitNot {tags = info1}; arg; tags } }
| info1 = MINUS arg = expression %prec PREFIX
  { let tags = P4info.merge info1 (Expression.tags arg) in
     Expression.UnaryOp{op = UMinus {tags = info1}; arg; tags } }
| info1 = PLUS exp = expression %prec PREFIX
  { (*let info2,exp = exp in*)
    let tags = P4info.merge info1 (Expression.tags exp) in
    Expression.update_tags exp tags }
| info1 = L_PAREN typ = typeRef R_PAREN expr = expression %prec PREFIX
  { let tags = P4info.merge info1 (Expression.tags expr) in
     Expression.Cast { typ; expr; tags } }
| typ = prefixedTypeName DOT name = member
  { let tags = name.tags in
     Expression.TypeMember { typ; name; tags } }
| info1 = ERROR DOT name = member
  { let tags = P4info.merge info1 name.tags in
     Expression.ErrorMember {err = name; tags} }
| expr = expression DOT name = member
  { let tags = P4info.merge (Expression.tags expr) name.tags in
     Expression.ExpressionMember { expr; name; tags } }
| arg1 = expression op = binop arg2 = expression
  { let tags = P4info.merge (Expression.tags arg1) (Expression.tags arg2) in
     Expression.BinaryOp { op; args = (arg1, arg2); tags } }
| cond = expression QUESTION tru = expression COLON fls = expression
   { let tags = P4info.merge (Expression.tags cond) (Expression.tags fls) in
      Expression.Ternary { cond; tru; fls; tags } }
| func = expression l_angle type_args = realTypeArgumentList r_angle
    L_PAREN args = argumentList info2 = R_PAREN
   { let tags = P4info.merge (Expression.tags func) info2 in
      Expression.FunctionCall { func; type_args; args; tags } }
| func = expression L_PAREN args = argumentList info2 = R_PAREN
   { let type_args = [] in
     let tags = P4info.merge (Expression.tags func) info2 in
      Expression.FunctionCall { func; type_args; args; tags } }
| typ = namedType L_PAREN args = argumentList info2 = R_PAREN
   { let tags = P4info.merge (Type.tags typ) info2 in
      Expression.NamelessInstantiation { typ; args; tags } }
;

%inline binop:
| info = MUL
    { Op.Mul {tags = info} }
| info = DIV
   { Op.Div {tags = info} }
| info = MOD
   { Op.Mod {tags = info} }
| info = PLUS
   { Op.Plus {tags = info} }
| info = PLUS_SAT
   { Op.PlusSat {tags = info}}
| info = MINUS
   { Op.Minus {tags = info} }
| info = MINUS_SAT
   { Op.MinusSat {tags = info} }
| info = SHL
   { Op.Shl {tags = info} }
| info_r = r_angle info2 = R_ANGLE_SHIFT
   { let tags = P4info.merge info_r info2 in Op.Shr {tags} }
| info = LE
   { Op.Le {tags = info} }
| info = GE
   { Op.Ge {tags = info} }
| info = l_angle
   { Op.Lt {tags = info} }
| info_r = r_angle
   { Op.Gt {tags = info_r} }
| info = NE
   { Op.NotEq {tags = info} }
| info = EQ
   { Op.Eq {tags = info} }
| info = BIT_AND
   { Op.BitAnd {tags = info} }
| info = BIT_XOR
   { Op.BitXor {tags = info} }
| info = BIT_OR
   { Op.BitOr {tags = info} }
| info = PLUSPLUS
   { Op.PlusPlus {tags = info} }
| info = AND
   { Op.And {tags = info} }
| info = OR
   { Op.Or {tags = info} }
;

%inline r_angle:
| info_r = R_ANGLE { info_r } 
| info_r = R_ANGLE_SHIFT { info_r }

%inline l_angle:
| info_r = L_ANGLE { info_r } 
| info_r = L_ANGLE_ARGS { info_r }

(* À jour avec le commit 45df9f41a2cf1af56f4fa1cfaa1f586adefd13b7
   de p4-spec; à dotPrefix et listes près *)
