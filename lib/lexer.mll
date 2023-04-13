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
{
open Lexing
open Context
open P4parser
open Poulet4.P4String
open Poulet4.P4Int

module S = String
module String = S

exception Error of string

let current_line  = ref 1 
let current_fname = ref ""
let line_start    = ref 1

type lexer_state =
  | SRegular (* Nothing to recall from the previous tokens. *)
  | SRangle of P4info.t
  | SPragma
  | STemplate
    (* We have seen a template *)
  | SIdent of P4string.t * lexer_state
    (* We have seen an identifier: we have just
     * emitted a [NAME] token. The next token will be
     * either [IDENTIFIER] or [TYPENAME], depending on
     * what kind of identifier this is. *)

let lexer_state = ref SRegular
    
let reset () =
  Context.reset ();
  lexer_state := SRegular;
  current_line := 1;
  current_fname := "";
  line_start := 1

let line_number () =
  !current_line
let filename () =
  !current_fname
let start_of_line () =
  !line_start

let set_line n =
  current_line  :=  n

let set_start_of_line c =
  line_start := c

let set_filename s =
  current_fname := s

let newline lexbuf =
  current_line := line_number() + 1 ;
  set_start_of_line (lexeme_end lexbuf)

let info lexbuf : P4info.t =
  let f = filename () in
  let c1 = lexeme_start lexbuf in
  let c2 = lexeme_end lexbuf in
  let c = start_of_line () in
  let l = line_number() in
  P4info.I { filename=f; line_start=l; line_end=None; col_start=c1-c; col_end=c2-c }

let sanitize s =
  String.concat "" (String.split_on_char '_' s)

let strip_prefix s =
  let length = String.length s in
  assert (length > 2);
  String.sub s 2 (length - 2)

let parse_int n info =
  let value = Bigint.of_string (sanitize n) in
  {tags=info; value; width_signed=None}

let parse_width_int s n info =
  let l_s = String.length s in
  let width = String.sub s 0 (l_s - 1) in
  let sign = String.sub s (l_s - 1) 1 in
  let value = Bigint.of_string (sanitize n) in
  let width_signed = match sign with
      "s" ->
      if (int_of_string width < 2)
      then raise (Error "signed integers must have width at least 2")
      else Some (Bigint.of_string width, true)
    | "w" ->
      Some (Bigint.of_string width, false)
    | _ -> 
      raise (Error "Illegal integer constant")
  in
  {tags=info; value = value; width_signed}
}

let name = ['A'-'Z' 'a'-'z' '_'] ['A'-'Z' 'a'-'z' '0'-'9' '_']*
let hex_number = '0' ['x' 'X'] ['0'-'9' 'a'-'f' 'A'-'F' '_']+
let dec_number = '0' ['d' 'D'] ['0'-'9' '_']+
let oct_number = '0' ['o' 'O'] ['0'-'7' '_']+
let bin_number = '0' ['b' 'B'] ['0' '1' '_']+
let int = ['0'-'9'] ['0'-'9' '_']*
let sign = ['0'-'9']+ ['w' 's']

let whitespace = [' ' '\t' '\012' '\r']

rule tokenize = parse
  | "/*"
      { match multiline_comment None lexbuf with 
         | None -> tokenize lexbuf
         | Some info -> PRAGMA_END (info) }
  | "//"
      { singleline_comment lexbuf; tokenize lexbuf }
  | '\n'
      { newline lexbuf; PRAGMA_END(info lexbuf) }
  | '"'
      { let str, end_info = (string lexbuf) in
        STRING_LITERAL ({tags=P4info.merge (info lexbuf) end_info; str}) }
  | whitespace
      { tokenize lexbuf }
  | '#'
      { preprocessor lexbuf ; tokenize lexbuf }
  | "@pragma"
      { PRAGMA(info lexbuf) }
  | hex_number as n
    { INTEGER (parse_int n (info lexbuf), n) }
  | dec_number as n
    { INTEGER (parse_int (strip_prefix n) (info lexbuf), n) }
  | oct_number as n
    { INTEGER (parse_int n (info lexbuf), n) }
  | bin_number as n
    { INTEGER (parse_int n (info lexbuf), n) }
  | int as n
    { INTEGER (parse_int n (info lexbuf), n) }
  | (sign as s) (hex_number as n)
    { INTEGER (parse_width_int s n (info lexbuf), n) }
  | (sign as s) (dec_number as n)
    { INTEGER (parse_width_int s (strip_prefix n) (info lexbuf), n) }
  | (sign as s) (oct_number as n)
    { INTEGER (parse_width_int s n (info lexbuf), n) }
  | (sign as s) (bin_number as n)
    { INTEGER (parse_width_int s n (info lexbuf), n) }
  | (sign as s) (int as n)
    { INTEGER (parse_width_int s n (info lexbuf), n) }
  | "abstract"
      { ABSTRACT (info lexbuf) }
  | "action"
      { ACTION (info lexbuf) }
  | "actions"
      { ACTIONS (info lexbuf) }
  | "apply"
      { APPLY (info lexbuf) }
  | "bool"
      { BOOL (info lexbuf) }
  | "bit"
      { BIT (info lexbuf) }
  | "const"
      { CONST (info lexbuf) }
  | "control"
      { CONTROL (info lexbuf) }
  | "default"
      { DEFAULT (info lexbuf) }
  | "default_action"
      { DEFAULT_ACTION (info lexbuf) }
  | "else"
      { ELSE (info lexbuf) }
  | "entries"
      { ENTRIES (info lexbuf) }
  | "enum"
      { ENUM (info lexbuf) }
  | "error"
      { ERROR (info lexbuf) }
  | "exit"
      { EXIT (info lexbuf) }
  | "extern"
      { EXTERN (info lexbuf) }
  | "header"
      { HEADER (info lexbuf) }
  | "header_union"
      { HEADER_UNION (info lexbuf) }
  | "true"
      { TRUE (info lexbuf) }
  | "false"
      { FALSE (info lexbuf) }
  | "if"
      { IF (info lexbuf) }
  | "in"
      { IN (info lexbuf) }
  | "inout"
      { INOUT (info lexbuf) }
  | "int"
      { INT (info lexbuf) }
  | "key"
      { KEY (info lexbuf) }
  | "match_kind"
      { MATCH_KIND (info lexbuf) }
  | "out"
      { OUT (info lexbuf) }
  | "parser"
      { PARSER (info lexbuf) }
  | "package"
      { PACKAGE (info lexbuf) }
  | "pragma" 
      { PRAGMA (info lexbuf) }
  | "return"
      { RETURN (info lexbuf) }
  | "select"
      { SELECT (info lexbuf) }
  | "state"
      { STATE (info lexbuf) }
  | "string"
      { STRING (info lexbuf) }
  | "struct"
      { STRUCT (info lexbuf) }
  | "switch"
      { SWITCH (info lexbuf) }
  | "table"
      { TABLE (info lexbuf) }
  | "transition"
      { TRANSITION (info lexbuf) }
  | "tuple"
      { TUPLE (info lexbuf) }
  | "typedef"
      { TYPEDEF (info lexbuf) }
  | "type"
      { TYPE (info lexbuf) }
  | "value_set"
      { VALUESET (info lexbuf) }
  | "varbit"
      { VARBIT (info lexbuf) }
  | "void"
      { VOID (info lexbuf) }
  | "_"
      { DONTCARE (info lexbuf) }
  | name
      { NAME ({tags=info lexbuf; str=Lexing.lexeme lexbuf}) }
  | "<="
      { LE (info lexbuf) }
  | ">="
      { GE (info lexbuf) }
  | "<<"
      { SHL (info lexbuf) }
  | "&&"
      { AND (info lexbuf) }
  | "||"
      { OR (info lexbuf) }
  | "!="
      { NE (info lexbuf) }
  | "=="
      { EQ (info lexbuf) }
  | "+"
      { PLUS (info lexbuf) }
  | "-"
      { MINUS (info lexbuf) }
  | "|+|"
      { PLUS_SAT (info lexbuf) }
  | "|-|"
      { MINUS_SAT (info lexbuf) }
  | "*"
      { MUL (info lexbuf) }
  | "/"
      { DIV (info lexbuf) }
  | "%"
      { MOD (info lexbuf) }
  | "|"
      { BIT_OR (info lexbuf) }
  | "&"
      { BIT_AND (info lexbuf) }
  | "^"
      { BIT_XOR (info lexbuf) }
  | "~"
      { COMPLEMENT (info lexbuf) }
  | "["
      { L_BRACKET (info lexbuf) }
  | "]"
      { R_BRACKET (info lexbuf) }
  | "{"
      { L_BRACE (info lexbuf) }
  | "}"
      { R_BRACE (info lexbuf) }
  | "<"
      { L_ANGLE (info lexbuf) }
  | ">"
      { R_ANGLE (info lexbuf) }
  | "("
      { L_PAREN (info lexbuf) }
  | ")"
      { R_PAREN (info lexbuf) }
  | "!"
      { NOT (info lexbuf) }
  | ":"
      { COLON (info lexbuf) }
  | ","
      { COMMA (info lexbuf) }
  | "?"
      { QUESTION (info lexbuf) }
  | "."
      { DOT (info lexbuf) }
  | "="
      { ASSIGN (info lexbuf) }
  | ";"
      { SEMICOLON (info lexbuf) }
  | "@"
      { AT (info lexbuf) }
  | "++"
      { PLUSPLUS (info lexbuf) }
  | "&&&"
      { MASK (info lexbuf) }
  | ".."
      { RANGE (info lexbuf) }
  | eof
      { END (info lexbuf) }
  | _
      { UNEXPECTED_TOKEN({tags=info lexbuf; str=lexeme lexbuf}) }
      
and string = parse
  | eof
      { raise (Error "File ended while reading a string litteral" ) }
  | "\\\""
      { let rest, end_info = (string lexbuf) in
        ("\"" ^ rest, end_info) }
  | '\\' 'n'
      { let rest, end_info = (string lexbuf) in
        ("\n" ^ rest, end_info) }
  | '\\' '\\'
      { let rest, end_info = (string lexbuf) in
        ("\\" ^ rest, end_info) }
  | '\\' _ as c
    { raise (Error ("Escape sequences not yet supported: \\" ^ c)) }
  | '"'
      { ("", info lexbuf) }
  | _ as chr
    { let rest, end_info = (string lexbuf) in
      ((String.make 1 chr) ^ rest, end_info) }
    
(* Preprocessor annotations indicate line and filename *)
and preprocessor = parse
  | ' '
      { preprocessor lexbuf }
  | int
      { let line = int_of_string (lexeme lexbuf) in
        set_line line ; preprocessor lexbuf }
      
  | '"'
      { preprocessor_string lexbuf }
      
  | '\n'
      { set_start_of_line (lexeme_end lexbuf) }
  | _
      { preprocessor lexbuf }
      
and preprocessor_string = parse
  | [^ '"']* '"'
    { let filename = lexeme lexbuf in 
      let filename = String.sub filename 0 (String.length filename - 1) in
      set_filename filename;
      preprocessor_column lexbuf }
      
(* Once a filename has been recognized, ignore the rest of the line *)
and preprocessor_column = parse
  | ' ' 
      { preprocessor_column lexbuf }
  | '\n'
      { set_start_of_line (lexeme_end lexbuf) }
  | eof
      { () }
  | _
      { preprocessor_column lexbuf }
      
(* Multi-line comment terminated by "*/" *)
and multiline_comment opt = parse
  | "*/"   { opt }
  | eof    { failwith "unterminated comment" }
  | '\n'   { newline lexbuf; multiline_comment (Some(info lexbuf)) lexbuf }
  | _      { multiline_comment opt lexbuf }
      
(* Single-line comment terminated by a newline *)
and singleline_comment = parse
  | '\n'   { newline lexbuf }
  | eof    { () }
  | _      { singleline_comment lexbuf }
      
{

let rec lexer (lexbuf:lexbuf) : token = 
   match !lexer_state with
    | SIdent(id,next) ->
      begin match get_kind id with
      | TypeName true ->
        lexer_state := STemplate;
        TYPENAME
      | Ident true ->
        lexer_state := STemplate;
        IDENTIFIER
      | TypeName false ->
        lexer_state := next;
        TYPENAME
      | Ident false ->
        lexer_state := next;
        IDENTIFIER
      end
    | SRangle info1 -> 
      begin 
        match tokenize lexbuf with
        | R_ANGLE info2 when P4info.follows info1 info2 -> 
          lexer_state := SRegular;
          R_ANGLE_SHIFT info2
        | PRAGMA _ as token ->
          lexer_state := SPragma;
          token
        | PRAGMA_END _ -> 
          lexer_state := SRegular;
          lexer lexbuf
        | NAME id as token ->
          lexer_state := SIdent (id, SRegular);
          token          
        | token -> 
          lexer_state := SRegular;
          token
      end
    | SRegular ->
      begin 
        match tokenize lexbuf with
        | NAME id as token ->
          lexer_state := SIdent(id, SRegular);
          token
       |  PRAGMA _ as token ->
          lexer_state := SPragma;
          token
        | PRAGMA_END _ ->
          lexer lexbuf
        | R_ANGLE info as token -> 
          lexer_state := SRangle info;
          token
        | token ->
          lexer_state := SRegular;
          token
       end
    | STemplate ->
      begin match tokenize lexbuf with
      | L_ANGLE info ->
        L_ANGLE_ARGS info
      | NAME id as token ->
        lexer_state := SIdent(id, SRegular);
        token
      | PRAGMA _ as token ->
        lexer_state := SPragma;
        token
      | PRAGMA_END _ ->
        lexer lexbuf
      | R_ANGLE info as token -> 
        lexer_state := SRangle info;
        token
      | token ->
        lexer_state := SRegular;
        token
       end
    | SPragma -> 
      begin 
        match tokenize lexbuf with
        | PRAGMA_END info as token -> 
           lexer_state := SRegular;
           token
        | NAME id as token -> 
           lexer_state := SIdent(id, SPragma);
           token
        | token -> 
           token
      end
}
