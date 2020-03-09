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
open Parser

exception Error of string

let current_line  = ref 1

type lexer = Keyword | Packet_data
let lexer = ref Keyword

let newline () =
  incr current_line
}

let white = [' ' '\t' '\r']
let whitespace = white+
let opt_whitespace = white*


let identifier = ['_' 'A'-'Z' 'a'-'z']['_' 'A'-'Z' 'a'-'z' '0'-'9']*

let q_chars = [^ '"' '\n']+
let h_chars = [^ '>' '\n']+
let digits = ['0'-'9']+

let binary_constant = '0'['b' 'B']['*' '0' '1']+

let hex_prefix = '0'['x' 'X']

let hex_digits = ['0'-'9' 'a'-'f' 'A'-'F']
let hex_constant_body = hex_digits+
let hex_constant = hex_prefix hex_constant_body
let hex_tern = ['0'-'9' 'a'-'f' 'A'-'F' '*']+
let hex_tern_constant = hex_prefix hex_tern
let identifier = ['a'-'z' '$' 'A'-'Z' '_']['a'-'z' '$' 'A'-'Z' '_' '0'-'9']*

rule token = parse
  | ""
    { match !lexer with
      | Keyword -> keyword lexbuf
      | Packet_data -> packet_data lexbuf }

and keyword = parse
  | ':'
      { COLON }
  | ','
      { COMMA }
  | '.'
      { DOT }
  | '['
      { LBRACKET }
  | ']'
      { RBRACKET }
  | '('
      { LPAREN }
  | ')'
      { RPAREN }
  | '='
      { EQUAL }
  | "=="
      { EQEQ }
  | "!="
      { NEQ }
  | '<'
      { LE }
  | "<="
      { LEQ }
  | '>'
      { GT }
  | ">="
      { GEQ }
  | '/'
      { SLASH }
  | "add"
    { ADD }
  | "all"
    { ALL }
  | "bytes"
    { BYTES }
  | "check_counter"
    { CHECK_COUNTER }
  | "expect"
    { lexer:= Packet_data; EXPECT}
  | "no_packet"
    { NO_PACKET }
  | "packet"
    { lexer:= Packet_data; PACKET }
  | "packets"
    { PACKETS }
  | "remove"
    { REMOVE }
  | "setdefault"
    { SETDEFAULT }
  | "wait"
    { WAIT }
  | '\n'
    { newline (); keyword lexbuf }
  | whitespace
    { keyword lexbuf }
  | '#' [^'\n']* '\n'
    { newline(); keyword lexbuf }
  | eof
    { END }

and packet_data = parse
  | digits
    { DATA_DEC(lexeme lexbuf) }
  | hex_constant_body
    { DATA_HEX(lexeme lexbuf) }
  | '*'
    { DATA_TERN }
  | '\n'+
    { lexer:= Keyword; keyword lexbuf }
  | whitespace
    { packet_data lexbuf }

{
}
