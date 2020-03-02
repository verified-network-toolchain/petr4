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
open Core_kernel
open Ast
%}

%token END
%token ADD ALL BYTES CHECK_COUNTER EXPECT NO_PACKET PACKET PACKETS REMOVE SETDEFAULT WAIT
%token COLON COMMA DATA_DEC DATA_HEX DATA_TERN DOT ID INT_CONST_BIN
%token INT_CONST_DEC TERN_CONST_HEX INT_CONST_HEX LBRACKET RBRACKET
%token LPAREN RPAREN SLASH EQUAL EQEQ LE LEQ GT GEQ NEQ


%start <Ast.term list> program

%%

program:
  term* END
  { $1 }
;

term:
  | STRING
      { String($1) }
  | TEXT
      { Text($1) }
  | INCLUDE
      { let line, search, filename = $1 in
        Include(line, search, filename) }
  | DEFINE
      { Define($1) }
  | UNDEF
      { Undef($1) }
  | IFDEF term* ENDIF
      { let line1, macro = $1 in
        let line2 = $3 in
        IfDef(macro, line1, $2, line2, [], line2) }
  | IFDEF term* ELSE term* ENDIF
      { let line1, macro = $1 in
        let line2 = $3 in
        let line3 = $5 in
        IfDef(macro, line1, $2, line2, $4, line3) }
  | IFNDEF term* ENDIF
      { let line1, macro = $1 in
        let line2 = $3 in
        IfNDef(macro, line1, $2, line2, [], line2) }
  | IFNDEF term* ELSE term* ENDIF
      { let line1, macro = $1 in
        let line2 = $3 in
        let line3 = $5 in
        IfNDef(macro, line1, $2, line2, $4, line3) }
  | IF test term* ENDIF
      { let line1 = $1 in
        let line2 = $4 in
        If($2, line1, $3, line2, [], line2) }
  | IF test term* ELSE term* ENDIF
      { let line1 = $1 in
        let line2 = $4 in
        let line3 = $6 in
        If($2, line1, $3, line2, $5, line3) }

test:
  | INT
    { Int($1) }
  | IDENT
    { Ident($1) }
  | DEFINED LPAREN IDENT RPAREN
    { Defined($3) }
  | test ADD test
    { BinOp($1, Add, $3) }
  | test SUB test
    { BinOp($1, Sub, $3) }
  | test MULT test
    { BinOp($1, Mult, $3) }
  | test DIV test
    { BinOp($1, Div, $3) }
  | test EQ test
    { BinOp($1, Eq, $3) }
  | test NEQ test
    { BinOp($1, Neq, $3) }
  | test GT test
    { BinOp($1, Gt, $3) }
  | test LT test
    { BinOp($1, Lt, $3) }
  | test LE test
    { BinOp($1, Le, $3) }
  | test GE test
    { BinOp($1, Ge, $3) }
  | test AND test
    { BinOp($1, And, $3) }
  | test OR test
    { BinOp($1, Or, $3) }
  | NOT test
    { UnOp(Not, $2) }
  | test BAND test
    { BinOp($1, BAnd, $3) }
  | test BOR test
    { BinOp($1, BOr, $3) }
  | BNOT test
    { UnOp(BNot, $2) }
  | test BSHL test
    { BinOp($1, BShl, $3) }
  | test BSHR test
    { BinOp($1, BShr, $3) }
  | test BXOR test
    { BinOp($1, BXor, $3) }
  | LPAREN test RPAREN
    { $2 }
