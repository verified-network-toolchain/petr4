type bop =
  | Add
  | Sub
  | Mult
  | Div
  | Eq
  | Neq
  | Lt
  | Gt
  | Le
  | Ge
  | And
  | Or
  | BAnd
  | BOr
  | BXor
  | BShl
  | BShr

type uop =
  | Not
  | BNot

type test =
  | Int of Int64.t
  | Ident of string
  | Defined of string
  | BinOp of test * bop * test
  | UnOp of uop * test

type term =
  | String of string
  | Text of string
  | Include of int * bool * string
  | Define of string
  | Undef of string
  | IfDef of string * int * term list * int * term list * int
  | IfNDef of string * int * term list * int * term list * int
  | If of test * int * term list * int * term list * int
