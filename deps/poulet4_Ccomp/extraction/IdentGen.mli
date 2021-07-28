open AST
open BinNums
open BinPosDef

type generator = ident

val gen_init : generator

val gen_next : generator -> generator * ident
