(*type ctyp =
  | CTVoid
  | CTInt

type cvar = string
  
type cexpr =
  | CEVar of cvar
  | CEInt of int
          
  type cstmt =
  | CSSkip
  | CSAssign of cvar * cexpr
  | CSIf of cexpr * cstmt * cstmt 

and cblk =
  | CBlock of cstmt list
               
type cdecl =
  | CDFunction of ctyp * string * cblk
                 
type cprog =
  | CProgram of cdecl list 
*) 

type ctyp =
  | CTVoid
  | CTInt

type cvar = string

type bop = 
(*rational operators*)
  | EQ (*equal*)
  | NE (*not equal*)
  | LT (*less than*)
  | GT (*greater than*)
  | GTE (*greater than equal*)
  | LTE (*less than equal*)
(*logical operators*)
  | And  
  | Or
(*arithmetic operators*)
  | Add 
  | Sub 
  | Mul 
  | Div 
  | Mod 
  
type uop = 
  | Neg

type cexpr =
  | CEVar of cvar
  (*no booleans so using 1 -> TRUE and 0 -> FALSE*)
  | CEInt of int
  | CCompExpr of bop * cexpr * cexpr
  | CUniExpr of uop * cexpr
  (*change to statement*)

type cstmt =
  | CSSkip
  | CSAssign of cvar * cexpr
  | CSIf of cexpr * cstmt list * cstmt list

and cblk =
  | CBlock of cstmt list
               
type cdecl =
  | CDFunction of ctyp * string * cblk
                 
type cprog =
  | CProgram of cdecl list 

