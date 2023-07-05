type ctyp =
  | CTVoid
  | CTInt

type cvar = string
  
type cexpr =
  | CEVar of cvar
  | CEInt of int

type cstmt =
  | CSSkip
  | CSAssign of cvar * cexpr

and cblk =
  | CBlock of cstmt list
               
type cdecl =
  | CDFunction of ctyp * string * cblk
                 
type cprog =
  | CProgram of cdecl list 
