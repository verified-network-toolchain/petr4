type ctyp =
  | CVoid
  | CInt

type cvar = string
  
type cexpr =
  | CVar of cvar

type cstmt =
  | CSkip
  | CAssign of cvar * cexpr

and cblk =
  | CBlock of cstmt list
               
type cdecl =
  | CFunction of ctyp * string * cblk
                 
type cprog =
  | CProgram of cdecl list 
