type ctyp =
  | CVoid
  | CInt

type cexpr =
  | CVar of string

type cstmt =
  | CSkip

and cblk =
  | CBlock of cstmt list
               
type cdecl =
  | CFunction of ctyp * string * cblk
                 
type cprog =
  | CProgram of cdecl list 


