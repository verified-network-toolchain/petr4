type ctyp =
  | CTVoid
  | CTInt

type cvar = string

type bop = 
  | CBEq
  | CBNe
  | CBLt
  | CBGt
  | CBGte
  | CBLte
  | CBAnd  
  | CBOr
  | CBAdd 
  | CBSub 
  | CBMul 
  | CBDiv 
  | CBMod 
  
type uop = 
  | Neg

type cexpr =
  | CEVar of cvar
  | CEInt of int
  | CECompExpr of bop * cexpr * cexpr
  | CEUniExpr of uop * cexpr

type cstmt =
  | CSSkip
  | CSAssign of cvar * cexpr
  | CSIf of cexpr * cstmt list * cstmt list

and cblk =
  | CKBlock of cstmt list
               
type cdecl =
  | CDFunction of ctyp * string * cblk
                 
type cprog =
  | CProgram of cdecl list 

