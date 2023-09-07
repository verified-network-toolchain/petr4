(** Cimpl is a small subset of C. It is not intended to capture the
 *  entire language, but rather to serve as a compilation target for
 *  Petr4. 
 * 
 * It inherits the usual conventions of C. For instance there
 *  are not booleans and instead `0` is interpreted as `false` and any
 *  non-zero value is interpreted as `true`.  
 * 
 * The datatypes in this file use the following conventions:
 * - All constructors start with `C`
 * - The next letter indicates the "kind" of term that it is:
 *   + `T` for types
 *   + `E` for expressions
 *   + `D` for declarations
 *   and so on...
 *)

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
  | CUNeg
  
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
