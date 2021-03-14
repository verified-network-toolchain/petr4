(* This file defines abstract syntax for building C programs that use
   the Petr4 C compiler's runtime.

   Design direction:
   - This is not a complete syntax for C. We can extend it as needed,
     but let's not get ahead of ourselves.
   - When the runtime offers a primitive op, we try to provide
     abstract syntax for the op, leaving the actual translation to a
     call to the runtime up to the pretty-printer pass.
   - In order for the previous bullet to work, programs built in this
     syntax must link to the Petr4 C runtime.
*)

type cname = string
type ctyp =
    CVoid
  | CInt
  | CChar
  | CBit8
  | CUInt
  | CBool
  | CTypeName of cname
  | CPtr of ctyp
type cdecl =
    CStruct of cname * cfield list
  | CFun of ctyp * cname * cparam list * cstmt list
  | CInclude of string
  | CStdInclude of string
  | CDecList of cdecl list 
and cfield = CField of ctyp * cname
and cparam = CParam of ctyp * cname
and cstmt =
  | CRet of cexpr
  | CSeq of cstmt * cstmt
  | CIf of cexpr * cstmt * cstmt
  | CIfElifElse of cexpr * cstmt * (cexpr * cstmt) list * cstmt 
  | CAssign of cexpr * cexpr
  | CVarInit of ctyp * cname * cexpr
  | CMethodCall of cname * cexpr list  
  | CSwitch of cexpr * ccase list
  | CBlock of cstmt list
  | CWhile of cexpr * cstmt
and ccase =
  | CCase of cexpr * cstmt list
and cexpr =
    CIntLit of int
  | CVar of cname
  | CDeref of cexpr
  | CAddrOf of cexpr
  | CMember of cexpr * cname
  | CCall of cname * cexpr list
  | CBoolExp of bool
  | CString of cname 
  | CGeq of cexpr * cexpr
  | CPointer of cexpr * cname

type cprog = cdecl list
