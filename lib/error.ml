open Typed
open Sexplib.Conv

type error =
  | Unbound of string
  | Mismatch of
      { expected: string; (* TODO: string or Typed.t? *)
        found: Type.t; }
  | UnfoundMember of
      { expected_member: string}
  | Type_Difference of Type.t * Type.t
  | Duplicate
  | UnreachableBlock
[@@deriving sexp]

let format_error fmt = function
  | Unbound x -> 
     Format.fprintf fmt "error: %s unbound" x
  | Mismatch { expected; found } -> 
     Format.fprintf fmt "error: type mismatch, expected %s but found <...>" 
       expected
  | UnfoundMember { expected_member } -> 
     Format.fprintf fmt "error: no such member %s" expected_member
  | Type_Difference(t1,t2) -> 
     Format.fprintf fmt "error: different types <...> and <...>"
  | Duplicate -> 
     Format.fprintf fmt "error: duplicate"
  | UnreachableBlock -> 
     Format.fprintf fmt "error: unreachable block"
     
<<<<<<< HEAD
exception Internal of string [@@deriving sexp]
exception Type of (Info.t * error) [@@deriving sexp]
=======
exception Internal of string
exception Type of (P4info.t * error)
>>>>>>> 62cd2770 (wip fix menhir build errors)
exception V1AssertionError

let raise_mismatch info expected found =
  let err = Mismatch { expected; found } in
  raise (Type (info, err))

let raise_unfound_member info expected_member =
  let err = UnfoundMember { expected_member } in
  raise (Type (info, err))

let raise_type_error info err =
  raise (Type (info, err))

let raise_internal_error s = raise (Internal s)

let v1_assert () = raise V1AssertionError
