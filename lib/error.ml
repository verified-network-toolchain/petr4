open Types
open Typed

open Sexplib.Conv

type error =
| Unbound of string 
| Mismatch of
  { expected: string; (* TODO: string or Typed.t? *)
    found: ExpType.t; }
| UnfoundMember of 
  { expected_member: string}
| Type_Difference of ExpType.t * ExpType.t
| Duplicate
| UnreachableBlock
[@@deriving sexp]

exception Internal of string
exception Type of (Info.t * error) [@@deriving sexp]

let raise_mismatch info expected found =
  let err = Mismatch { expected; found } in
  raise (Type (info, err))

let raise_unfound_member info expected_member =
  let err = UnfoundMember { expected_member } in
  raise (Type (info, err))

let raise_type_error info err =
  raise (Type (info, err))

let raise_internal_error s = raise (Internal s)
