open! Core
open! Petr4
open Poulet4
open GCL
open Semantics

type gcl = (string, BitVec.t, Form.t) GCL.t

let denote (a:Arch.t) (s:store) (g:gcl) : (string, store list) Result.result = Semantics.denote a s g

let%test "dummy" = false

let%test "first GCL" =
  let g = GCL.GSkip in
  let a = [] in
  let s = [] in
  match denote a s g with
  | Result.Ok [[]] -> true
  | _ -> false
     
      
