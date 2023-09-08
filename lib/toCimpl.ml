open Poulet4
open AST
open ToP4cub
open Cimpl
open Core
open Result.Let_syntax

type ctx = coq_DeclCtx

type error =
  | NotFound of string
  | V1Model of string

let string_of_error = function
  | NotFound msg -> msg
  | V1Model msg -> msg

type 'a result = ('a,error) Core.result 

let name_of_top (t : Top.t) : string =
  match t with
  | Instantiate (_,n,_,_,_) -> n
  | Extern (n,_,_,_,_) -> n
  | Control (n,_,_,_,_,_,_) -> n
  | Parser (n,_,_,_,_,_,_) -> n
  | Funct (n,_,_,_) -> n

let lookup (l:Top.t list) (n:string) : Top.t result =
  let f t = String.equal (name_of_top t) n in
  match List.find l ~f with
  | Some c ->
    Ok c
  | None ->
    Error (NotFound n)

let lookup_package prog = lookup prog.packages
let lookup_controls prog = lookup prog.controls
let lookup_parser prog = lookup prog.parsers
 
let get_v1model_instances (ctx:ctx) =
  match%bind lookup_package ctx "main" with
  | Instantiate(_,_,_,_,[p;v;i;e;u;d]) ->
    Ok (p,v,i,e,u,d)
  | _ ->
    Error (V1Model ("'main' is not well-formed for V1Model"))

let compile_control (c:Ctrl.t) (args:Exp.t list) : cstmt result =
  Ok (Cimpl.CSSkip)  

let compile_program (ctx:ctx) : cprog result = 
  let%bind p,v,i,e,u,d = get_v1model_instances ctx in
  let _ = ignore (p,v,i,e,u,d) in 
  Ok (Cimpl.CProgram [])
