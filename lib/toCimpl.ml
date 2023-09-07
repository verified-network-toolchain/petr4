open Poulet4
open Cimpl
open Core

let name_of_top (t : AST.Top.t) : string =
  match t with
  | Instantiate (_,n,_,_,_) -> n
  | Extern (n,_,_,_,_) -> n
  | Control (n,_,_,_,_,_,_) -> n
  | Parser (n,_,_,_,_,_,_) -> n
  | Funct (n,_,_,_) -> n

let is_instantiate (t:AST.Top.t) : bool =
  match t with
  | Instantiate _ -> true
  | Extern _ -> false
  | Control _ -> false
  | Parser _ -> false
  | Funct _ -> false
     
let get_v1model_instances (prog:ToP4cub.coq_DeclCtx) =
  let f t = is_instantiate t && String.equal (name_of_top t) "main" in
  match List.find prog.packages ~f with
  | Some Instantiate(_,_,_,_,[p;v;i;e;u;d]) ->
     (p,v,i,e,u,d)
  | Some _ ->
     failwith "Unexpected error: wrong number of arguments to 'main'"
  | None ->
     failwith "Unexpected error: 'main' not found"
   
let compile_program (prog:ToP4cub.coq_DeclCtx) : (cprog,string) result = 
  let p,v,i,e,u,d = get_v1model_instances prog in
  let _ = ignore (p,v,i,e,u,d) in 
  Ok (Cimpl.CProgram [])
