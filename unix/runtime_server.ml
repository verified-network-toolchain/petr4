open Core_kernel
open Cohttp_lwt
open Cohttp_lwt_unix
open Lwt.Infix

let petr4_uri name = 
  Uri.of_string (Printf.sprintf "http://localhost:9000/%s" name)

let rec loop handlers = 
  let%bind response,body = Client.get (petr4_uri "event") in 
  try 
    let%bind str = Body.to_string body in 
    let json = Yojson.Safe.from_string str in 
    let () = match Petr4.Runtime.message_of_yojson json with
      | Ok msg -> 
         handlers msg
      | Error err -> 
         Printf.eprintf "Unexpected error: %s" err in
    loop handlers
  with exn -> 
    Printf.eprintf "Unexpected error";
    loop handlers
    
let start ~handlers () = 
  let hello = Petr4.Runtime.Hello { switch = "s0"; ports = 1} in
  let body = hello |> Petr4.Runtime.message_to_yojson |> Yojson.Safe.to_string |> Body.of_string in
  let%bind response,body = Client.post ~body (petr4_uri "hello") in 
  loop handlers
