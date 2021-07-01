open Core_kernel
open Cohttp_lwt
open Cohttp_lwt_unix
open Lwt.Infix

let petr4_uri name = 
  Uri.of_string (Printf.sprintf "http://localhost:9000/%s" name)

let rec loop switch handlers = 
  let event = Petr4.Runtime.Event { switch } in
  let body = event |> Petr4.Runtime.switch_msg_to_yojson |> Yojson.Safe.to_string |> Body.of_string in
  let%bind response,body = Client.post ~body (petr4_uri "event") in 
  try 
    let%bind str = Body.to_string body in 
    let json = Yojson.Safe.from_string str in 
    let () = match Petr4.Runtime.ctrl_msg_of_yojson json with
      | Ok msg -> 
         handlers msg
      | Error err -> 
         Printf.eprintf "Unexpected parsing error: %s\n%s\n%!" err str in
    loop switch handlers
  with exn ->
    Printf.eprintf "Unexpected error: %s\n%!" (Exn.to_string exn);
    loop switch handlers
    
let start switch ~handlers () = 
  let hello = Petr4.Runtime.Hello { switch = switch; ports = 1} in
  let body = hello |> Petr4.Runtime.switch_msg_to_yojson |> Yojson.Safe.to_string |> Body.of_string in
  let%bind response,body = Client.post ~body (petr4_uri "hello") in
  let%bind () = Cohttp_lwt.Body.drain_body body in 
  loop switch handlers

let post_packet switch in_port packet =
  let pkt = Petr4.Runtime.PacketIn { switch; in_port; packet } in
  let body =
    pkt
    |> Petr4.Runtime.switch_msg_to_yojson
    |> Yojson.Safe.to_string
    |> Body.of_string in
  let%bind response, body = Client.post ~body (petr4_uri "packet_in") in
  let%bind () = Cohttp_lwt.Body.drain_body body in
  Lwt.return ()

let post_counter_response switch name index count =
  let pkt = Petr4.Runtime.CounterResponse { switch; name; index; count } in
  let body =
    pkt
    |> Petr4.Runtime.switch_msg_to_yojson
    |> Yojson.Safe.to_string
    |> Body.of_string in
  let%bind response, body = Client.post ~body (petr4_uri "counter_response") in
  let%bind () = Cohttp_lwt.Body.drain_body body in
  Lwt.return ()
