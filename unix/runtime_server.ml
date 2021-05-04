open Core_kernel
open Cohttp_lwt
open Cohttp_lwt_unix
open Lwt.Infix

(* Extract the path, split on slashes, and remove empty strings *)
let extract_path (req:Request.t) : string list =
    List.filter ~f:(fun str -> not (String.is_empty str))
      (String.split ~on:'/'
         (Uri.path (Request.uri req)))

let handle_message handlers (body:Body.t) : (Response.t * Body.t) Lwt.t = 
  try 
    begin
      let%bind str = Body.to_string body in
      Printf.eprintf "Message: %s\n%!" str;
      let json = Yojson.Safe.from_string str in
      match Petr4.Runtime.message_of_yojson json with 
      | Ok msg -> 
         let () = handlers msg in
         Server.respond_string ~status:`OK ~body:"" ()         
      | Error err -> 
         Server.respond_error ~status:`Bad_request ~body:err ()
    end
  with _ -> 
    Server.respond_error ~status:`Bad_request ~body:"" ()

let callback handlers _conn (req:Request.t) (body:Body.t) : (Response.t * Body.t) Lwt.t =
  match req.meth, extract_path req with
  | `GET, ["version"] ->
     Printf.eprintf "Version\n%!";
     Server.respond_string ~status:`OK ~body:"1.0" ()
  | `POST, [_;"message"] ->
     Printf.eprintf "Message\n%!";
     handle_message handlers body
  | _ -> 
     List.iter (extract_path req) ~f:(fun s -> Printf.eprintf "Chunk: %s\n%!" s);
     Printf.eprintf "Unknown Request: %s\n%!" (req |> Request.uri |> Uri.to_string);
     Server.respond_error ~status:`Not_found ~body:"Unknown request" ()

let listen ?(port=9000) ~handlers () = 
  Server.create ~mode:(`TCP (`Port port)) (Server.make ~callback:(callback handlers) ())
