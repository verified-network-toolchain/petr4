open Core_kernel
open Cohttp_lwt_unix

(* Extract the path, split on slashes, and remove empty strings *)
let extract_path (req:Request.t) : string list =
    List.filter ~f:(fun str -> not (String.is_empty str))
      (String.split ~on:'/'
         (Uri.path (Request.uri req)))

let callback _conn (req:Request.t) body =
  match req.meth, extract_path req with
  | `GET, ["version"] -> 
     Server.respond_string ~status:`OK ~body:"1.0" ()
  | `POST, ["insert"] -> 
     Server.respond_string ~status:`OK ~body:"inserted" ()
  | _ -> 
     Server.respond_error ~status:`Not_found ~body:"Unknown request" ()

let listen ?(port=9000) () = 
  Server.create ~mode:(`TCP (`Port port)) (Server.make ~callback ())
