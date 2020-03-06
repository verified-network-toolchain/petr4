open Core
open Petr4
open Petr4.Types

module TableVertex = struct
  type t = 
    { name : P4String.t;
      properties : Table.property list }
    let compare = Stdlib.compare
    let hash = Hashtbl.hash
    let equal = Stdlib.(=)
end

module TableGraph = Graph.Persistent.Digraph.Concrete(TableVertex)

let format_table_graph fmt g = 
  Format.fprintf fmt "Yo@\n"

let rec tables_declaration g decl = 
  let open Declaration in 
  match decl with 
  | _, Control ctrl -> 
     List.fold_left ctrl.locals ~init:g ~f:tables_declaration
  | _, Table tbl -> 
     Format.eprintf "TABLE: %s@\n" (snd tbl.name);
     let t = 
       TableVertex.{ name = tbl.name; 
                     properties = [] } in 
     TableGraph.add_vertex g t
  | _ -> 
     failwith "unimplemented"

let tables_program g prog = 
  let Program decls = prog in 
  List.fold_left decls ~f:tables_declaration ~init:g

let go verbose include_dirs p4file = 
  let () = Lexer.reset () in 
  let () = Lexer.set_filename p4file in 
  let p4string = 
    let buf = Buffer.create 101 in 
    let _ = P4pp.Eval.(preprocess_file include_dirs { file = p4file; defines = [] } buf p4file) in 
    Buffer.contents buf in
  let lexbuf = Lexing.from_string p4string in
  try
    let prog = Petr4.Parser.p4program Lexer.lexer lexbuf in 
    let tables = tables_program TableGraph.empty prog in 
    Format.printf "%a@\n" format_table_graph tables
  with
  | err -> 
     Format.eprintf "[%s] Failed@\n%!" p4file
  
let tables_command =
  let open Command.Spec in
  Command.basic_spec
    ~summary: "Compute table graph for P4_16 program"
    (empty
     +> flag "-v" no_arg ~doc:" Enable verbose output"
     +> flag "-I" (listed string) ~doc:"<dir> Add directory to include search path"
     +> anon ("p4file" %: string))
     (fun verbose include_dirs p4file () ->
       ignore (go verbose include_dirs p4file))

let () = Command.run ~version: "0.1.1" tables_command
