open Ast

let stmt_string s =
  match s with
  | Expect(port, Some(expect)) ->
    "port: " ^ port ^" expect: " ^ expect
  | Packet(port, packet) ->
    "port: " ^ port ^" packet: " ^ packet
  | _ -> failwith "unimplemented"

let str =
{|#       bit<32> A bit<32> B    bit<64> C
# In the output C = (A + B) on 32 bits

packet 0 00000000 00000000 ABCDEF01 ABCDEF01
expect 0 00000000 00000000 00000000 00000000

packet 0 00000001 00000000 00000000 00000000
expect 0 00000001 00000000 00000000 00000001

packet 0 00000001 00000001 00000000 00000000
expect 0 00000001 00000001 00000000 00000002

packet 0 00000011 00000022 00000000 00000000
expect 0 00000011 00000022 00000000 00000033

packet 0 FFFFFFFF 00000001 00000000 00000000
expect 0 FFFFFFFF 00000001 00000000 00000000

|}

let main () =
  let ic = open_in "arith-bmv2.stf" in
  (* let lexbuf = Lexing.from_string str in *)
  let lexbuf = Lexing.from_channel ic in
  let stmts = Parser.statements Lexer.token lexbuf in
  List.length stmts |> string_of_int |> print_endline;
  stmts |> List.map stmt_string |> String.concat "\n" |> print_endline

let _ = main ()
