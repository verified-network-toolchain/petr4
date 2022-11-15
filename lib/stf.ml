open Ast
open P4light
open Core
module R = Poulet4.Result
module Exn = Poulet4.Target.Exn

type st = Obj.t Poulet4.Maps.PathMap.t

let strip_spaces s =
  s
  |> String.split_on_chars ~on:([' '])
  |> String.concat ~sep:""

let evaler
    (prog : program)
    (pkt_in : string)
    (port : int)
    (st : st)
  : (Exn.t, (st * Bigint.t) * bool list) R.result =
  let pkt_in = pkt_in
               |> String.lowercase
               |> Cstruct.of_hex
               |> Cstruct.to_string
               |> Util.string_to_bits in
  let port = Bigint.of_int port in
  Eval.v1_interp prog st port pkt_in

let rec run_test
    (prog : program)
    (stmts : statement list)
    (results : (string * string) list)
    (expected : (string * string) list)
    (st : st)
  : ((string * string) list) * ((string * string) list) = 
  match stmts with
  | [] -> (expected, results)
  | hd :: tl -> 
    match hd with
    | Packet (port, packet) -> 
      let results', st' =
        match evaler prog packet (int_of_string port) st with
        | Ok ((st', port), pkt) ->
          let fixed = pkt |> Util.bits_to_string |> Util.hex_of_string |> strip_spaces |> String.lowercase in
          (Bigint.to_string port, fixed) :: results, st'
        | Error e ->
          failwith (Exn.to_string e)
      in
      run_test prog tl results' expected st'
    | Expect (port, None) ->
      failwith "unimplemented stf statement: Expect w/ no pkt"
    | Expect (port, Some packet) ->
      run_test prog tl results ((port, strip_spaces packet |> String.lowercase) :: expected) st
    | Add (tbl_name, priority, match_list, (action_name, args), id) ->
      failwith "unimplemented stf statement: Add"
         (*
        run_test prog tl results expected st
        let tbl_name = convert_qualified tbl_name in 
        let action_name' = convert_qualified action_name in
        let entry = Poulet4.Target.Coq_mk_table_entry (match_list, action_name') in
        let st' = Poulet4.Semantics.add_entry _ st tbl_name entry in
        run_test prog tl results expected st'
          *)
    | Wait ->
      failwith "unimplemented stf statement: Wait"
      (*
      Core_unix.sleep 1;
      run_test prog tl results expected st
         *)
    | Set_default (tbl_name, (action_name, args)) ->
      failwith "unimplemented stf statement: Set_default"
  (*
        let tbl_name' = convert_qualified tbl_name in 
        let action_name' = convert_qualified action_name in
        let set_def' = update set_def tbl_name' (action_name', args) in
        run_test prog tl results expected env st
   *)
    | Remove_all ->
      failwith "unimplemented stf statement: Remove_all"
    | No_packet ->
      failwith "unimplemented stf statement: No_packet"
    | Check_counter _ ->
      failwith "unimplemented stf statement: Check_counter"

let run_stf stf_file prog =
  let ic = In_channel.create stf_file in
  let lexbuf = Lexing.from_channel ic in
  let stmts = Stf_parser.statements Stf_lexer.token lexbuf in
  let target =
    prog
    |> List.rev
    |> List.hd_exn 
    |> function | Poulet4.Syntax.DeclInstantiation (_, typ, _, _, _) -> typ
                | _ -> failwith "unexpected main value"
  in
  match target with
  | TypSpecializedType (TypTypeName {str = "V1Switch"; _}, _) -> 
    run_test prog stmts [] [] (fun _ -> None)
  | _ -> failwith "architecture unsupported"

