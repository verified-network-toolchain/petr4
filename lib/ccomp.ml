open Core_kernel
module C = Csyntax
module Map = Map.Make(String)

module Env = struct
  type t = C.cexpr Map.t
end

(* Type of a compiler producing syntax in 'a. *)
type 'a comp = Env.t -> Env.t * 'a

module CompOps = struct
  type 'a t = 'a comp

  let bind (c: 'a t) ~f:(f:'a -> 'b t) : 'b t =
    fun env -> let (env', a) = c env in f a env'

  let return (a: 'a) =
    fun env -> (env, a)

  let map = `Define_using_bind

  let find_var (var: string) : (C.cexpr option) t =
    fun env -> (env, Map.find env var)
end

module CompM = Monad.Make(CompOps)

open CompM.Let_syntax

let translate_expr (e: Prog.Expression.t) : C.cexpr comp =
  match (snd e).expr with
  | Name (BareName x) ->
    begin match%bind CompOps.find_var (snd x) with
      | Some e -> e |> return
      | None -> C.CVar (snd x) |> return
    end
  | _ -> failwith "unimplemented"

let translate_stmt (s: Prog.Expression.t) : C.cstmt comp =
  failwith "unimplemented"

let rec translate_decl (d: Prog.Declaration.t) : C.cdecl comp =
  match snd d with
  | Struct {name; fields; _} ->
    let%bind cfields = translate_fields fields in
    C.CStruct (snd name, cfields) |> return
  | Header {name; fields; _} ->
    let%bind cfields = translate_fields fields in
    let valid = C.CField (CBool, "__header_valid") in
    C.CStruct (snd name, valid :: cfields) |> return
  | _ -> failwith "Unimplemented"

and translate_field (field: Prog.Declaration.field) : C.cfield comp =
  let%bind ctyp = translate_type (snd field).typ in
  C.CField (ctyp, snd (snd field).name) |> return

and translate_fields (fields: Prog.Declaration.field list) =
  fields
  |> List.map ~f:translate_field
  |> CompM.all

and translate_type (typ: Typed.Type.t) : C.ctyp comp =
  match typ with
  | Typed.Type.Bool -> C.CBool |> return
  | _ -> failwith "unimplemented"

let translate_prog ((Program t): Prog.program) : C.cprog comp =
  t
  |> List.map ~f:translate_decl
  |> CompM.all

let compile (prog: Prog.program) : C.cprog =
  translate_prog prog Map.empty |> snd
