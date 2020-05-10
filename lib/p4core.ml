open Prog.Value
open Typed
open Target
open Bitstring
open Env
module I = Info
open Core_kernel
module Info = I

module Corize (T : Target) : Target = struct

  type obj = T.obj

  type state = T.state

  type extern = state pre_extern

  let value_of_field (init_fs : (string * value) list) 
      (f : RecordType.field) : string * value =
    f.name,
    List.Assoc.find_exn init_fs f.name ~equal:String.equal

  let nbytes_of_hdr (fs : (string * value) list) : Bigint.t =
    fs
    |> List.map ~f:snd
    |> List.map ~f:width_of_val
    |> List.fold_left ~init:Bigint.zero ~f:Bigint.(+)
    |> fun x -> Bigint.(x / ((one + one) * (one + one) * (one + one)))

  let bytes_of_packet (pkt : buf) (nbytes : Bigint.t) : buf * Bigint.t * signal =
    try
      let (c1,c2) = Cstruct.split pkt (Bigint.to_int_exn nbytes) in
      let s = Cstruct.to_string c1 in
      let chars = String.to_list s in
      let bytes = List.map chars ~f:Char.to_int in
      let bytes' = List.map bytes ~f:Bigint.of_int in
      let eight = Bigint.((one + one) * (one + one) * (one + one)) in
      let f a n = Bigint.(a * power_of_two eight + n) in
      let n = List.fold_left bytes' ~init:Bigint.zero ~f:f in
      (c2,n,SContinue)
    with Invalid_argument _ -> (pkt ,Bigint.zero,SReject "PacketTooShort")

  let rec extract_hdr_field (nvarbits : Bigint.t) (n, s : (Bigint.t * Bigint.t) * signal)
      (v : value) : ((Bigint.t * Bigint.t) * signal) * value =
    match s with
    | SContinue ->
      begin match v with
        | VBit{w;_} -> extract_bit n w
        | VInt{w;_} -> extract_int n w
        | VVarbit{max;_} -> extract_varbit nvarbits n max
        | _ -> failwith "invalid header field type" end
    | SReject _ -> ((n,s),VNull)
    | _ -> failwith "unreachable"

  and extract_bit (n : Bigint.t * Bigint.t)
      (w : Bigint.t) : ((Bigint.t * Bigint.t) * signal) * value =
    let (nw,nv) = n in
    let x = bitstring_slice nv Bigint.(nw-one) Bigint.(nw-w) in
    let y = bitstring_slice nv Bigint.(nw-w-one) Bigint.zero in
    Bigint.(((nw-w, y), SContinue), VBit{w;v=x})

  and extract_int (n : Bigint.t * Bigint.t)
      (w : Bigint.t) : ((Bigint.t * Bigint.t) * signal) * value =
    let (nw,nv) = n in
    let x = bitstring_slice nv Bigint.(nw-one) Bigint.(nw-w) in
    let y = bitstring_slice nv Bigint.(nw-w-one) Bigint.zero in
    Bigint.(((nw-w, y), SContinue), VInt{w;v=to_twos_complement x w})

  and extract_varbit (nbits : Bigint.t) (n : Bigint.t * Bigint.t)
      (w : Bigint.t) : ((Bigint.t * Bigint.t) * signal) * value =
    let (nw,nv) = n in
    if Bigint.(nbits > w)
    then ((n,SReject "HeaderTooShort"),VNull)
    else
      let x = bitstring_slice nv Bigint.(nw-one) Bigint.(nw-nbits) in
      let y = bitstring_slice nv Bigint.(nw-nbits-one) Bigint.zero in
      Bigint.(((nw-nbits, y), SContinue), VVarbit{max=w;w=nbits;v=x})

  let rec reset_fields (env : env) (fs : (string * value) list)
      (t : Type.t) : (string * value) list =
    match t with
    | Struct rt | Header rt -> List.map rt.fields ~f:(value_of_field fs)
    | TypeName n  -> reset_fields env fs (EvalEnv.find_typ n env)
    | NewType nt -> reset_fields env fs nt.typ
    | _ -> failwith "not resettable"

  let eval_extract' (ctrl : ctrl) (env : env) (st : state)
      (t : Type.t) (pkt : value) (v : value) (w : Bigint.t)
      (is_fixed : bool) : env * state * signal * value =
    let obj = State.get_packet st in
    let pkt = obj.main in
    let init_fs = match v with
      | VHeader { fields; is_valid } -> fields
      | _ -> failwith "extract expects header" in
    let fs = reset_fields env init_fs t in
    let eight = Bigint.((one + one) * (one + one) * (one + one)) in
    let nbytes = Bigint.(nbytes_of_hdr fs + w / eight) in
    let (pkt', extraction, s) = bytes_of_packet pkt nbytes in
    let st' = State.set_packet {obj with main = pkt'} st in
    match s with
    | SReject _ | SExit | SReturn _ -> env, st, s, VNull
    | SContinue ->
      let (ns, vs) = List.unzip fs in
      let ((_,s), vs') =
        List.fold_map vs 
          ~init:(Bigint.(nbytes * eight, extraction), SContinue)
          ~f:(extract_hdr_field w) in
      begin match s with 
        | SReject _ | SExit | SReturn _ -> env, st', s, VNull
        | SContinue ->
          let fs' = List.zip_exn ns vs' in
          let h = VHeader {
            fields = fs';
            is_valid = true;
          } in
          let env'= 
            EvalEnv.insert_val_bare
              (if is_fixed then "hdr" else "variableSizeHeader")
              h env in
          env', st', SContinue, VNull
      end

  let eval_advance : extern = fun ctrl env st _ args ->
    let (pkt_loc, v) = match args with
      | [(VRuntime {loc;_}, _); (VBit{v;_}, _)] -> loc, v
      | _ -> failwith "unexpected args for advance" in
    let obj = State.get_packet st in
    let pkt = obj.main in 
    try
      let x = (Bigint.to_int_exn v) / 8 in
      let pkt' = Cstruct.split pkt x |> snd in
      let st' = State.set_packet {obj with main = pkt'} st in
      env, st', SContinue, VNull
    with Invalid_argument _ ->
      env, st, SReject "PacketTooShort", VNull

  let eval_extract : extern = fun ctrl env st targs args ->
    match args with 
    | [(pkt, _);(v1, t)] -> eval_extract' ctrl env st t pkt v1 Bigint.zero true
    | [(pkt,_);(v1,t);(v2, _)] -> eval_extract' ctrl env st t pkt v1 (assert_bit v2 |> snd) false
    | [] -> eval_advance ctrl env st targs args
    | _ -> failwith "wrong number of args for extract"

  let rec val_of_bigint (env : env) (t : Type.t) (n : Bigint.t) : value =
    match t with
    | Bool -> if Bigint.(n = zero) then VBool false else VBool true
    | Int {width} -> 
      VInt {v = to_twos_complement n (Bigint.of_int width); w = Bigint.of_int width}
    | Bit {width} ->
      VBit {v = of_twos_complement n (Bigint.of_int width); w = Bigint.of_int width}
    | Array {typ;size} -> failwith "TODO: array of bigint"
    | Tuple _ -> failwith "TODO: tuple of bigint"
    | Record _ -> failwith "TODO: record_of_bigint"
    | Header _ -> failwith "TODO: header of bigint"
    | Struct _ -> failwith "TODO: struct of bigint"
    | Enum {typ = Some t;_} -> val_of_bigint env t n
    | TypeName name -> val_of_bigint env (EvalEnv.find_typ name env) n
    | NewType nt -> val_of_bigint env nt.typ n
    | _ -> failwith "not a fixed-width type"
    
  let eval_lookahead : extern = fun _ env st targs args ->
    let t = match targs with
      | [t] -> t
      | _ -> failwith "unexpected type args for lookahead" in
    let w = width_of_typ env t in
    let obj = State.get_packet st in
    let pkt = obj.main in
    let eight = Bigint.((one + one) * (one + one) * (one + one)) in
    try
      let (pkt_hd, _) = Cstruct.split ~start:0 pkt Bigint.(to_int_exn (w/eight)) in
      let (_, n, _) = bytes_of_packet pkt_hd Bigint.(w/eight) in
      env, st, SContinue, val_of_bigint env t n
    with Invalid_argument _ -> env, st, SReject "PacketTooShort", VNull

  let eval_length : extern = fun _ env st _ args ->
    match args with
    | [(VRuntime {loc;_}, _)] ->
      let obj = State.get_packet st in
      let len = obj.in_size in
      env, st, SContinue, VBit {w= Bigint.of_int 32; v = Bigint.of_int len }
    | _ -> failwith "unexpected args for length"

  let packet_of_bytes (n : Bigint.t) (w : Bigint.t) : buf =
    let eight = Bigint.((one + one) * (one + one) * (one + one)) in
    let seven = Bigint.(eight - one) in
    let rec h acc n w =
      if Bigint.(w = zero) then acc else
        let lsbyte = bitstring_slice n seven Bigint.zero in
        let n' = bitstring_slice n Bigint.(w-one) eight in
        h (lsbyte :: acc) n' Bigint.(w-eight) in
    let bytes = h [] n w in
    let ints = List.map bytes ~f:Bigint.to_int_exn in
    let chars = List.map ints ~f:Char.of_int_exn in
    let s = String.of_char_list chars in
    Cstruct.of_string s

  let rec field_types_of_typ (env : env) (t : Type.t) : Type.t list =
    match t with 
    | Header rt | Record rt | Struct rt -> List.map rt.fields ~f:(fun x -> x.typ)
    | TypeName n -> field_types_of_typ env (EvalEnv.find_typ n env)
    | NewType nt -> field_types_of_typ env nt.typ
    | _ -> failwith "type does not have fields"

  let rec packet_of_value (env : env) (t : Type.t) (v : value) : buf =
    match v with
    | VBit {w; v} -> packet_of_bit w v
    | VInt {w; v} -> packet_of_int w v
    | VVarbit {max; w; v} -> packet_of_bit w v
    | VStruct {fields} -> packet_of_struct env t fields
    | VHeader {fields; is_valid} -> packet_of_hdr env t fields is_valid
    | VUnion {valid_header; valid_fields} -> packet_of_union env t valid_header valid_fields
    | VStack {headers; _} -> packet_of_stack env t headers
    | VInteger _ -> failwith "it was integer"
    | _ -> failwith "emit undefined on type"

  and packet_of_bit (w : Bigint.t) (v : Bigint.t) : buf =
    packet_of_bytes v w

  and packet_of_int (w : Bigint.t) (v : Bigint.t) : buf =
    packet_of_bytes (of_twos_complement v w) w

  and packet_of_struct (env : env) (t : Type.t)
      (fields : (string * value) list) : buf =
    let fs = reset_fields env fields t in
    let fs' = List.map ~f:snd fs in
    let fts = field_types_of_typ env t in
    let pkts = List.map2_exn ~f:(fun v t -> packet_of_value env t v) fs' fts in
    List.fold ~init:Cstruct.empty ~f:Cstruct.append pkts

  and packet_of_hdr (env : env) (t : Type.t)
      (fields : (string * value) list) (is_valid : bool) : buf =
    if is_valid then packet_of_struct env t fields else Cstruct.empty

  and packet_of_union (env : env) (t : Type.t) (hdr : value)
      (fs : (string * bool) list) : buf =
    if List.exists fs ~f:snd
    then packet_of_value env t hdr
    else Cstruct.empty

  and packet_of_stack (env : env) (t : Type.t) (headers : value list) : buf =
    let t' = match t with
      | Array at -> at.typ
      | _ -> failwith "expected array type" in
    let pkts = List.map ~f:(packet_of_value env t') headers in
    List.fold ~init:Cstruct.empty ~f:Cstruct.append pkts

  let eval_emit : extern = fun _ env st _ args ->
    let (pkt_loc, v, t) = match args with
      | [(VRuntime {loc; _}, _); (hdr, t)] -> loc, hdr, t
      | _ -> failwith "unexpected args for emit" in
    let obj = State.get_packet st in
    let (pkt_hd, pkt_tl) = obj.emitted, obj.main in
    let pkt_add = packet_of_value env t v in
    let emitted = Cstruct.append pkt_hd pkt_add in
    let st' = State.set_packet {obj with emitted = emitted} st in
    env, st', SContinue, VNull

  let eval_verify : extern = fun _ env st _ args ->
    let b, err = match args with
      | [(VBool b, _); (VError err,_)] -> b, err
      | _ -> failwith "unexpected args for verify" in
    if b then env, st, SContinue, VNull
    else env, st, SReject err, VNull

  let core_externs : (string * extern) list =
    [ ("extract", eval_extract);
      ("lookahead", eval_lookahead);
      ("advance", eval_advance);
      ("length", eval_length);
      ("emit", eval_emit);
      ("verify", eval_verify)]

  let corize_extern (textern : T.extern) : extern = failwith "TOD"
    (* fun ctrl env core_st ts vs ->
    let (env, targ_st, s, v) = textern ctrl env (targetize_st core_st) in *)


  let externs : (string * extern) list =
    core_externs @ T.externs (* core has precedence of target *)

  let eval_extern name =
    match name with
    | "extract" -> eval_extract
    | "lookahead" -> eval_lookahead
    | "advance" -> eval_advance
    | "length" -> eval_length
    | "emit" -> eval_emit
    | "verify" -> eval_verify 
    | _ -> T.eval_extern name

  let initialize_metadata = T.initialize_metadata

  let check_pipeline = T.check_pipeline

  let eval_pipeline ctrl env st pkt app =
    let st = State.set_packet pkt st in
    T.eval_pipeline ctrl env st pkt app
end