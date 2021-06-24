open Prog.Value
open Typed
open Target
open Bitstring
open Prog.Env
module I = Info
open Core_kernel
module Info = I
let (=) = Stdlib.(=)
let (<>) = Stdlib.(<>)

let rec field_types_of_typ (env : env) (t : Type.t) : Type.t list =
  match t with
  | Header rt | Record rt | Struct rt | HeaderUnion rt -> List.map rt.fields ~f:(fun x -> x.typ)
  | TypeName n -> field_types_of_typ env (EvalEnv.find_typ n env)
  | NewType nt -> field_types_of_typ env nt.typ
  | _ -> failwith "type does not have fields"
       
let value_of_field (init_fs : (string * value) list)
      (f : RecordType.field) : string * value =
  f.name,
  List.Assoc.find_exn init_fs f.name ~equal:String.equal
  
let rec reset_fields (env : env) (fs : (string * value) list)
          (t : Type.t) : (string * value) list =
  match t with
  | Struct rt | Header rt | HeaderUnion rt -> List.map rt.fields ~f:(value_of_field fs)
  | TypeName n  -> reset_fields env fs (EvalEnv.find_typ n env)
  | NewType nt -> reset_fields env fs nt.typ
  | _ -> raise_s [%message "not resettable"
                     ~t:(t:Type.t)]

let packet_of_bytes (n : Bigint.t) (w : Bigint.t) : buf =
  let eight = Bigint.((one + one) * (one + one) * (one + one)) in
  let seven = Bigint.(eight - one) in
  if Bigint.(w % eight <> zero) then failwith "packet_of_bytes: len must be byte-aligned";
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
  
let rec packet_of_value (env : env) (t : Type.t) (v : value) : buf =
  match v with
  | VBit {w; v} -> packet_of_bit w v
  | VInt {w; v} -> packet_of_int w v
  | VVarbit {max; w; v} -> packet_of_bit w v
  | VStruct {fields} -> packet_of_struct env t fields
  | VHeader {fields; is_valid} -> packet_of_hdr env t fields is_valid
  | VUnion {fields} -> packet_of_struct env t fields
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
  let rec underlying_typ_of_enum env t =
    match t with
    | Typed.Type.Enum et -> Option.value_exn et.typ
    | TypeName n -> EvalEnv.find_typ n env |> underlying_typ_of_enum env
    | NewType nt -> nt.typ |> underlying_typ_of_enum env
    | _ -> failwith "no such underlying type" in
  let f = fun (accw, accv) (w,v) ->
      Bigint.(accw + w), Bigint.(shift_bitstring_left accv w + v) in
  let rec wv_of_val (v, t) = match v with
    | VBit{w;v} -> w, v
    | VInt{w;v} -> w, of_twos_complement v w
    | VVarbit{max;w;v} -> w, v
    | VBool true -> Bigint.one, Bigint.one
    | VBool false -> Bigint.one, Bigint.zero
    | VSenumField{v;_} -> wv_of_val (v, underlying_typ_of_enum env t)
    | VStruct {fields;} ->
       let fs = reset_fields env fields t in
       let fs' = List.map ~f:snd fs in
       let fts = field_types_of_typ env t in
        List.zip_exn fs' fts |> List.map ~f:wv_of_val
        |> List.fold ~init:(Bigint.zero, Bigint.zero) ~f:f
    | _ -> failwith "invalid type for header field" in
  if not is_valid then Cstruct.empty else
    let fts = field_types_of_typ env t in
    let w, v = reset_fields env fields t
      |> List.map ~f:snd
               |> (fun a -> List.zip_exn a fts)
               |> List.map ~f:wv_of_val
               |> List.fold ~init:(Bigint.zero, Bigint.zero) ~f:f in
    packet_of_bit w v
    
and packet_of_stack (env : env) (t : Type.t) (hdrs : value list) : buf =
  let t' = match t with
    | Array at -> at.typ
    | _ -> failwith "expected array type" in
  let pkts = List.map ~f:(packet_of_value env t') hdrs in
  List.fold ~init:Cstruct.empty ~f:Cstruct.append pkts
  
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
    |> List.map ~f:(width_of_val)
    |> List.fold ~init:Bigint.zero ~f:Bigint.(+)
    |> fun x -> Bigint.(x / of_int 8)

  let bytes_of_packet (pkt : buf) (nbytes : Bigint.t) : buf * Bigint.t * signal =
    let (c1,c2), signal =
      try Cstruct.split pkt (Bigint.to_int_exn nbytes), SContinue
      with Invalid_argument  _ -> (pkt, Cstruct.empty), SReject "PacketTooShort"
    in
    let s = Cstruct.to_string c1 in
    let chars = String.to_list s in
    let bytes = List.map chars ~f:Char.to_int in
    let bytes' = List.map bytes ~f:Bigint.of_int in
    let eight = Bigint.((one + one) * (one + one) * (one + one)) in
    let f a n = Bigint.(a * power_of_two eight + n) in
    let n = List.fold_left bytes' ~init:Bigint.zero ~f:f in
    (c2,n,signal)

  let rec extract_hdr_field (nvarbits : Bigint.t)
      (n, s : (Bigint.t * Bigint.t) * signal)
      (v : value) : ((Bigint.t * Bigint.t) * signal) * value =
    match s with
    | SContinue ->
      begin match v with
        | VBit{w;_} -> extract_bit n w
        | VVarbit{max;_} -> extract_varbit nvarbits n max
        | VBool b -> extract_bool n
        | VInt{w;_} -> extract_int n w
        | VStruct {fields} ->
           let field_names = List.map ~f:fst fields in
           let (n, s), field_vals = extract_struct nvarbits (n, s) fields in
           let fields = List.zip_exn field_names field_vals in
           (n, s), VStruct{fields}
        | VSenumField {typ_name; enum_name; v} ->
          extract_senum typ_name enum_name v nvarbits (n, s)
        | _ -> raise_s [%message "invalid header field type"
                      ~v:(v:value)]
      end
    | SReject _ -> ((n,s),VNull)
    | _ -> failwith "unreachable"

  and extract_bit (n : Bigint.t * Bigint.t)
      (w : Bigint.t) : ((Bigint.t * Bigint.t) * signal) * value =
    let (nw,nv) = n in
    let x = bitstring_slice nv Bigint.(nw-one) Bigint.(nw-w) in
    let y = bitstring_slice nv Bigint.(nw-w-one) Bigint.zero in
    Bigint.(((nw-w, y), SContinue)), VBit{w;v=x}

  and extract_bool (buf : Bigint.t * Bigint.t) : ((Bigint.t * Bigint.t) * signal) * value =
    let open Bigint in
    let (bufsize, buf) = buf in
    let x = bitstring_slice buf (bufsize-one) (bufsize-one) in
    let y = bitstring_slice buf (bufsize-of_int 2) zero in
    ((bufsize-one, y), SContinue), VBool (x <> zero)

  and extract_int (n : Bigint.t * Bigint.t)
      (w : Bigint.t) : ((Bigint.t * Bigint.t) * signal) * value =
    let (nw,nv) = n in
    let x = bitstring_slice nv Bigint.(nw-one) Bigint.(nw-w) in
    let y = bitstring_slice nv Bigint.(nw-w-one) Bigint.zero in
    Bigint.(((nw-w, y), SContinue)), VInt{w;v=to_twos_complement x w}

  and extract_varbit (nbits : Bigint.t) (nw,nv : Bigint.t * Bigint.t)
      (w : Bigint.t) : ((Bigint.t * Bigint.t) * signal) * value =
    if Bigint.(nbits > w)
    then (((nw,nv),SReject "HeaderTooShort"),VNull)
    else if Bigint.(nbits > nw)
    then (((nw,nv), SReject "ParserInvalidArgument"), VNull)
    else
      let x = bitstring_slice nv Bigint.(nw-one) Bigint.(nw-nbits) in
      let y = bitstring_slice nv Bigint.(nw-nbits-one) Bigint.zero in
      Bigint.((nw-nbits, y), SContinue), VVarbit{max=w;w=nbits;v=x}

  and extract_struct (nvarbits : Bigint.t) (n, s : (Bigint.t * Bigint.t) * signal)
      (fields : (string * value) list) : ((Bigint.t * Bigint.t) * signal) * value list =
    let (n, s), vs = List.fold_map (List.map ~f:snd fields)
      ~init:(n, s)
      ~f:(fun (n, s) v -> extract_hdr_field nvarbits (n,s) v) in
    (n,s), vs

  and extract_senum (typ_name : string) (enum_name : string) (v : value)
      (nvarbits : Bigint.t) (n, s) : ((Bigint.t * Bigint.t) * signal) * value =
    let (x, v) = extract_hdr_field nvarbits (n, s) v in
    x, VSenumField{typ_name; enum_name; v}

  let eval_extract' (env : env) (st : state)
      (t : Type.t) (pkt : value) (_ : value) (w : Bigint.t)
      (is_fixed : bool) : env * state * signal * value =
    let obj = State.get_packet st in
    let pkt = obj.main in
    let init_v = init_val_of_typ env t in
    let init_fs = match init_v with
      | VHeader { fields; is_valid } -> fields
      | _ -> failwith "extract expects header" in
    let eight = Bigint.of_int 8 in
    let nbytes = Bigint.(nbytes_of_hdr init_fs + w / eight) in
    let (pkt', extraction, s) = bytes_of_packet pkt nbytes in
    let st' = State.set_packet {obj with main = pkt'} st in
    match s with
    | SReject _ | SExit | SReturn _ -> env, st, s, VNull
    | SContinue ->
      let (ns, vs) = List.unzip init_fs in
      try
        let (st'', _,s), vs' =
          List.fold_map vs
            ~init:(st', Bigint.(nbytes * eight, extraction), SContinue)
            ~f:(fun (st, n, s) v ->
                let ((n,s), v) = extract_hdr_field w (n,s) v in
                (st, n,s), v) in
        begin match s with
        | SReject _ | SExit | SReturn _ -> env, st, s, VNull
        | SContinue ->
          let fs' = List.zip_exn ns vs' in
          let h = VHeader {
                      fields = fs';
                      is_valid = true;
                    } in
          let loc = State.fresh_loc () in
          let st''' = State.insert_heap loc h st'' in
          let env'=
            EvalEnv.insert_val_bare
              (if is_fixed then "hdr" else "variableSizeHeader")
              loc env in
          env', st''', SContinue, VNull
        end
      with Invalid_argument _ ->
        env, st', SReject "PacketTooShort", VNull

  let eval_advance : extern = fun env st _ args ->
    let (pkt_loc, v) = match args with
      | [(VRuntime {loc;_}, _); (VBit{v;_}, _)] -> loc, v
      | [(VRuntime {loc;_}, _); (VInteger v, _)] -> loc, v
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

  let eval_extract : extern = fun env st targs args ->
    match args with
    | [(pkt, _);(v1, t)] -> (match v1 with
                            | VNull -> let targ = List.nth targs 0 |> Option.value_exn in
                              eval_advance env st targs [(pkt, t); (VBit{v=width_of_typ env targ;w=Bigint.zero}, t)]
                            | _ -> eval_extract' env st t pkt v1 Bigint.zero true)
    | [(pkt,_);(v1,t);(v2, _)] -> eval_extract' env st t pkt v1 (bigint_of_val v2) false
    | _ -> failwith "wrong number of args for extract"

  let rec val_of_bigint (env : env) (t : Type.t) (n : Bigint.t) : value =
    let w = width_of_typ env t in
    let f (w,n) t =
      let rmax = width_of_typ env t in
      let v =
        val_of_bigint env t (bitstring_slice n Bigint.(w - one) Bigint.(w-rmax)) in
      Bigint.(w - rmax, bitstring_slice n (w - rmax) zero), v in
    let fieldvals_of_recordtype (rt : RecordType.t) : (string * value) list =
      let names = List.map ~f:(fun x -> x.name) rt.fields in
      let typs = List.map ~f:(fun x -> x.typ) rt.fields in
      let vs = List.fold_map typs ~init:(w,n) ~f:f in
      List.zip_exn names (snd vs) in
    match t with
    | Bool -> if Bigint.(n = zero) then VBool false else VBool true
    | Int {width} ->
      VInt {v = to_twos_complement n (Bigint.of_int width); w = Bigint.of_int width}
    | Bit {width} ->
      VBit {v = of_twos_complement n (Bigint.of_int width); w = Bigint.of_int width}
    | Array {typ;size} ->
      let init = List.init size ~f:(fun x -> t) in
      let (_, hdrs) =
        List.fold_map init
        ~init:(w,n)
        ~f:f in
      VStack {headers = hdrs;size=Bigint.of_int size;next=Bigint.zero}
    | List {types} | Tuple {types} ->
      let _, vs = List.fold_map types ~init:(w,n) ~f:f in
      VTuple vs
    | Record rt -> VRecord (fieldvals_of_recordtype rt)
    | Header rt -> VHeader {fields=fieldvals_of_recordtype rt;is_valid=true}
    | Struct rt -> VStruct {fields=fieldvals_of_recordtype rt;}
    | Enum {typ = Some t;_} -> val_of_bigint env t n
    | TypeName name -> val_of_bigint env (EvalEnv.find_typ name env) n
    | NewType nt -> val_of_bigint env nt.typ n
    | _ -> raise_s [%message "not a fixed-width type" ~t:(t: Type.t)]

  let eval_lookahead : extern = fun env st targs args ->
    let t = match targs with
      | [t] -> t
      | _ -> failwith "unexpected type args for lookahead" in
    let w = width_of_typ env t in
    let obj = State.get_packet st in
    let pkt = obj.main in
    let eight = Bigint.((one + one) * (one + one) * (one + one)) in
    try
      let (pkt_hd, _) = Cstruct.split ~start:0 pkt Bigint.(to_int_exn (w/eight)) in
      let (_, n, s) = bytes_of_packet pkt_hd Bigint.(w/eight) in
      begin match s with 
      | SContinue -> 
        let v = val_of_bigint env t n in
        env, st, SContinue, v
      | _ -> env, st, s, VNull end
    with Invalid_argument _ -> env, st, SReject "PacketTooShort", VNull

  let eval_length : extern = fun env st _ args ->
    match args with
    | [(VRuntime {loc;_}, _)] ->
      let obj = State.get_packet st in
      let len = obj.in_size in
      env, st, SContinue, VBit {w= Bigint.of_int 32; v = Bigint.of_int len }
    | _ -> failwith "unexpected args for length"

  let eval_emit : extern = fun env st _ args ->
    let (pkt_loc, v, t) = match args with
      | [(VRuntime {loc; _}, _); (hdr, t)] -> loc, hdr, t
      | _ -> failwith "unexpected args for emit" in
    let obj = State.get_packet st in
    let (pkt_hd, pkt_tl) = obj.emitted, obj.main in
    let pkt_add = packet_of_value env t v in
    let emitted = Cstruct.append pkt_hd pkt_add in
    let st' = State.set_packet {obj with emitted = emitted} st in
    env, st', SContinue, VNull

  let eval_verify : extern = fun env st _ args ->
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

  let write_header_field : T.obj Target.writer = T.write_header_field

  let read_header_field : T.obj Target.reader = T.read_header_field

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
