open Error
open Core_kernel

(** [block] is a custom minimalize representation of *)
type block = {
  stmts : Prog.Statement.t list;
  trans : Prog.Parser.transition;
}

(** [cfg] is a decomposition of [Prog.Parser.state list] with the additional
    information needed to describe a complete control-flow graph. *)
type cfg = {
  states : (string * Prog.Parser.state) list;
  edges : (string * string list) list;
}

(** [dom_map] maps states [s] to lists of states dominating [s], always with
    respect to a given CFG. *)
type dom_map = (string * string list) list

(** [loop] represents a loop, or more generally, a strongly-connected component
    in a given CFG. A [hdr] value of [None] indicates that the loop is not a natural
    loop. [states] are pointers to the set of states that comprise the loop, and
    [exits] are those states which have transitions to states outside of the loop.
    Invariant: [hdr] is [None] or [Some s] where [s] is in [states], and [exits]
      is a subset of [states]. *)
type loop = {
  hdr : string option;
  states : string list;
  exits : string list;
}

let equal = String.equal
let mem n l = List.exists l ~f:(equal n)

(** [to_cfg states] is a CFG describing the control structure of the [states]. *)
let to_cfg (states : Prog.Parser.state list) : cfg =
  let open Prog.Parser in
  let f state =
    snd (snd state).name, state in
  let states = List.map states ~f in
  let f (state, (_, { transition; _ })) =
    let succs = match snd transition with
      | Direct {next = (_, "accept")} -> []
      | Direct {next = (_, "reject")} -> []
      | Direct {next = (_, succ)}  -> [succ]
      | Select { cases; _ } ->
        List.map cases ~f:(fun case -> (snd case).next |> snd)
        |> List.filter
          ~f:(fun succ -> not (equal succ "reject" || equal succ "accept")) in
    state, succs in
  let edges = List.map states ~f in
  { states; edges; }

let of_cfg (cfg : cfg) : Prog.Parser.state list =
  List.map cfg.states ~f:snd

let get_preds (v : string) (cfg : cfg) : string list =
  List.map cfg.states ~f:fst
  |> List.filter ~f:(fun st -> List.Assoc.find_exn cfg.edges ~equal st |> mem v)

(** [get_dom_map cfg] returns a dominance map according to the given [cfg]. *)
let get_dom_map (cfg : cfg) : dom_map =
  let nodes = List.map cfg.states ~f:fst in
  let init = List.map nodes ~f:(fun v -> v, nodes) in
  let rec f acc =
    let update acc v =
      let preds = get_preds v cfg in
      if Int.equal (List.length preds) 0
      then List.Assoc.add acc v [v] ~equal
      else
        let pred = List.hd_exn preds in
        let doms = pred
          |> List.Assoc.find_exn acc ~equal
          |> List.filter ~f:(fun n -> List.for_all preds
            ~f:(fun pred -> List.Assoc.find_exn acc pred ~equal |> mem n)) in 
        List.Assoc.add acc v (if mem v doms then doms else v :: doms) ~equal in
    let acc' = List.fold ~init:acc ~f:update nodes in
    let unchanged = List.for_all nodes
      ~f:(fun v -> Int.equal (List.Assoc.find_exn acc' v ~equal |> List.length)
        (List.Assoc.find_exn acc v ~equal |> List.length)) in
    if unchanged then acc' else f acc' in
  f init

(** [get_sccs cfg] is a list of strongly-connected sub-graphs of [cfg] computed
    using Tarjan's strongly connected components algorithm. *)
let get_sccs (cfg : cfg) : loop list =
  [] (* TODO *)

(** [is_natural cfg doms scc] is [true] iff. there is a state in the [scc] of
    the [cfg] which dominates all other states in the [scc] and which is the only
    state in the [scc] with in-going edges from outside of the [scc]. *)
let is_natural (cfg : cfg) (doms : dom_map) (scc : loop) : bool =
  false (* TODO *)

(** [consumes_pkt cfg loop] is [true] iff. some state in the [loop] calls
    [packet_in.extract] or [packet_in.advance]. *)
let consumes_pkt (cfg : cfg) (loop : loop) : bool =
  false (* TODO *)

(** [loops_equal l1 l2] is [true] iff. [l1] and [l2] have exactly the same states. *)
let loops_equal (l1 : loop) (l2 : loop) : bool =
  List.equal equal l1.states l2.states

(** [unroll_loop cfg loops n i] is an updated version of both [cfg] and [loops],
    updated to reflect the fact that the loop at index [i] in [loops] has been
    unrolled. The computation attempts to establish the appropriate number of
    unrollings to perform based on header stack size. If unable to do so, it
    defaults to [n] unrollings. Additionally, it is guaranteed that if [n] was
    replaced by a value computed using header stack size, the loop is replaced
    with straight-line code, whereas if [n] is used, the semantics are the same. *)
let unroll_loop_h (n : int) (cfg : cfg) (idx_loops : (string * loop) list)
    (idx : string) : cfg * (string * loop) list =
  cfg, idx_loops (* TODO *)

let unroll_loop a (b,c) d = unroll_loop_h a b c d

let unroll_parser (n : int) (states : Prog.Parser.state list) : Prog.Parser.state list =
  let cfg = to_cfg states in
  let doms = get_dom_map cfg in
  let sccs = get_sccs cfg in
  let loops' = List.filter sccs ~f:(is_natural cfg doms) in
  let () =
    if List.equal loops_equal sccs loops'
    then ()
    else raise IrreducibleCFG in
  let loops = List.filter loops' ~f:(consumes_pkt cfg) in
  let () =
    if List.equal loops_equal loops' loops
    then ()
    else raise UnboundedLoop in
  let idxs = List.init (List.length loops) ~f:string_of_int in
  let idx_loops = List.zip_exn idxs loops in
  let cfg, _ = List.fold idxs ~init:(cfg, idx_loops) ~f:(unroll_loop n) in
  of_cfg cfg

let unroll_parsers (n : int) (p : Prog.program) : Prog.program =
  let open Prog.Declaration in
  let f = function
    | (i, Parser {
        annotations;
        name;
        type_params;
        params;
        constructor_params;
        locals;
        states;
    }) -> (i, Parser {
      annotations;
      name;
      type_params;
      params;
      constructor_params;
      locals;
      states = unroll_parser n states;
    })
    | d -> d in
  match p with Program ds ->
  Program (List.map ds ~f)