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

type scc_meta = {
  index : int;
  low_link : int;
  on_stack : bool;
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

(** [of_cfg cfg] is the P4 parser described by the [cfg]. *)
let of_cfg (cfg : cfg) : Prog.Parser.state list =
  List.map cfg.states ~f:snd

(** [get_preds cfg v] is a list of states which are predecessors of [v] according
    to the [cfg]. *)
let get_preds (cfg : cfg) (v : string) : string list =
  List.map cfg.states ~f:fst
  |> List.filter ~f:(fun st -> List.Assoc.find_exn cfg.edges ~equal st |> mem v)

(** [get_dom_map cfg] returns a dominance map according to the given [cfg]. *)
let get_dom_map (cfg : cfg) : dom_map =
  let nodes = List.map cfg.states ~f:fst in
  let init = List.map nodes ~f:(fun v -> v, nodes) in
  let rec f acc =
    let update acc v =
      let preds = get_preds cfg v in
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

let rec strong_connect
    (cfg : cfg)
    (idx : int)
    (stack : string list)
    (meta : (string * scc_meta) list)
    (sccs : loop list)
    (v : string):
    int * string list * (string * scc_meta) list * loop list =
  let vmeta = { index = idx; low_link = idx; on_stack = true; } in
  let meta = List.Assoc.add meta v vmeta ~equal in
  let idx = idx + 1 in
  let stack = v :: stack in
  let succs = List.Assoc.find_exn cfg.edges v ~equal in
  let f (idx, stack, meta, sccs) w =
    if List.Assoc.mem meta w ~equal
    then
      let idx, stack, meta, sccs = strong_connect cfg idx stack meta sccs w in
      let vmeta = List.Assoc.find_exn meta v ~equal in
      let wlow = (List.Assoc.find_exn meta w ~equal).low_link in
      let vmeta = { vmeta with low_link = Int.min vmeta.low_link wlow } in
      let meta = List.Assoc.add meta v vmeta ~equal in
      idx, stack, meta, sccs
    else if (List.Assoc.find_exn meta w ~equal).on_stack
    then
      let vmeta = List.Assoc.find_exn meta v ~equal in
      let wlow = (List.Assoc.find_exn meta w ~equal).low_link in
      let vmeta = { vmeta with low_link = Int.min vmeta.low_link wlow } in
      let meta = List.Assoc.add meta v vmeta ~equal in
      idx, stack, meta, sccs
    else idx, stack, meta, sccs in
  let idx, stack, meta, sccs = List.fold succs ~init:(idx, stack, meta, sccs) ~f in
  let vmeta = List.Assoc.find_exn meta v ~equal in
  if Int.equal vmeta.low_link vmeta.index
  then
    let rec f stack meta new_scc =
      let w = List.hd_exn stack in
      let stack = List.tl_exn stack in
      let wmeta = List.Assoc.find_exn meta w ~equal in
      let wmeta = { wmeta with on_stack = false } in
      let meta = List.Assoc.add meta w wmeta ~equal in
      let new_scc = w :: new_scc in
      if equal w v then stack, meta, new_scc else f stack meta new_scc in
    let new_scc = [] in
    let stack, meta, new_scc = f stack meta new_scc in
    let sccs = { states = new_scc; hdr = None; exits = []; } :: sccs in
    idx, stack, meta, sccs
  else idx, stack, meta, sccs

(** [get_sccs cfg] is a list of strongly-connected sub-graphs of [cfg] computed
    using Tarjan's strongly connected components algorithm. *)
let get_sccs (cfg : cfg) : loop list =
  let idx, stack, meta, sccs = 0, [], [], [] in
  let nodes = List.map cfg.states ~f:fst in
  let f (idx, stack, meta, sccs) v =
    if List.Assoc.mem meta v ~equal
    then strong_connect cfg idx stack meta sccs v
    else idx, stack, meta, sccs in
  List.fold nodes ~init:(idx, stack, meta, sccs) ~f
  |> fun (_, _, _, sccs) -> sccs

(** [is_natural cfg doms scc] is [true] iff. there is a state [st] in the [scc]
    of the [cfg] satisfying the following two conditions:
    1) [st] dominates all other states in the [scc]
    2) [st] is the only state in the [scc] with in-going edges from outside of
       the [scc]  *)
let is_natural (cfg : cfg) (doms : dom_map) (scc : loop) : loop option =
  let is_dom st =
    List.for_all scc.states
      ~f:(fun b -> List.Assoc.find_exn doms b ~equal |> mem st) in
  let is_hdr st =
    let cond = List.for_all scc.states
      ~f:(fun b -> List.for_all (get_preds cfg b)
        ~f:(fun p -> mem p scc.states || equal b st)) in
    if cond then Some { scc with hdr = Some st } else None in
  let header = List.find scc.states ~f:is_dom in
  Option.bind header ~f:is_hdr

(** [close_under_pred cfg (b,a)] is the natural loop formed around the backedge
    [b,a] according to the [cfg]. *)
let close_under_pred (cfg : cfg) (exit,head : string * string) : loop =
  let loop = {
    states = if equal exit head then [head] else [head; exit];
    hdr = Some head;
    exits = [];
  } in
  let rec f loop =
    let preds = loop.states
      |> List.filter ~f:(fun b -> equal b head |> not)
      |> List.map ~f:(fun b -> get_preds cfg b)
      |> List.fold ~init:[] ~f:(@) in
    let states = List.fold preds ~init:loop.states
      ~f:(fun acc p -> if mem p acc then acc else p :: acc) in
    if Int.equal (List.length states) (List.length loop.states)
    then loop
    else f {loop with states = states;} in
  f loop

(** [merge_loops l1 l2] is a new loop which subsumes both [l1] and [l2].
    Precondition: [l1] and [l2] are natural loops sharing the same header *)
let merge_loops (l1 : loop) (l2 : loop) : loop = 
  let union l1 l2 =
    List.fold l1 ~init:l2 ~f:(fun acc b -> if mem b acc then acc else b :: acc) in
  { states = union l1.states l2.states;
    hdr = l1.hdr;
    exits = union l1.exits l2.exits; }

(** [merge_sc_loops] merges loops for which neither is a subset of the other but
    which share the same header. *)
let merge_sc_loops (acc : (string * loop) list)
    (idx, loop : string * loop) : (string * loop) list =
  let entry = List.find acc ~f:(fun (_, l) -> Option.equal equal loop.hdr l.hdr) in
  let entry = Option.map entry ~f:(fun (idx, l) -> idx, merge_loops loop l) in
  let idx, loop = Option.value_map entry ~default:(idx,loop) ~f:Fn.id in
  List.Assoc.add acc idx loop ~equal

(** [extract_nested cfg doms acc loop] scans the [loop] for natural nested
    sub-loops according to the [cfg] and returns [acc] with all such loops added.*)
let extract_nested (cfg : cfg) (doms : dom_map) (acc : loop list) (loop : loop) : loop list =
  let backedges =
    List.map loop.states ~f:(fun st -> st, List.Assoc.find_exn cfg.edges st ~equal)
    |> List.map ~f:(fun (e, ss) -> e, List.filter ss ~f:(fun v -> mem v loop.states))
    |> List.fold ~init:[] ~f:(fun acc (e,ss) -> acc @ (List.map ss ~f:(fun s -> e,s)))
    |> List.filter ~f:(fun (b,a) -> List.Assoc.find_exn doms b ~equal |> mem a) in
  if Int.equal (List.length backedges) 1
  then loop :: acc
  else
    let loops = List.map backedges ~f:(close_under_pred cfg) in
    let idx_loops = List.mapi loops ~f:(fun i l -> string_of_int i, l) in
    let idx_loops = List.fold idx_loops ~init:[] ~f:merge_sc_loops in
    let loops = List.map idx_loops ~f:snd in
    acc @ loops

let accepts_or_rejects (cfg : cfg) (st : string) : bool =
  let trans = (List.Assoc.find_exn cfg.states st ~equal |> snd).transition in
  match snd trans with
  | Direct {next = (_, st)} -> equal st "reject" || equal st "accept"
  | Select {cases; _} ->
    List.map cases ~f:(fun (_,case) -> snd case.next)
    |> List.exists ~f:(fun st -> equal st "reject" || equal st "accept")

(** [update_exists cfg loop] is [loop] updated with an accurate list of [exits]
    according to the [cfg]. *)
let update_exits (cfg : cfg) (loop : loop) : loop =
  let is_exit st =
    let succs = List.Assoc.find_exn cfg.edges st ~equal in
    List.exists cfg.states ~f:(fun (b,_) -> mem b succs && not (mem b loop.states))
    || accepts_or_rejects cfg st in
  { loop with exits = List.filter loop.states ~f:is_exit; }

(*  NOTE: the common case is for extract or advance to occur as a method call.
    The current implementation checks for this, but it is also possible for other
    kinds of statements, such as applications, other function calls, and even
    assignment statements which assign from an expression containing a function
    call, to have side effects which also increment packet pointer. With some
    inlining, the difficulties will be decrease, but it will still be necessary
    to do some sort of global analysis in order to maximize the completeness of
    this check. This will probably be some kind of dataflow analysis whose
    values are 'Extracts' and 'MayNotExtract' or something of the sort. *)

(* NOTE: in order for the check to be truely sound, we would need to use a
    dataflow analysis to check that the argument to advance is non-zero. For now,
    we simply assume the programmer was smart enough not to allow this. *)

(** [stmt_consumes_pkt stmt] is [true] iff. the semantics of [stmt] increment
    the packet pointer. *)
let stmt_consumes_pkt (env : Prog.Env.EvalEnv.t) (stmt : Prog.Statement.t) : bool =
  match (snd stmt).stmt with
  | Prog.Statement.MethodCall {
    func = _, {expr = Prog.Expression.Name (BareName (_, "extract")); _};
    type_args = [t]; _ } ->
    Bigint.(zero < (Target.width_of_typ env t))
  (* | MethodCall {
    func = _, {expr = Prog.Expression.Name (BareName (_, "advance")); _}; _ } ->
    true *)
  | _ -> false  

(** [state_consumes_pkt st] is [true] iff. the [st] contains code whose semantics
    increment the packet pointer. *)
let state_consumes_pkt (env : Prog.Env.EvalEnv.t) (st : Prog.Parser.state) : bool =
  List.exists (snd st).statements ~f:(stmt_consumes_pkt env)

(** [consumes_pkt cfg loop] is [true] iff. every path from the [loop.hdr] to a
    state in [loop.exits] calls [packet_in.extract] or [packet_in.advance] on a
    value whose bit-length is non-zero. *)
let loop_consumes_pkt (env : Prog.Env.EvalEnv.t) (cfg : cfg) (doms : dom_map)
    (loop : loop) : bool =
  List.for_all loop.exits ~f:(fun e ->
    List.exists (List.Assoc.find_exn doms e ~equal) ~f:(fun st ->
      state_consumes_pkt env (List.Assoc.find_exn cfg.states st ~equal)))

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

let unroll_parser (n : int) (env : Prog.Env.EvalEnv.t)
    (states : Prog.Parser.state list) : Prog.Parser.state list =
  let cfg = to_cfg states in
  let doms = get_dom_map cfg in
  let sccs = get_sccs cfg in
  let loops' = List.filter_map sccs ~f:(is_natural cfg doms) in
  let () =
    if List.equal loops_equal sccs loops'
    then ()
    else raise IrreducibleCFG in
  let loops' = List.fold loops' ~init:[] ~f:(extract_nested cfg doms) in
  let loops = List.map loops' ~f:(update_exits cfg) in
  let loops = List.filter loops ~f:(loop_consumes_pkt env cfg doms) in
  let () =
    if List.equal loops_equal loops' loops
    then ()
    else raise UnboundedLoop in
  let idxs = List.init (List.length loops) ~f:string_of_int in
  let idx_loops = List.zip_exn idxs loops in
  let cfg, _ = List.fold idxs ~init:(cfg, idx_loops) ~f:(unroll_loop n) in
  of_cfg cfg

let unroll_parsers (n : int) (env : Prog.Env.EvalEnv.t) (p : Prog.program) : Prog.program =
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
      states = unroll_parser n env states;
    })
    | d -> d in
  match p with Program ds ->
  Program (List.map ds ~f)