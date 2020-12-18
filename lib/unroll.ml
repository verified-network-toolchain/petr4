open Error
open Core_kernel

(** [block] is a custom minimalize representation of *)
type block = {
  stmts : Types.Statement.t list;
  trans : Types.Parser.transition;
}

(** [cfg] is a decomposition of [Types.Parser.state list] with the additional
    information needed to describe a complete control-flow graph. *)
type cfg = {
  states : (string * Types.Parser.state) list;
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
let to_cfg (states : Types.Parser.state list) : cfg =
  let open Types.Parser in
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
let of_cfg (cfg : cfg) : Types.Parser.state list =
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
  (* Format.printf "Called strong_connect on %s\nCurrent num sccs: %d\n" v (List.length sccs); *)
  let vmeta = { index = idx; low_link = idx; on_stack = true; } in
  let meta = List.Assoc.add meta v vmeta ~equal in
  let idx = idx + 1 in
  let stack = v :: stack in
  let succs = List.Assoc.find_exn cfg.edges v ~equal in
  let f (idx, stack, meta, sccs) w =
    if not (List.Assoc.mem meta w ~equal)
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
    (* let () = Format.printf "Adding new scc\n" in *)
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
  (* Format.printf "Starting scc algorithm\n"; *)
  let idx, stack, meta, sccs = 0, [], [], [] in
  let nodes = List.map cfg.states ~f:fst in
  let f (idx, stack, meta, sccs) v =
    if List.Assoc.mem meta v ~equal
    then idx, stack, meta, sccs
    else strong_connect cfg idx stack meta sccs v in
  List.fold nodes ~init:(idx, stack, meta, sccs) ~f
  |> fun (_, _, _, sccs) -> sccs
  
let nontrivial (cfg : cfg) (loop : loop) : bool =
  not (Int.equal (List.length loop.states) 1)
  || List.Assoc.find_exn cfg.edges (List.hd_exn loop.states) ~equal
      |> mem (List.hd_exn loop.states)

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
    List.exists cfg.states ~f:(fun (b,_) -> mem b succs && (not (mem b loop.states)
      || Option.equal equal (Some b) loop.hdr))
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
let stmt_consumes_pkt (stmt : Types.Statement.t) : bool =
  match (snd stmt) with
  | Types.Statement.MethodCall {
    func = _, Types.Expression.ExpressionMember {name = (_, "extract"); _ }; _ } ->
    true
    (* Bigint.(zero < (Target.width_of_typ env t)) *)
  | MethodCall {
    func = _, Types.Expression.ExpressionMember {name = (_, "advance"); _}; _ } ->
    true
  | _ -> false  

(** [state_consumes_pkt st] is [true] iff. the [st] contains code whose semantics
    increment the packet pointer. *)
let state_consumes_pkt (st : Types.Parser.state) : bool =
  List.exists (snd st).statements ~f:(stmt_consumes_pkt)

(** [consumes_pkt cfg loop] is [true] iff. every path from the [loop.hdr] to a
    state in [loop.exits] calls [packet_in.extract] or [packet_in.advance] on a
    value whose bit-length is non-zero. *)
let loop_consumes_pkt (cfg : cfg) (doms : dom_map)
    (loop : loop) : bool =
  List.for_all loop.exits ~f:(fun e ->
    (* let () = Format.printf "Checking if exit '%s' consumes packet\n" e in *)
    List.exists (List.Assoc.find_exn doms e ~equal |> List.filter ~f:(fun d -> mem d loop.states)) ~f:(fun st ->
      (* let () = Format.printf "Checking if dominator '%s' of exit '%s' consumes packet\n" st e in *)
      state_consumes_pkt (List.Assoc.find_exn cfg.states st ~equal)))

(** [loops_equal l1 l2] is [true] iff. [l1] and [l2] have exactly the same states. *)
let loops_equal (l1 : loop) (l2 : loop) : bool =
  List.equal equal l1.states l2.states

let get_stack_bound (cfg : cfg) (loop : loop) : int option =
  None (* TODO *)

let rename_loop_copy (i : int) (states : (string * Types.Parser.state) list) : (string * Types.Parser.state) list =
  let open Types.Parser in
  let f (n, st : string * Types.Parser.state) =
    Format.sprintf "%s_unroll%d" n i,
    (fst st, { (snd st) with name = fst (snd st).name,
      Format.sprintf "%s_unroll%d" (snd (snd st).name) i; }) in
  List.map states ~f

let update_case (max : int) (term : bool) (hdr : string) (states : string list)
    (curr : int) (case : Types.Parser.case) : Types.Parser.case =
  let n = snd (snd case).next in
  fst case, { (snd case) with next = fst (snd case).next,
    if equal hdr n
    then if term && (curr + 1 >= max)
      then "reject"
      else Format.sprintf "%s_unroll%d" n ((curr + 1) % max)
    else if mem n states
    then Format.sprintf "%s_unroll%d" n curr
    else n
  }

let update_transitions (max : int) (term : bool) (hdr : string) (states : string list)
    (curr : int) (st : Types.Parser.state) : Types.Parser.state =
  fst st, { (snd st) with transition = fst (snd st).transition, 
    match snd (snd st).transition with
    | Direct {next = (i, n)} ->
      let n =
        if equal n hdr
        then if term && (curr + 1 >= max)
          then "reject"
          else Format.sprintf "%s_unroll%d" n ((curr + 1) % max)
        else if mem n states
        then Format.sprintf "%s_unroll%d" n curr
        else n in
      Direct {next = (i,n)}
    | Select {exprs; cases;} ->
      let cases = List.map cases ~f:(update_case max term hdr states curr) in
      Select {exprs; cases;}
  }

let update_loop_transitions (max : int) (term : bool) (hdr : string) (states : string list)
    (curr : int) (c : (string * Types.Parser.state) list) : (string * Types.Parser.state) list =
  List.map c ~f:(fun (n, st) -> n, update_transitions max term hdr states curr st)

let rename_edges (max : int) (hdr : string) (states : string list) (curr : int)
    (n, es : string * string list) : string * string list =
  let f e =
    if equal e hdr
    then Format.sprintf "%s_unroll%d" e ((curr + 1) % max)
    else if mem e states
    then Format.sprintf "%s_unroll%d" e curr
    else e in
  let n = if mem n states then Format.sprintf "%s_unroll%d" n curr else n in
  let es = List.map es ~f in
  n, es

let rename_loop_edges (max : int) (hdr : string) (states : string list) (curr : int)
    (c : (string * string list) list) : (string * string list) list =
  List.map c ~f:(rename_edges max hdr states curr)
  
let subloop (l1 : loop) (l2 : loop) : bool =
  List.for_all l1.states ~f:(fun st -> mem st l2.states)

let update_loop (hdr : string) (states : string list)
    (new_nodes : string list) (l : loop) : loop = { l with
  hdr =
    if equal hdr (Option.value_exn l.hdr)
    then Some (Format.sprintf "%s_unroll0" hdr)
    else l.hdr;
  states =
    List.filter l.states
      ~f:(fun st -> not (mem st states)) |> (@) new_nodes; }  

(** [unroll_loop cfg loops max term i] is an updated version of both [cfg] and [loops],
    updated to reflect the fact that the loop at index [i] in [loops] has been
    unrolled. The computation attempts to establish the appropriate number of
    unrollings to perform based on header stack size. If unable to do so, it
    defaults to [n] unrollings. Additionally, it is guaranteed that if [n] was
    replaced by a value computed using header stack size, the loop is replaced
    with straight-line code, whereas if [n] is used, we check the [term] flag.
    If [term] is true, [n] unrollings are performed, and all transitions from the
    [n]th copy of the loop to the first copy of the loop are replaced with
    transitions to the reject state. Otherwise, the loop is left intact with
    [n] copies of the body. *)
let unroll_loop_h (max : int) (term : bool) (count : int) (cfg : cfg)
    (idx_loops : (string * loop) list) (idx : string) : int * cfg * (string * loop) list =
  let loop = List.Assoc.find_exn idx_loops idx ~equal in
  let stack_bound = get_stack_bound cfg loop in
  if Option.is_some stack_bound
  then count + 1, cfg, idx_loops (* TODO *)
  else if max <= 1 then count, cfg, idx_loops
  else
    let loop_states = List.map loop.states ~f:(fun st ->
      st, List.Assoc.find_exn cfg.states st ~equal) in
    let loop_edges = List.map loop.states ~f:(fun st ->
      st, List.Assoc.find_exn cfg.edges st ~equal) in
    let states = List.fold loop.states ~init:cfg.states ~f:(fun acc st ->
      List.Assoc.remove acc st ~equal) in
    let edges = List.fold loop.states ~init:cfg.edges ~f:(fun acc st ->
      List.Assoc.remove acc st ~equal) in
    let states = List.map states ~f:(fun (n, st) ->
      n, update_transitions max term (Option.value_exn loop.hdr) [] (-1) st) in
    let edges = List.map edges ~f:(fun (st, succs) ->
      st, List.map succs ~f:(fun succ ->
        if mem succ loop.states then Format.sprintf "%s_unroll0" succ else succ)) in
    let loop_copies = List.init max ~f:(Fn.const loop_states) in
    let loop_copies = List.mapi loop_copies ~f:rename_loop_copy in
    let loop_copies = List.mapi loop_copies 
      ~f:(update_loop_transitions max term (Option.value_exn loop.hdr) loop.states) in
    let states = List.concat loop_copies |> List.fold ~init:states
      ~f:(fun acc (n, st) -> List.Assoc.add acc n st ~equal) in
    let edge_copies = List.init max ~f:(Fn.const loop_edges) in
    let edge_copies = List.mapi edge_copies
      ~f:(rename_loop_edges max (Option.value_exn loop.hdr) loop.states) in
    let edges = List.concat edge_copies |> List.fold ~init:edges
      ~f:(fun acc (n, es) -> List.Assoc.add acc n es ~equal) in
    let cfg = { states; edges; } in
    let supset_loops = List.filter idx_loops ~f:(fun (_, l) -> subloop loop l) in
    let new_nodes = List.init max ~f:(Fn.const loop.states) in
    let new_nodes = List.mapi new_nodes
      ~f:(fun i sts -> List.map sts ~f:(fun st -> Format.sprintf "%s_unroll%d" st i))
      |> List.concat in
    let supset_loops = List.map supset_loops
      ~f:(fun (idx, l) -> idx, update_loop (Option.value_exn loop.hdr) loop.states new_nodes l) in
    let idx_loops = List.fold supset_loops ~init:idx_loops
      ~f:(fun acc (idx, l) -> List.Assoc.add acc idx l ~equal) in
    count, cfg, idx_loops

let unroll_loop a b (c, d, e) f = unroll_loop_h a b c d e f

let unroll_parser (n : int) (term : bool)
    (states : Types.Parser.state list) : Types.Parser.state list =
  (* Format.printf "Number of states: %d\n" (List.length states); *)
  let cfg = to_cfg states in
  let doms = get_dom_map cfg in
  (* List.iter doms ~f:(fun (v, ds) -> Format.printf "Dominators for state %s:\n" v;
    List.iter ds ~f:(fun d -> Format.printf "\t%s\n" d)); *)
  let sccs = get_sccs cfg in
  let sccs = List.filter sccs ~f:(nontrivial cfg) in
  (* Format.printf "Found SCCs!\n"; *)
  (* List.iter sccs ~f:(fun scc -> Format.printf "SCC:\n"; List.iter scc.states ~f:(fun st -> Format.printf "\t%s\n" st)); *)
  let loops' = List.filter_map sccs ~f:(is_natural cfg doms) in
  (* Format.printf "Filtered SCCS!\n"; *)
  (* List.iter loops' ~f:(fun scc -> Format.printf "SCC:\n"; List.iter scc.states ~f:(fun st -> Format.printf "\t%s\n" st)); *)
  (* Format.printf "Number of sccs: %d\n" (List.length sccs); *)
  (* Format.printf "Number of natural loops: %d\n" (List.length loops'); *)
  let () =
    if List.equal loops_equal sccs loops'
    then ()
    else raise IrreducibleCFG in
  let loops' = List.fold loops' ~init:[] ~f:(extract_nested cfg doms) in
  (* Format.printf "Extracted nested loops!\n"; *)
  (* List.iter loops' ~f:(fun scc -> Format.printf "SCC:\n"; List.iter scc.states ~f:(fun st -> Format.printf "\t%s\n" st)); *)
  let loops = List.map loops' ~f:(update_exits cfg) in
  let loops = List.filter loops ~f:(loop_consumes_pkt cfg doms) in
  (* Format.printf "Filtered non-packet-consuming loops!\n"; *)
  (* List.iter loops ~f:(fun scc -> Format.printf "SCC:\n"; List.iter scc.states ~f:(fun st -> Format.printf "\t%s\n" st)); *)
  let () =
    if List.equal loops_equal loops' loops
    then ()
    else raise UnboundedLoop in
  Format.printf "Found %d natural loops consuming the packet\n" (List.length loops);
  let loops = List.sort loops ~compare:(fun l1 l2 -> if subloop l1 l2 then -1 else 1) in
  let idxs = List.init (List.length loops) ~f:string_of_int in
  let idx_loops = List.zip_exn idxs loops in
  let count, cfg, _ = List.fold idxs ~init:(0, cfg, idx_loops) ~f:(unroll_loop n term) in
  Format.printf "Successfully eliminated %d natural loops using stack heuristics\n" count;
  of_cfg cfg

let unroll_parsers (n : int) (term : bool) (p : Types.program) : Types.program =
  let open Types.Declaration in
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
      states = unroll_parser n term states;
    })
    | d -> d in
  match p with Program ds ->
  Program (List.map ds ~f)