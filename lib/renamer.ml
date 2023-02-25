open Core

type state = { counter : int;
               seen : string list }

type t = state ref


let create () = ref { counter = 0; seen = [] }

let seen_name st name =
  List.mem ~equal:String.equal !st.seen name

let observe_name st name =
  if seen_name st name
  then ()
  else st := { !st with seen = name :: !st.seen }

let incr st =
  st := {!st with counter = !st.counter + 1}

let rec gen_name st name =
  let { counter = i; _ } = !st in
  let new_name = Printf.sprintf "%s%d" name i in
  incr st;
  if seen_name st new_name
  then gen_name st name
  else new_name

let freshen_name st name =
  let new_name =
    if seen_name st name
    then gen_name st name
    else name
  in
  observe_name st new_name;
  new_name

let freshen_p4string st (s: P4string.t): P4string.t =
  {s with str = freshen_name st s.str}

