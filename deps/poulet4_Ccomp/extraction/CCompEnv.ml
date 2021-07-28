open AST0
open AST
open BinNums
open Clight
open Ctypes
open Datatypes
open Envn
open Equality
open EquivDec
open EquivUtil
open IdentGen
open List0

module P = P4cub

module E = P.Expr

type coq_ClightEnv = { identMap : (string, ident) Env.t;
                       temps : (ident * coq_type) list;
                       vars : (ident * coq_type) list;
                       composites : (E.t * composite_definition) list;
                       identGenerator : generator;
                       fenv : (string, coq_function) Env.t;
                       tempOfArg : (string, ident * ident) Env.t }

(** val newClightEnv : coq_ClightEnv **)

let newClightEnv =
  { identMap = Env.empty; temps = []; vars = []; composites = [];
    identGenerator = gen_init; fenv = Env.empty; tempOfArg = Env.empty }

(** val add_temp_arg :
    coq_ClightEnv -> string -> coq_type -> ident -> coq_ClightEnv **)

let add_temp_arg env temp t0 oldid =
  let (gen', new_ident0) = gen_next env.identGenerator in
  { identMap = env.identMap; temps = env.temps; vars = ((new_ident0,
  t0) :: env.vars); composites = env.composites; identGenerator = gen';
  fenv = env.fenv; tempOfArg =
  (Env.bind temp (oldid, new_ident0) env.tempOfArg) }

(** val add_temp_nameless :
    coq_ClightEnv -> coq_type -> coq_ClightEnv * ident **)

let add_temp_nameless env t0 =
  let (gen', new_ident0) = gen_next env.identGenerator in
  ({ identMap = env.identMap; temps = ((new_ident0, t0) :: env.temps); vars =
  env.vars; composites = env.composites; identGenerator = gen'; fenv =
  env.fenv; tempOfArg = env.tempOfArg }, new_ident0)

(** val add_var : coq_ClightEnv -> string -> coq_type -> coq_ClightEnv **)

let add_var env var t0 =
  let (gen', new_ident0) = gen_next env.identGenerator in
  { identMap = (Env.bind var new_ident0 env.identMap); temps = env.temps;
  vars = ((new_ident0, t0) :: env.vars); composites = env.composites;
  identGenerator = gen'; fenv = env.fenv; tempOfArg = env.tempOfArg }

(** val add_composite_typ :
    coq_ClightEnv -> E.t -> composite_definition -> coq_ClightEnv **)

let add_composite_typ env p4t composite_def =
  { identMap = env.identMap; temps = env.temps; vars = env.vars; composites =
    ((p4t, composite_def) :: env.composites); identGenerator =
    env.identGenerator; fenv = env.fenv; tempOfArg = env.tempOfArg }

(** val add_function :
    coq_ClightEnv -> string -> coq_function -> coq_ClightEnv **)

let add_function env name f0 =
  let (gen', new_ident0) = gen_next env.identGenerator in
  { identMap = (Env.bind name new_ident0 env.identMap); temps = env.temps;
  vars = env.vars; composites = env.composites; identGenerator = gen'; fenv =
  (Env.bind name f0 env.fenv); tempOfArg = env.tempOfArg }

(** val update_function :
    coq_ClightEnv -> string -> coq_function -> coq_ClightEnv **)

let update_function env name f0 =
  { identMap = env.identMap; temps = env.temps; vars = env.vars; composites =
    env.composites; identGenerator = env.identGenerator; fenv =
    (Env.bind name f0 env.fenv); tempOfArg = env.tempOfArg }

(** val new_ident : coq_ClightEnv -> coq_ClightEnv * ident **)

let new_ident env =
  let (gen', new_ident0) = gen_next env.identGenerator in
  ({ identMap = env.identMap; temps = env.temps; vars = env.vars;
  composites = env.composites; identGenerator = gen'; fenv = env.fenv;
  tempOfArg = env.tempOfArg }, new_ident0)

(** val find_ident : coq_ClightEnv -> string -> ident option **)

let find_ident env name =
  Env.find coq_StringEqDec name env.identMap

(** val find_ident_temp_arg :
    coq_ClightEnv -> string -> (ident * ident) option **)

let find_ident_temp_arg env name =
  Env.find coq_StringEqDec name env.tempOfArg

(** val lookup_composite_rec :
    (E.t * composite_definition) list -> E.t -> composite_definition option **)

let rec lookup_composite_rec composites0 p4t =
  match composites0 with
  | [] -> None
  | p :: tl ->
    let (head, comp) = p in
    if equiv_dec TypeEquivalence.coq_TypeEqDec head p4t
    then Some comp
    else lookup_composite_rec tl p4t

(** val lookup_composite :
    coq_ClightEnv -> E.t -> composite_definition option **)

let lookup_composite env p4t =
  lookup_composite_rec env.composites p4t

(** val lookup_function :
    coq_ClightEnv -> string -> (coq_function * ident) option **)

let lookup_function env name =
  match Env.find coq_StringEqDec name env.fenv with
  | Some f0 ->
    (match Env.find coq_StringEqDec name env.identMap with
     | Some id -> Some (f0, id)
     | None -> None)
  | None -> None

(** val get_vars : coq_ClightEnv -> (ident * coq_type) list **)

let get_vars env =
  env.vars

(** val get_temps : coq_ClightEnv -> (ident * coq_type) list **)

let get_temps env =
  env.temps

(** val get_functions :
    coq_ClightEnv -> (ident * coq_function) list option **)

let get_functions env =
  let keys0 = Env.keys coq_StringEqDec env.fenv in
  fold_right (fun key0 accumulator ->
    match accumulator with
    | Some l ->
      (match lookup_function env key0 with
       | Some p -> let (f0, id) = p in Some ((id, f0) :: l)
       | None -> None)
    | None -> None) (Some []) keys0

(** val get_composites : coq_ClightEnv -> composite_definition list **)

let get_composites env =
  map snd env.composites
