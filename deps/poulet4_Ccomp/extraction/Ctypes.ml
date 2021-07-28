open AST
open Archi
open BinInt
open BinNums
open Coqlib
open Datatypes
open Errors
open Maps
open Nat
open Zpower

type signedness =
| Signed
| Unsigned

type intsize =
| I8
| I16
| I32
| IBool

type floatsize =
| F32
| F64

type attr = { attr_volatile : bool; attr_alignas : coq_N option }

(** val noattr : attr **)

let noattr =
  { attr_volatile = false; attr_alignas = None }

type coq_type =
| Tvoid
| Tint of intsize * signedness * attr
| Tlong of signedness * attr
| Tfloat of floatsize * attr
| Tpointer of coq_type * attr
| Tarray of coq_type * coq_Z * attr
| Tfunction of typelist * coq_type * calling_convention
| Tstruct of ident * attr
| Tunion of ident * attr
and typelist =
| Tnil
| Tcons of coq_type * typelist

(** val attr_of_type : coq_type -> attr **)

let attr_of_type = function
| Tint (_, _, a) -> a
| Tlong (_, a) -> a
| Tfloat (_, a) -> a
| Tpointer (_, a) -> a
| Tarray (_, _, a) -> a
| Tstruct (_, a) -> a
| Tunion (_, a) -> a
| _ -> noattr

(** val change_attributes : (attr -> attr) -> coq_type -> coq_type **)

let change_attributes f ty = match ty with
| Tint (sz, si, a) -> Tint (sz, si, (f a))
| Tlong (si, a) -> Tlong (si, (f a))
| Tfloat (sz, a) -> Tfloat (sz, (f a))
| Tpointer (elt, a) -> Tpointer (elt, (f a))
| Tarray (elt, sz, a) -> Tarray (elt, sz, (f a))
| Tstruct (id, a) -> Tstruct (id, (f a))
| Tunion (id, a) -> Tunion (id, (f a))
| _ -> ty

(** val remove_attributes : coq_type -> coq_type **)

let remove_attributes ty =
  change_attributes (fun _ -> noattr) ty

type struct_or_union =
| Struct
| Union

type members = (ident * coq_type) list

type composite_definition =
| Composite of ident * struct_or_union * members * attr

(** val name_composite_def : composite_definition -> ident **)

let name_composite_def = function
| Composite (id, _, _, _) -> id

type composite = { co_su : struct_or_union; co_members : members;
                   co_attr : attr; co_sizeof : coq_Z; co_alignof : coq_Z;
                   co_rank : nat }

type composite_env = composite PTree.t

(** val type_int32s : coq_type **)

let type_int32s =
  Tint (I32, Signed, noattr)

(** val type_bool : coq_type **)

let type_bool =
  Tint (IBool, Signed, noattr)

(** val typeconv : coq_type -> coq_type **)

let typeconv ty = match ty with
| Tint (i, _, _) ->
  (match i with
   | I32 -> remove_attributes ty
   | _ -> Tint (I32, Signed, noattr))
| Tarray (t0, _, _) -> Tpointer (t0, noattr)
| Tfunction (_, _, _) -> Tpointer (ty, noattr)
| _ -> remove_attributes ty

(** val complete_type : composite_env -> coq_type -> bool **)

let rec complete_type env = function
| Tvoid -> false
| Tarray (t', _, _) -> complete_type env t'
| Tfunction (_, _, _) -> false
| Tstruct (id, _) ->
  (match PTree.get id env with
   | Some _ -> true
   | None -> false)
| Tunion (id, _) ->
  (match PTree.get id env with
   | Some _ -> true
   | None -> false)
| _ -> true

(** val align_attr : attr -> coq_Z -> coq_Z **)

let align_attr a al =
  match a.attr_alignas with
  | Some l -> two_p (Z.of_N l)
  | None -> al

(** val alignof : composite_env -> coq_type -> coq_Z **)

let rec alignof env t0 =
  align_attr (attr_of_type t0)
    (match t0 with
     | Tint (i, _, _) ->
       (match i with
        | I16 -> Zpos (Coq_xO Coq_xH)
        | I32 -> Zpos (Coq_xO (Coq_xO Coq_xH))
        | _ -> Zpos Coq_xH)
     | Tlong (_, _) -> align_int64
     | Tfloat (f, _) ->
       (match f with
        | F32 -> Zpos (Coq_xO (Coq_xO Coq_xH))
        | F64 -> align_float64)
     | Tpointer (_, _) ->
       if ptr64
       then Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH)))
       else Zpos (Coq_xO (Coq_xO Coq_xH))
     | Tarray (t', _, _) -> alignof env t'
     | Tstruct (id, _) ->
       (match PTree.get id env with
        | Some co -> co.co_alignof
        | None -> Zpos Coq_xH)
     | Tunion (id, _) ->
       (match PTree.get id env with
        | Some co -> co.co_alignof
        | None -> Zpos Coq_xH)
     | _ -> Zpos Coq_xH)

(** val sizeof : composite_env -> coq_type -> coq_Z **)

let rec sizeof env = function
| Tint (i, _, _) ->
  (match i with
   | I16 -> Zpos (Coq_xO Coq_xH)
   | I32 -> Zpos (Coq_xO (Coq_xO Coq_xH))
   | _ -> Zpos Coq_xH)
| Tlong (_, _) -> Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH)))
| Tfloat (f, _) ->
  (match f with
   | F32 -> Zpos (Coq_xO (Coq_xO Coq_xH))
   | F64 -> Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
| Tpointer (_, _) ->
  if ptr64
  then Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH)))
  else Zpos (Coq_xO (Coq_xO Coq_xH))
| Tarray (t', n, _) -> Z.mul (sizeof env t') (Z.max Z0 n)
| Tstruct (id, _) ->
  (match PTree.get id env with
   | Some co -> co.co_sizeof
   | None -> Z0)
| Tunion (id, _) ->
  (match PTree.get id env with
   | Some co -> co.co_sizeof
   | None -> Z0)
| _ -> Zpos Coq_xH

(** val alignof_composite : composite_env -> members -> coq_Z **)

let rec alignof_composite env = function
| [] -> Zpos Coq_xH
| p :: m' ->
  let (_, t0) = p in Z.max (alignof env t0) (alignof_composite env m')

(** val sizeof_struct : composite_env -> coq_Z -> members -> coq_Z **)

let rec sizeof_struct env cur = function
| [] -> cur
| p :: m' ->
  let (_, t0) = p in
  sizeof_struct env (Z.add (align cur (alignof env t0)) (sizeof env t0)) m'

(** val sizeof_union : composite_env -> members -> coq_Z **)

let rec sizeof_union env = function
| [] -> Z0
| p :: m' -> let (_, t0) = p in Z.max (sizeof env t0) (sizeof_union env m')

(** val rank_type : composite_env -> coq_type -> nat **)

let rec rank_type ce = function
| Tarray (t', _, _) -> S (rank_type ce t')
| Tstruct (id, _) ->
  (match PTree.get id ce with
   | Some co -> S co.co_rank
   | None -> O)
| Tunion (id, _) ->
  (match PTree.get id ce with
   | Some co -> S co.co_rank
   | None -> O)
| _ -> O

(** val rank_members : composite_env -> members -> nat **)

let rec rank_members ce = function
| [] -> O
| p :: m0 -> let (_, t0) = p in max (rank_type ce t0) (rank_members ce m0)

(** val type_of_params : (ident * coq_type) list -> typelist **)

let rec type_of_params = function
| [] -> Tnil
| p :: rem -> let (_, ty) = p in Tcons (ty, (type_of_params rem))

(** val typ_of_type : coq_type -> typ **)

let typ_of_type = function
| Tvoid -> AST.Tint
| Tint (_, _, _) -> AST.Tint
| Tlong (_, _) -> AST.Tlong
| Tfloat (f, _) -> (match f with
                    | F32 -> Tsingle
                    | F64 -> AST.Tfloat)
| _ -> coq_Tptr

(** val sizeof_composite :
    composite_env -> struct_or_union -> members -> coq_Z **)

let sizeof_composite env su m =
  match su with
  | Struct -> sizeof_struct env Z0 m
  | Union -> sizeof_union env m

(** val complete_members : composite_env -> members -> bool **)

let rec complete_members env = function
| [] -> true
| p :: m' ->
  let (_, t0) = p in (&&) (complete_type env t0) (complete_members env m')

(** val composite_of_def :
    composite_env -> ident -> struct_or_union -> members -> attr -> composite
    res **)

let composite_of_def env id su m a =
  match PTree.get id env with
  | Some _ ->
    Error ((MSG
      ('M'::('u'::('l'::('t'::('i'::('p'::('l'::('e'::(' '::('d'::('e'::('f'::('i'::('n'::('i'::('t'::('i'::('o'::('n'::('s'::(' '::('o'::('f'::(' '::('s'::('t'::('r'::('u'::('c'::('t'::(' '::('o'::('r'::(' '::('u'::('n'::('i'::('o'::('n'::(' '::[]))))))))))))))))))))))))))))))))))))))))) :: ((CTX
      id) :: []))
  | None ->
    if complete_members env m
    then let al = align_attr a (alignof_composite env m) in
         OK { co_su = su; co_members = m; co_attr = a; co_sizeof =
         (align (sizeof_composite env su m) al); co_alignof = al; co_rank =
         (rank_members env m) }
    else Error ((MSG
           ('I'::('n'::('c'::('o'::('m'::('p'::('l'::('e'::('t'::('e'::(' '::('s'::('t'::('r'::('u'::('c'::('t'::(' '::('o'::('r'::(' '::('u'::('n'::('i'::('o'::('n'::(' '::[])))))))))))))))))))))))))))) :: ((CTX
           id) :: []))

(** val add_composite_definitions :
    composite_env -> composite_definition list -> composite_env res **)

let rec add_composite_definitions env = function
| [] -> OK env
| c :: defs0 ->
  let Composite (id, su, m, a) = c in
  (match composite_of_def env id su m a with
   | OK x -> add_composite_definitions (PTree.set id x env) defs0
   | Error msg -> Error msg)

(** val build_composite_env :
    composite_definition list -> composite_env res **)

let build_composite_env defs =
  add_composite_definitions PTree.empty defs

type 'f fundef =
| Internal of 'f
| External of external_function * typelist * coq_type * calling_convention

type 'f program = { prog_defs : (ident * ('f fundef, coq_type) globdef) list;
                    prog_public : ident list; prog_main : ident;
                    prog_types : composite_definition list;
                    prog_comp_env : composite_env }

(** val make_program :
    composite_definition list -> (ident * ('a1 fundef, coq_type) globdef)
    list -> ident list -> ident -> 'a1 program res **)

let make_program types defs public main =
  let filtered_var = build_composite_env types in
  (match filtered_var with
   | OK ce ->
     OK { prog_defs = defs; prog_public = public; prog_main = main;
       prog_types = types; prog_comp_env = ce }
   | Error e -> Error e)
