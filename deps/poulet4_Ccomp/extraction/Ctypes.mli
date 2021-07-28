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

val noattr : attr

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

val attr_of_type : coq_type -> attr

val change_attributes : (attr -> attr) -> coq_type -> coq_type

val remove_attributes : coq_type -> coq_type

type struct_or_union =
| Struct
| Union

type members = (ident * coq_type) list

type composite_definition =
| Composite of ident * struct_or_union * members * attr

val name_composite_def : composite_definition -> ident

type composite = { co_su : struct_or_union; co_members : members;
                   co_attr : attr; co_sizeof : coq_Z; co_alignof : coq_Z;
                   co_rank : nat }

type composite_env = composite PTree.t

val type_int32s : coq_type

val type_bool : coq_type

val typeconv : coq_type -> coq_type

val complete_type : composite_env -> coq_type -> bool

val align_attr : attr -> coq_Z -> coq_Z

val alignof : composite_env -> coq_type -> coq_Z

val sizeof : composite_env -> coq_type -> coq_Z

val alignof_composite : composite_env -> members -> coq_Z

val sizeof_struct : composite_env -> coq_Z -> members -> coq_Z

val sizeof_union : composite_env -> members -> coq_Z

val rank_type : composite_env -> coq_type -> nat

val rank_members : composite_env -> members -> nat

val type_of_params : (ident * coq_type) list -> typelist

val typ_of_type : coq_type -> typ

val sizeof_composite : composite_env -> struct_or_union -> members -> coq_Z

val complete_members : composite_env -> members -> bool

val composite_of_def :
  composite_env -> ident -> struct_or_union -> members -> attr -> composite
  res

val add_composite_definitions :
  composite_env -> composite_definition list -> composite_env res

val build_composite_env : composite_definition list -> composite_env res

type 'f fundef =
| Internal of 'f
| External of external_function * typelist * coq_type * calling_convention

type 'f program = { prog_defs : (ident * ('f fundef, coq_type) globdef) list;
                    prog_public : ident list; prog_main : ident;
                    prog_types : composite_definition list;
                    prog_comp_env : composite_env }

val make_program :
  composite_definition list -> (ident * ('a1 fundef, coq_type) globdef) list
  -> ident list -> ident -> 'a1 program res
