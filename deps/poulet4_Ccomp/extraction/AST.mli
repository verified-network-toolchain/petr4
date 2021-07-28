open Archi
open BinInt
open BinNums
open Bool
open Coqlib
open Datatypes
open Errors
open Floats
open Integers
open List0
open Maps
open String0

type ident = positive

val ident_eq : positive -> positive -> bool

type typ =
| Tint
| Tfloat
| Tlong
| Tsingle
| Tany32
| Tany64

val typ_rect : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> typ -> 'a1

val typ_rec : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> typ -> 'a1

val typ_eq : typ -> typ -> bool

val list_typ_eq : typ list -> typ list -> bool

val coq_Tptr : typ

val typesize : typ -> coq_Z

val subtype : typ -> typ -> bool

val subtype_list : typ list -> typ list -> bool

type rettype =
| Tret of typ
| Tint8signed
| Tint8unsigned
| Tint16signed
| Tint16unsigned
| Tvoid

val rettype_rect :
  (typ -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> rettype -> 'a1

val rettype_rec :
  (typ -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> rettype -> 'a1

val rettype_eq : rettype -> rettype -> bool

val proj_rettype : rettype -> typ

type calling_convention = { cc_vararg : coq_Z option; cc_unproto : bool;
                            cc_structret : bool }

val cc_vararg : calling_convention -> coq_Z option

val cc_unproto : calling_convention -> bool

val cc_structret : calling_convention -> bool

val cc_default : calling_convention

val calling_convention_eq : calling_convention -> calling_convention -> bool

type signature = { sig_args : typ list; sig_res : rettype;
                   sig_cc : calling_convention }

val sig_args : signature -> typ list

val sig_res : signature -> rettype

val sig_cc : signature -> calling_convention

val proj_sig_res : signature -> typ

val signature_eq : signature -> signature -> bool

val signature_main : signature

type memory_chunk =
| Mint8signed
| Mint8unsigned
| Mint16signed
| Mint16unsigned
| Mint32
| Mint64
| Mfloat32
| Mfloat64
| Many32
| Many64

val memory_chunk_rect :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  memory_chunk -> 'a1

val memory_chunk_rec :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  memory_chunk -> 'a1

val chunk_eq : memory_chunk -> memory_chunk -> bool

val coq_Mptr : memory_chunk

val type_of_chunk : memory_chunk -> typ

val rettype_of_chunk : memory_chunk -> rettype

val chunk_of_type : typ -> memory_chunk

type init_data =
| Init_int8 of Int.int
| Init_int16 of Int.int
| Init_int32 of Int.int
| Init_int64 of Int64.int
| Init_float32 of float32
| Init_float64 of float
| Init_space of coq_Z
| Init_addrof of ident * Ptrofs.int

val init_data_rect :
  (Int.int -> 'a1) -> (Int.int -> 'a1) -> (Int.int -> 'a1) -> (Int64.int ->
  'a1) -> (float32 -> 'a1) -> (float -> 'a1) -> (coq_Z -> 'a1) -> (ident ->
  Ptrofs.int -> 'a1) -> init_data -> 'a1

val init_data_rec :
  (Int.int -> 'a1) -> (Int.int -> 'a1) -> (Int.int -> 'a1) -> (Int64.int ->
  'a1) -> (float32 -> 'a1) -> (float -> 'a1) -> (coq_Z -> 'a1) -> (ident ->
  Ptrofs.int -> 'a1) -> init_data -> 'a1

val init_data_size : init_data -> coq_Z

val init_data_list_size : init_data list -> coq_Z

type 'v globvar = { gvar_info : 'v; gvar_init : init_data list;
                    gvar_readonly : bool; gvar_volatile : bool }

val gvar_info : 'a1 globvar -> 'a1

val gvar_init : 'a1 globvar -> init_data list

val gvar_readonly : 'a1 globvar -> bool

val gvar_volatile : 'a1 globvar -> bool

type ('f, 'v) globdef =
| Gfun of 'f
| Gvar of 'v globvar

val globdef_rect :
  ('a1 -> 'a3) -> ('a2 globvar -> 'a3) -> ('a1, 'a2) globdef -> 'a3

val globdef_rec :
  ('a1 -> 'a3) -> ('a2 globvar -> 'a3) -> ('a1, 'a2) globdef -> 'a3

type ('f, 'v) program = { prog_defs : (ident * ('f, 'v) globdef) list;
                          prog_public : ident list; prog_main : ident }

val prog_defs : ('a1, 'a2) program -> (ident * ('a1, 'a2) globdef) list

val prog_public : ('a1, 'a2) program -> ident list

val prog_main : ('a1, 'a2) program -> ident

val prog_defs_names : ('a1, 'a2) program -> ident list

val prog_defmap : ('a1, 'a2) program -> ('a1, 'a2) globdef PTree.t

val transform_program_globdef :
  ('a1 -> 'a2) -> (ident * ('a1, 'a3) globdef) -> ident * ('a2, 'a3) globdef

val transform_program :
  ('a1 -> 'a2) -> ('a1, 'a3) program -> ('a2, 'a3) program

val transf_globvar :
  (ident -> 'a1 -> 'a2 res) -> ident -> 'a1 globvar -> 'a2 globvar res

val transf_globdefs :
  (ident -> 'a1 -> 'a2 res) -> (ident -> 'a3 -> 'a4 res) -> (ident * ('a1,
  'a3) globdef) list -> (ident * ('a2, 'a4) globdef) list res

val transform_partial_program2 :
  (ident -> 'a1 -> 'a2 res) -> (ident -> 'a3 -> 'a4 res) -> ('a1, 'a3)
  program -> ('a2, 'a4) program res

val transform_partial_program :
  ('a1 -> 'a2 res) -> ('a1, 'a3) program -> ('a2, 'a3) program res

type external_function =
| EF_external of char list * signature
| EF_builtin of char list * signature
| EF_runtime of char list * signature
| EF_vload of memory_chunk
| EF_vstore of memory_chunk
| EF_malloc
| EF_free
| EF_memcpy of coq_Z * coq_Z
| EF_annot of positive * char list * typ list
| EF_annot_val of positive * char list * typ
| EF_inline_asm of char list * signature * char list list
| EF_debug of positive * ident * typ list

val external_function_rect :
  (char list -> signature -> 'a1) -> (char list -> signature -> 'a1) ->
  (char list -> signature -> 'a1) -> (memory_chunk -> 'a1) -> (memory_chunk
  -> 'a1) -> 'a1 -> 'a1 -> (coq_Z -> coq_Z -> 'a1) -> (positive -> char list
  -> typ list -> 'a1) -> (positive -> char list -> typ -> 'a1) -> (char list
  -> signature -> char list list -> 'a1) -> (positive -> ident -> typ list ->
  'a1) -> external_function -> 'a1

val external_function_rec :
  (char list -> signature -> 'a1) -> (char list -> signature -> 'a1) ->
  (char list -> signature -> 'a1) -> (memory_chunk -> 'a1) -> (memory_chunk
  -> 'a1) -> 'a1 -> 'a1 -> (coq_Z -> coq_Z -> 'a1) -> (positive -> char list
  -> typ list -> 'a1) -> (positive -> char list -> typ -> 'a1) -> (char list
  -> signature -> char list list -> 'a1) -> (positive -> ident -> typ list ->
  'a1) -> external_function -> 'a1

val ef_sig : external_function -> signature

val ef_inline : external_function -> bool

val ef_reloads : external_function -> bool

val external_function_eq : external_function -> external_function -> bool

type 'f fundef =
| Internal of 'f
| External of external_function

val fundef_rect :
  ('a1 -> 'a2) -> (external_function -> 'a2) -> 'a1 fundef -> 'a2

val fundef_rec :
  ('a1 -> 'a2) -> (external_function -> 'a2) -> 'a1 fundef -> 'a2

val transf_fundef : ('a1 -> 'a2) -> 'a1 fundef -> 'a2 fundef

val transf_partial_fundef : ('a1 -> 'a2 res) -> 'a1 fundef -> 'a2 fundef res

type 'a rpair =
| One of 'a
| Twolong of 'a * 'a

val rpair_rect : ('a1 -> 'a2) -> ('a1 -> 'a1 -> 'a2) -> 'a1 rpair -> 'a2

val rpair_rec : ('a1 -> 'a2) -> ('a1 -> 'a1 -> 'a2) -> 'a1 rpair -> 'a2

val typ_rpair : ('a1 -> typ) -> 'a1 rpair -> typ

val map_rpair : ('a1 -> 'a2) -> 'a1 rpair -> 'a2 rpair

val regs_of_rpair : 'a1 rpair -> 'a1 list

val regs_of_rpairs : 'a1 rpair list -> 'a1 list

type 'a builtin_arg =
| BA of 'a
| BA_int of Int.int
| BA_long of Int64.int
| BA_float of float
| BA_single of float32
| BA_loadstack of memory_chunk * Ptrofs.int
| BA_addrstack of Ptrofs.int
| BA_loadglobal of memory_chunk * ident * Ptrofs.int
| BA_addrglobal of ident * Ptrofs.int
| BA_splitlong of 'a builtin_arg * 'a builtin_arg
| BA_addptr of 'a builtin_arg * 'a builtin_arg

val builtin_arg_rect :
  ('a1 -> 'a2) -> (Int.int -> 'a2) -> (Int64.int -> 'a2) -> (float -> 'a2) ->
  (float32 -> 'a2) -> (memory_chunk -> Ptrofs.int -> 'a2) -> (Ptrofs.int ->
  'a2) -> (memory_chunk -> ident -> Ptrofs.int -> 'a2) -> (ident ->
  Ptrofs.int -> 'a2) -> ('a1 builtin_arg -> 'a2 -> 'a1 builtin_arg -> 'a2 ->
  'a2) -> ('a1 builtin_arg -> 'a2 -> 'a1 builtin_arg -> 'a2 -> 'a2) -> 'a1
  builtin_arg -> 'a2

val builtin_arg_rec :
  ('a1 -> 'a2) -> (Int.int -> 'a2) -> (Int64.int -> 'a2) -> (float -> 'a2) ->
  (float32 -> 'a2) -> (memory_chunk -> Ptrofs.int -> 'a2) -> (Ptrofs.int ->
  'a2) -> (memory_chunk -> ident -> Ptrofs.int -> 'a2) -> (ident ->
  Ptrofs.int -> 'a2) -> ('a1 builtin_arg -> 'a2 -> 'a1 builtin_arg -> 'a2 ->
  'a2) -> ('a1 builtin_arg -> 'a2 -> 'a1 builtin_arg -> 'a2 -> 'a2) -> 'a1
  builtin_arg -> 'a2

type 'a builtin_res =
| BR of 'a
| BR_none
| BR_splitlong of 'a builtin_res * 'a builtin_res

val builtin_res_rect :
  ('a1 -> 'a2) -> 'a2 -> ('a1 builtin_res -> 'a2 -> 'a1 builtin_res -> 'a2 ->
  'a2) -> 'a1 builtin_res -> 'a2

val builtin_res_rec :
  ('a1 -> 'a2) -> 'a2 -> ('a1 builtin_res -> 'a2 -> 'a1 builtin_res -> 'a2 ->
  'a2) -> 'a1 builtin_res -> 'a2

val globals_of_builtin_arg : 'a1 builtin_arg -> ident list

val globals_of_builtin_args : 'a1 builtin_arg list -> ident list

val params_of_builtin_arg : 'a1 builtin_arg -> 'a1 list

val params_of_builtin_args : 'a1 builtin_arg list -> 'a1 list

val params_of_builtin_res : 'a1 builtin_res -> 'a1 list

val map_builtin_arg : ('a1 -> 'a2) -> 'a1 builtin_arg -> 'a2 builtin_arg

val map_builtin_res : ('a1 -> 'a2) -> 'a1 builtin_res -> 'a2 builtin_res

type builtin_arg_constraint =
| OK_default
| OK_const
| OK_addrstack
| OK_addressing
| OK_all

val builtin_arg_constraint_rect :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> builtin_arg_constraint -> 'a1

val builtin_arg_constraint_rec :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> builtin_arg_constraint -> 'a1
