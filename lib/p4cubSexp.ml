open Core
open Sexplib.Std
open Poulet4.AST

(** [make_sexp name args] is the s-expression [(name args)]; the s-expression of
    constructor with name [name] and arguments [args] *)
let make_sexp name args = Sexp.List (Sexp.Atom name :: args)

let sexp_of_strings = sexp_of_list sexp_of_string
let sexp_of_bit_type width = make_sexp "Typ.Bit" [ Bigint.sexp_of_t width ]
let sexp_of_int_type width = make_sexp "Typ.Int" [ Bigint.sexp_of_t width ]
let sexp_of_type_var idx = make_sexp "Typ.Var" [ sexp_of_int idx ]

let sexp_of_set_validity valid =
  make_sexp "Una.SetValidity" [ sexp_of_bool valid ]

let sexp_of_una = function
  | Una.Not -> Sexp.Atom "Una.Not"
  | Una.BitNot -> Sexp.Atom "Una.BitNot"
  | Una.Minus -> Sexp.Atom "Una.Minus"
  | Una.IsValid -> Sexp.Atom "Una.IsValid"
  | Una.SetValidity valid -> sexp_of_set_validity valid

let string_of_bin = function
  | Bin.Plus -> "Bin.Plus"
  | Bin.PlusSat -> "Bin.PlusSat"
  | Bin.Minus -> "Bin.Minus"
  | Bin.MinusSat -> "Bin.MinusSat"
  | Bin.Times -> "Bin.Times"
  | Bin.Shl -> "Bin.Shl"
  | Bin.Shr -> "Bin.Shr"
  | Bin.Le -> "Bin.Le"
  | Bin.Ge -> "Bin.Ge"
  | Bin.Lt -> "Bin.Lt"
  | Bin.Gt -> "Bin.Gt"
  | Bin.Eq -> "Bin.Eq"
  | Bin.NotEq -> "Bin.NotEq"
  | Bin.BitAnd -> "Bin.BitAnd"
  | Bin.BitXor -> "Bin.BitXor"
  | Bin.BitOr -> "Bin.BitOr"
  | Bin.PlusPlus -> "Bin.PlusPlus"
  | Bin.And -> "Bin.And"
  | Bin.Or -> "Bin.Or"

let sexp_of_bin bin = Sexp.Atom (string_of_bin bin)

let rec sexp_of_type = function
  | Typ.Bool -> Sexp.Atom "Typ.Bool"
  | Typ.Bit width -> sexp_of_bit_type width
  | Typ.Int width -> sexp_of_int_type width
  | Typ.Error -> Sexp.Atom "Typ.Error"
  | Typ.Struct (is_header, fields) -> sexp_of_struct_type is_header fields
  | Typ.Array (size, typ) -> sexp_of_array_type size typ
  | Typ.Var idx -> sexp_of_type_var idx
  | Typ.VarBit z -> Bigint.sexp_of_t z

and sexp_of_types types = sexp_of_list sexp_of_type types

and sexp_of_struct_type is_header fields =
  make_sexp "Typ.Struct" [ sexp_of_bool is_header; sexp_of_types fields ]

and sexp_of_array_type size typ =
  make_sexp "Typ.Array" [ Bigint.sexp_of_t size; sexp_of_type typ ]

let sexp_of_bool_exp b = make_sexp "Exp.Bool" [ sexp_of_bool b ]

let sexp_of_bit_exp width i =
  make_sexp "Exp.Bit" [ Bigint.sexp_of_t width; Bigint.sexp_of_t i ]

let sexp_of_int_exp width i =
  make_sexp "Exp.Int" [ Bigint.sexp_of_t width; Bigint.sexp_of_t i ]

let sexp_of_varbit_exp max_width width z =
  make_sexp "Exp.VarBit" [ Bigint.sexp_of_t max_width; Bigint.sexp_of_t width; Bigint.sexp_of_t z ]

let sexp_of_var_exp typ x idx =
  make_sexp "Exp.Var" [ sexp_of_type typ; Sexp.Atom x; sexp_of_int idx ]

let sexp_of_lists_array typ = make_sexp "Lst.Array" [ sexp_of_type typ ]
let sexp_of_lists_header b = make_sexp "Lst.Header" [ sexp_of_bool b ]
let sexp_of_error err = make_sexp "Exp.Error" [ Sexp.Atom err ]

let sexp_of_lists_type = function
  | Lst.Struct -> Sexp.Atom "Lst.Struct"
  | Lst.Array typ -> sexp_of_lists_array typ
  | Lst.Header b -> sexp_of_lists_header b

let rec sexp_of_exp = function
  | Exp.Bool b -> sexp_of_bool_exp b
  | Exp.Bit (width, i) -> sexp_of_bit_exp width i
  | Exp.Int (width, i) -> sexp_of_int_exp width i
  | Exp.Var (typ, x, idx) -> sexp_of_var_exp typ x idx
  | Exp.Slice (hi, lo, e) -> sexp_of_slice hi lo e
  | Exp.Cast (typ, e) -> sexp_of_cast typ e
  | Exp.Uop (typ, op, e) -> sexp_of_una_exp typ op e
  | Exp.Bop (typ, op, e1, e2) -> sexp_of_bin_exp typ op e1 e2
  | Exp.Lists (flag, es) -> sexp_of_lists flag es
  | Exp.Index (typ, array, index) -> sexp_of_index typ array index
  | Exp.Member (typ, mem, e) -> sexp_of_member typ mem e
  | Exp.Error msg -> sexp_of_error msg
  | Exp.VarBit (width_max, width, z) -> sexp_of_varbit_exp width_max width z

and sexp_of_exps es = sexp_of_list sexp_of_exp es

and sexp_of_slice hi lo e =
  make_sexp "Exp.Slice"
    [ Bigint.sexp_of_t hi; Bigint.sexp_of_t lo; sexp_of_exp e ]

and sexp_of_cast typ e =
  make_sexp "Exp.Cast" [ sexp_of_type typ; sexp_of_exp e ]

and sexp_of_una_exp typ op e =
  make_sexp "Exp.Bin" [ sexp_of_type typ; sexp_of_una op; sexp_of_exp e ]

and sexp_of_bin_exp typ op e1 e2 =
  make_sexp "Exp.Bin"
    [ sexp_of_type typ; sexp_of_bin op; sexp_of_exp e1; sexp_of_exp e2 ]

and sexp_of_lists flag es =
  make_sexp "Exp.Lists" [ sexp_of_lists_type flag; sexp_of_exps es ]

and sexp_of_index typ array index =
  make_sexp "Exp.Index"
    [ sexp_of_type typ; sexp_of_exp array; sexp_of_exp index ]

and sexp_of_member typ mem e =
  make_sexp "Exp.Member" [ sexp_of_type typ; sexp_of_int mem; sexp_of_exp e ]

let sexp_of_exp_opt = sexp_of_option sexp_of_exp

let sexp_of_state_label = function
  | Lbl.Start -> Sexp.Atom "Lbl.Start"
  | Lbl.Accept -> Sexp.Atom "Lbl.Accept"
  | Lbl.Reject -> Sexp.Atom "Lbl.Reject"
  | Lbl.Name st -> make_sexp "Lbl.Name" [ sexp_of_int st ]

let sexp_of_direct_transition st =
  make_sexp "Trns.Direct" [ sexp_of_state_label st ]

let sexp_of_bit_pat width value =
  make_sexp "Pat.Bit" [ Bigint.sexp_of_t width; Bigint.sexp_of_t value ]

let sexp_of_int_pat width value =
  make_sexp "Pat.Int" [ Bigint.sexp_of_t width; Bigint.sexp_of_t value ]

(** [sexp_of_fields sexp_of_key sexp_of_value \[(k1, v1); ...; (kn, vn)\]] is
    the s-expession [((k1' v1') ... (kn' vn'))] where [ki' = sexp_of_key ki]
    and [vi' = sexp_of_val vi] *)
let sexp_of_fields sexp_of_key sexp_of_value =
  sexp_of_list (sexp_of_pair sexp_of_key sexp_of_value)

(** [sexp_of_dict sexp_of_value \[(k1, v1); ...; (kn, vn)\]] is the s-expession
    [((k1 v1') ... (kn vn'))] where [vi' = sexp_of_val vi] *)
let sexp_of_dict sexp_of_value = sexp_of_fields sexp_of_string sexp_of_value

let rec sexp_of_pat = function
  | Pat.Wild -> Sexp.Atom "Pat.Wild"
  | Pat.Mask (p1, p2) -> sexp_of_mask p1 p2
  | Pat.Range (lo, hi) -> sexp_of_range lo hi
  | Pat.Bit (width, value) -> sexp_of_bit_pat width value
  | Pat.Int (width, value) -> sexp_of_int_pat width value
  | Pat.Lists ps -> sexp_of_list_pat ps

and sexp_of_mask p1 p2 =
  make_sexp "Pat.Mask" [ sexp_of_pat p1; sexp_of_pat p2 ]

and sexp_of_range lo hi =
  make_sexp "Pat.Range" [ sexp_of_pat lo; sexp_of_pat hi ]

and sexp_of_list_pat ps =
  make_sexp "Pat.List" [ sexp_of_list sexp_of_pat ps ]

let sexp_of_parser_select discriminee default cases =
  make_sexp "Trns.Select"
    [
      sexp_of_exp discriminee;
      sexp_of_state_label default;
      sexp_of_fields sexp_of_pat sexp_of_state_label cases;
    ]

let sexp_of_parser_transition = function
  | Trns.Direct st -> sexp_of_direct_transition st
  | Trns.Select (discriminee, default, cases) ->
      sexp_of_parser_select discriminee default cases

let sexp_of_return e = make_sexp "Stm.Ret" [ sexp_of_exp_opt e ]

let sexp_of_transition_stm trans =
  make_sexp "Stm.Trans" [ sexp_of_parser_transition trans ]

let sexp_of_assign lhs rhs =
  make_sexp "Stm.Asgn" [ sexp_of_exp lhs; sexp_of_exp rhs ]

let sexp_of_funct name type_args ret =
  make_sexp "Call.Funct"
    [ Sexp.Atom name; sexp_of_types type_args; sexp_of_exp_opt ret ]

let sexp_of_action name ctrl_args =
  make_sexp "Call.Action" [ Sexp.Atom name; sexp_of_exps ctrl_args ]

let sexp_of_method extern_name name type_args ret =
  make_sexp "Call.Method"
    [
      Sexp.Atom extern_name;
      Sexp.Atom name;
      sexp_of_types type_args;
      sexp_of_exp_opt ret;
    ]

let sexp_of_apply name ext_args =
  make_sexp "Call.Inst" [ sexp_of_string name; sexp_of_strings ext_args ]

let sexp_of_call = function
  | Call.Funct (name, type_args, ret) -> sexp_of_funct name type_args ret
  | Call.Action (name, ctrl_args) -> sexp_of_action name ctrl_args
  | Call.Method (extern_name, name, type_args, ret) ->
      sexp_of_method extern_name name type_args ret
  | Call.Inst (name, ext_args) -> sexp_of_apply name ext_args

let sexp_of_paramarg f = function
  | PAIn a -> make_sexp "PAIn" [ f a ]
  | PAOut a -> make_sexp "PAOut" [ f a ]
  | PAInOut a -> make_sexp "PAInOut" [ f a ]

let sexp_of_param = sexp_of_paramarg sexp_of_type
let sexp_of_params = sexp_of_dict sexp_of_param
let sexp_of_arg = sexp_of_paramarg sexp_of_exp
let sexp_of_args = sexp_of_list sexp_of_arg

let sexp_of_app call args =
  make_sexp "Stm.App" [ sexp_of_call call; sexp_of_args args ]

let sexp_of_invoke eo name =
make_sexp "Stm.Invoke" [ sexp_of_exp_opt eo; Sexp.Atom name ]

(** [map_sum f g (inl a)] is [f a] and [map_sum f g (inr b)] is [g b] *)
let map_sum f g =
  let open Poulet4.Datatypes in
  function
  | Coq_inl l -> f l
  | Coq_inr r -> g r

let sexp_of_var_init = map_sum sexp_of_type sexp_of_exp

let rec sexp_of_stm = function
  | Stm.Skip -> Sexp.Atom "Stm.Skip"
  | Stm.Ret e -> sexp_of_return e
  | Stm.Exit -> Sexp.Atom "Stm.Exit"
  | Stm.Trans trans -> sexp_of_transition_stm trans
  | Stm.Asgn (lhs, rhs) -> sexp_of_assign lhs rhs
  | Stm.App (call, args) -> sexp_of_app call args
  | Stm.Invoke (eo, name) -> sexp_of_invoke eo name
  | Stm.LetIn (x, e, tail) -> sexp_of_var_decl x e tail
  | Stm.Seq (h, t) -> sexp_of_seq_stm h t
  | Stm.Cond (e, s1, s2) -> sexp_of_conditional e s1 s2

and sexp_of_var_decl x e init =
  make_sexp "Stm.LetIn" [ Sexp.Atom x; sexp_of_var_init e; sexp_of_stm init ]

and sexp_of_seq_stm h t =
  make_sexp "Stm.Seq" [ sexp_of_stm h; sexp_of_stm t ]

and sexp_of_conditional e s1 s2 =
  make_sexp "Stm.Cond"
    [ sexp_of_exp e; sexp_of_stm s1; sexp_of_stm s2 ]

let sexp_of_control_var x e =
  make_sexp "Ctrl.Var" [ Sexp.Atom x; sexp_of_var_init e ]

let sexp_of_control_action_decl name cparams dparams body =
  make_sexp "Ctrl.Action"
    [
      Sexp.Atom name;
      sexp_of_dict sexp_of_type cparams;
      sexp_of_params dparams;
      sexp_of_stm body;
    ]

let sexp_of_control_table_decl name key actions def =
  make_sexp "Ctrl.Table"
    [
      Sexp.Atom name;
      sexp_of_fields sexp_of_exp sexp_of_string key;
      sexp_of_dict sexp_of_args actions;
      sexp_of_option (sexp_of_pair sexp_of_string sexp_of_exps)  def
    ]

let sexp_of_control_decl = function
  | Ctrl.Var (x, e) -> sexp_of_control_var x e
  | Ctrl.Action (name, cparams, dparams, body) ->
      sexp_of_control_action_decl name cparams dparams body
  | Ctrl.Table (name, key, actions, def) ->
      sexp_of_control_table_decl name key actions def

let sexp_of_cnstr = function
  | Cnstr.Control -> Sexp.Atom "Cnstr.Control"
  | Cnstr.Parser  -> Sexp.Atom "Cnstr.Parser"

let sexp_of_ctr_inst_type flag extern_params params =
  make_sexp "InstTyp.Ctr"
    [ sexp_of_cnstr flag; sexp_of_strings extern_params; sexp_of_params params ]

let sexp_of_extern_inst_type name =
  make_sexp "InstTyp..Extern" [ Sexp.Atom name ]

let sexp_of_constructor_param_type = function
  | InstTyp.Ctr (flag, extern_params, params) ->
      sexp_of_ctr_inst_type flag extern_params params
  | InstTyp.Package -> Sexp.Atom "Top.PackageInstType"
  | InstTyp.Extern name -> sexp_of_extern_inst_type name

let sexp_of_constructor_params = sexp_of_dict sexp_of_constructor_param_type

let sexp_of_function_type ({ paramargs; rtrns } : Typ.arrowT) =
  let params_sexp = sexp_of_params paramargs in
  let rtrns_sexp = sexp_of_option sexp_of_type rtrns in
  Sexp.List
    [
      Sexp.List [ Sexp.Atom "paramargs"; params_sexp ];
      Sexp.List [ Sexp.Atom "rtrns"; rtrns_sexp ];
    ]

let sexp_of_instantiate constructor instance type_args cargs es =
  make_sexp "Top.Instantiate"
    [
      Sexp.Atom constructor;
      Sexp.Atom instance;
      sexp_of_types type_args;
      sexp_of_strings cargs;
      sexp_of_exps es;
    ]

let sexp_of_extern name type_params cparams exp_cparams methods =
  let sexp_of_method_sig ((type_params, extern_params), params) =
    Sexp.List
      [
        sexp_of_int type_params;
        sexp_of_strings extern_params;
        sexp_of_function_type params;
      ]
  in
  make_sexp "Top.Extern"
    [
      Sexp.Atom name;
      sexp_of_int type_params;
      sexp_of_constructor_params cparams;
      sexp_of_types exp_cparams;
      sexp_of_dict sexp_of_method_sig methods;
    ]

let sexp_of_control name cparams exp_cparams eparams params body s =
  make_sexp "Top.Control"
    [
      Sexp.Atom name;
      sexp_of_constructor_params cparams;
      sexp_of_types exp_cparams;
      sexp_of_dict sexp_of_string eparams;
      sexp_of_params params;
      sexp_of_list sexp_of_control_decl body;
      sexp_of_stm s;
    ]

let sexp_of_parser name cparams exp_cparams eparams params start states =
  make_sexp "Top.Parser"
    [
      Sexp.Atom name;
      sexp_of_constructor_params cparams;
      sexp_of_dict sexp_of_string eparams;
      sexp_of_params params;
      sexp_of_stm start;
      sexp_of_list sexp_of_stm states;
    ]

let sexp_of_funct name type_params signature body =
  make_sexp "Top.Funct"
    [
      Sexp.Atom name;
      sexp_of_int type_params;
      sexp_of_function_type signature;
      sexp_of_stm body;
    ]

let sexp_of_top_decl : Top.t -> Sexp.t = function
  | Top.Instantiate (constructor, instance, type_args, cargs, es) ->
      sexp_of_instantiate constructor instance type_args cargs es
  | Top.Extern (name, type_params, cparams, exp_cparams, methods) ->
      sexp_of_extern name type_params cparams exp_cparams methods
  | Top.Control (name, cparams, exp_cparams, eparams, params, body, s) ->
      sexp_of_control name cparams exp_cparams eparams params body s
  | Top.Parser (name, cparams, exp_cparams, eparams, params, start, states)
    -> sexp_of_parser name cparams exp_cparams eparams params start states
  | Top.Funct (name, type_params, signature, body) ->
      sexp_of_funct name type_params signature body

let sexp_of_prog : Top.prog -> Sexp.t = sexp_of_list sexp_of_top_decl

let print fmt prog = prog |> sexp_of_prog |> Sexp.pp_hum fmt
