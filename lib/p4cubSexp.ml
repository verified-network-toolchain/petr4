open Core
open Sexplib.Std
open Poulet4.AST

(** [make_sexp name args] is the s-expression [(name args)]; the s-expression of
    constructor with name [name] and arguments [args] *)
let make_sexp name args = Sexp.List (Sexp.Atom name :: args)

let sexp_of_strings = sexp_of_list sexp_of_string
let sexp_of_bit_type width = make_sexp "Expr.TBool" [ Bigint.sexp_of_t width ]
let sexp_of_int_type width = make_sexp "Expr.TInt" [ Bigint.sexp_of_t width ]
let sexp_of_type_var idx = make_sexp "Expr.TVar" [ sexp_of_int idx ]

let sexp_of_set_validity valid =
  make_sexp "Expr.SetValidity" [ sexp_of_bool valid ]

let sexp_of_uop = function
  | Expr.Not -> Sexp.Atom "Expr.Not"
  | Expr.BitNot -> Sexp.Atom "Expr.BitNot"
  | Expr.UMinus -> Sexp.Atom "Expr.UMinus"
  | Expr.IsValid -> Sexp.Atom "Expr.IsValid"
  | Expr.SetValidity valid -> sexp_of_set_validity valid

let string_of_bop = function
  | Expr.Plus -> "Expr.Plus"
  | Expr.PlusSat -> "Expr.PlusSat"
  | Expr.Minus -> "Expr.Minus"
  | Expr.MinusSat -> "Expr.MinusSat"
  | Expr.Times -> "Expr.Times"
  | Expr.Shl -> "Expr.Shl"
  | Expr.Shr -> "Expr.Shr"
  | Expr.Le -> "Expr.Le"
  | Expr.Ge -> "Expr.Ge"
  | Expr.Lt -> "Expr.Lt"
  | Expr.Gt -> "Expr.Gt"
  | Expr.Eq -> "Expr.Eq"
  | Expr.NotEq -> "Expr.NotEq"
  | Expr.BitAnd -> "Expr.BitAnd"
  | Expr.BitXor -> "Expr.BitXor"
  | Expr.BitOr -> "Expr.BitOr"
  | Expr.PlusPlus -> "Expr.PlusPlus"
  | Expr.And -> "Expr.And"
  | Expr.Or -> "Expr.Or"

let sexp_of_bop bop = Sexp.Atom (string_of_bop bop)

let rec sexp_of_type = function
  | Expr.TBool -> Sexp.Atom "Expr.TBool"
  | Expr.TBit width -> sexp_of_bit_type width
  | Expr.TInt width -> sexp_of_int_type width
  | Expr.TError -> Sexp.Atom "Expr.TError"
  | Expr.TStruct (is_header, fields) -> sexp_of_struct_type is_header fields
  | Expr.TArray (size, typ) -> sexp_of_array_type size typ
  | Expr.TVar idx -> sexp_of_type_var idx
  | Expr.TVarBit z -> Bigint.sexp_of_t z

and sexp_of_types types = sexp_of_list sexp_of_type types

and sexp_of_struct_type is_header fields =
  make_sexp "Expr.TStruct" [ sexp_of_bool is_header; sexp_of_types fields ]

and sexp_of_array_type size typ =
  make_sexp "Expr.TArray" [ Bigint.sexp_of_t size; sexp_of_type typ ]

let sexp_of_bool_expr b = make_sexp "Expr.Bool" [ sexp_of_bool b ]

let sexp_of_bit_expr width i =
  make_sexp "Expr.Bit" [ Bigint.sexp_of_t width; Bigint.sexp_of_t i ]

let sexp_of_int_expr width i =
  make_sexp "Expr.Int" [ Bigint.sexp_of_t width; Bigint.sexp_of_t i ]

let sexp_of_varbit_expr max_width width z =
  make_sexp "Expr.VarBit" [ Bigint.sexp_of_t max_width; Bigint.sexp_of_t width; Bigint.sexp_of_t z ]

let sexp_of_var_expr typ x idx =
  make_sexp "Expr.Var" [ sexp_of_type typ; Sexp.Atom x; sexp_of_int idx ]

let sexp_of_lists_array typ = make_sexp "Expr.lists_array" [ sexp_of_type typ ]
let sexp_of_lists_header b = make_sexp "Expr.lists_header" [ sexp_of_bool b ]
let sexp_of_error err = make_sexp "Expr.Error" [ Sexp.Atom err ]

let sexp_of_lists_type = function
  | Expr.Coq_lists_struct -> Sexp.Atom "Expr.lists_struct"
  | Expr.Coq_lists_array typ -> sexp_of_lists_array typ
  | Expr.Coq_lists_header b -> sexp_of_lists_header b

let rec sexp_of_expr = function
  | Expr.Bool b -> sexp_of_bool_expr b
  | Expr.Bit (width, i) -> sexp_of_bit_expr width i
  | Expr.Int (width, i) -> sexp_of_int_expr width i
  | Expr.Var (typ, x, idx) -> sexp_of_var_expr typ x idx
  | Expr.Slice (hi, lo, e) -> sexp_of_slice hi lo e
  | Expr.Cast (typ, e) -> sexp_of_cast typ e
  | Expr.Uop (typ, op, e) -> sexp_of_uop_expr typ op e
  | Expr.Bop (typ, op, e1, e2) -> sexp_of_bop_expr typ op e1 e2
  | Expr.Lists (flag, es) -> sexp_of_lists flag es
  | Expr.Index (typ, array, index) -> sexp_of_index typ array index
  | Expr.Member (typ, mem, e) -> sexp_of_member typ mem e
  | Expr.Error msg -> sexp_of_error msg
  | Expr.VarBit (width_max, width, z) -> sexp_of_varbit_expr width_max width z

and sexp_of_exprs es = sexp_of_list sexp_of_expr es

and sexp_of_slice hi lo e =
  make_sexp "Expr.Slice"
    [ Bigint.sexp_of_t hi; Bigint.sexp_of_t lo; sexp_of_expr e ]

and sexp_of_cast typ e =
  make_sexp "Expr.Cast" [ sexp_of_type typ; sexp_of_expr e ]

and sexp_of_uop_expr typ op e =
  make_sexp "Expr.Uop" [ sexp_of_type typ; sexp_of_uop op; sexp_of_expr e ]

and sexp_of_bop_expr typ op e1 e2 =
  make_sexp "Expr.Bop"
    [ sexp_of_type typ; sexp_of_bop op; sexp_of_expr e1; sexp_of_expr e2 ]

and sexp_of_lists flag es =
  make_sexp "Expr.Lists" [ sexp_of_lists_type flag; sexp_of_exprs es ]

and sexp_of_index typ array index =
  make_sexp "Expr.Index"
    [ sexp_of_type typ; sexp_of_expr array; sexp_of_expr index ]

and sexp_of_member typ mem e =
  make_sexp "Expr.Member" [ sexp_of_type typ; sexp_of_int mem; sexp_of_expr e ]

let sexp_of_expr_opt = sexp_of_option sexp_of_expr

let sexp_of_state_label = function
  | Parser.Start -> Sexp.Atom "Parser.Start"
  | Parser.Accept -> Sexp.Atom "Parser.Accept"
  | Parser.Reject -> Sexp.Atom "Parser.Reject"
  | Parser.Name st -> make_sexp "Parser.Name" [ sexp_of_int st ]

let sexp_of_direct_transition st =
  make_sexp "Parser.Direct" [ sexp_of_state_label st ]

let sexp_of_bit_pat width value =
  make_sexp "Parser.Bit" [ Bigint.sexp_of_t width; Bigint.sexp_of_t value ]

let sexp_of_int_pat width value =
  make_sexp "Parser.Int" [ Bigint.sexp_of_t width; Bigint.sexp_of_t value ]

(** [sexp_of_fields sexp_of_key sexp_of_value \[(k1, v1); ...; (kn, vn)\]] is
    the s-expression [((k1' v1') ... (kn' vn'))] where [ki' = sexp_of_key ki]
    and [vi' = sexp_of_val vi] *)
let sexp_of_fields sexp_of_key sexp_of_value =
  sexp_of_list (sexp_of_pair sexp_of_key sexp_of_value)

(** [sexp_of_dict sexp_of_value \[(k1, v1); ...; (kn, vn)\]] is the s-expression
    [((k1 v1') ... (kn vn'))] where [vi' = sexp_of_val vi] *)
let sexp_of_dict sexp_of_value = sexp_of_fields sexp_of_string sexp_of_value

let rec sexp_of_pat = function
  | Parser.Wild -> Sexp.Atom "Parser.Wild"
  | Parser.Mask (p1, p2) -> sexp_of_mask p1 p2
  | Parser.Range (lo, hi) -> sexp_of_range lo hi
  | Parser.Bit (width, value) -> sexp_of_bit_pat width value
  | Parser.Int (width, value) -> sexp_of_int_pat width value
  | Parser.Lists ps -> sexp_of_list_pat ps

and sexp_of_mask p1 p2 =
  make_sexp "Parser.Mask" [ sexp_of_pat p1; sexp_of_pat p2 ]

and sexp_of_range lo hi =
  make_sexp "Parser.Range" [ sexp_of_pat lo; sexp_of_pat hi ]

and sexp_of_list_pat ps =
  make_sexp "Parser.List" [ sexp_of_list sexp_of_pat ps ]

let sexp_of_parser_select discriminee default cases =
  make_sexp "Parser.Select"
    [
      sexp_of_expr discriminee;
      sexp_of_state_label default;
      sexp_of_fields sexp_of_pat sexp_of_state_label cases;
    ]

let sexp_of_parser_transition = function
  | Parser.Direct st -> sexp_of_direct_transition st
  | Select (discriminee, default, cases) ->
      sexp_of_parser_select discriminee default cases

let sexp_of_return e = make_sexp "Stmt.Return" [ sexp_of_expr_opt e ]

let sexp_of_transition_stmt trans =
  make_sexp "Stmt.Transition" [ sexp_of_parser_transition trans ]

let sexp_of_assign lhs rhs =
  make_sexp "Stmt.Assign" [ sexp_of_expr lhs; sexp_of_expr rhs ]

let sexp_of_funct name type_args ret =
  make_sexp "Stmt.Funct"
    [ Sexp.Atom name; sexp_of_types type_args; sexp_of_expr_opt ret ]

let sexp_of_action name ctrl_args =
  make_sexp "Stmt.Action" [ Sexp.Atom name; sexp_of_exprs ctrl_args ]

let sexp_of_method extern_name name type_args ret =
  make_sexp "Stmt.Method"
    [
      Sexp.Atom extern_name;
      Sexp.Atom name;
      sexp_of_types type_args;
      sexp_of_expr_opt ret;
    ]

let sexp_of_fun_kind = function
  | Stmt.Funct (name, type_args, ret) -> sexp_of_funct name type_args ret
  | Stmt.Action (name, ctrl_args) -> sexp_of_action name ctrl_args
  | Stmt.Method (extern_name, name, type_args, ret) ->
      sexp_of_method extern_name name type_args ret

let sexp_of_paramarg f = function
  | PAIn a -> make_sexp "PAIn" [ f a ]
  | PAOut a -> make_sexp "PAOut" [ f a ]
  | PAInOut a -> make_sexp "PAInOut" [ f a ]

let sexp_of_param = sexp_of_paramarg sexp_of_type
let sexp_of_params = sexp_of_dict sexp_of_param
let sexp_of_arg = sexp_of_paramarg sexp_of_expr
let sexp_of_args = sexp_of_list sexp_of_arg

let sexp_of_call call args =
  make_sexp "Stmt.Call" [ sexp_of_fun_kind call; sexp_of_args args ]

let sexp_of_invoke eo name =
make_sexp "Stmt.Invoke" [ sexp_of_expr_opt eo; Sexp.Atom name ]

let sexp_of_apply name ext_args args =
  make_sexp "Stmt.Apply" [ sexp_of_strings ext_args; sexp_of_args args ]

(** [map_sum f g (inl a)] is [f a] and [map_sum f g (inr b)] is [g b] *)
let map_sum f g =
  let open Poulet4.Datatypes in
  function
  | Coq_inl l -> f l
  | Coq_inr r -> g r

let sexp_of_var_init = map_sum sexp_of_type sexp_of_expr

let rec sexp_of_stmt = function
  | Stmt.Skip -> Sexp.Atom "Stmt.Skip"
  | Stmt.Return e -> sexp_of_return e
  | Stmt.Exit -> Sexp.Atom "Stmt.Exit"
  | Stmt.Transition trans -> sexp_of_transition_stmt trans
  | Stmt.Assign (lhs, rhs) -> sexp_of_assign lhs rhs
  | Stmt.Call (call, args) -> sexp_of_call call args
  | Stmt.Invoke (eo, name) -> sexp_of_invoke eo name
  | Stmt.Apply (name, ext_args, args) -> sexp_of_apply name ext_args args
  | Stmt.Var (x, e, tail) -> sexp_of_var_decl x e tail
  | Stmt.Seq (h, t) -> sexp_of_seq_stmt h t
  | Stmt.Conditional (e, s1, s2) -> sexp_of_conditional e s1 s2

and sexp_of_var_decl x e init =
  make_sexp "Stmt.Var" [ Sexp.Atom x; sexp_of_var_init e; sexp_of_stmt init ]

and sexp_of_seq_stmt h t =
  make_sexp "Stmt.Seq" [ sexp_of_stmt h; sexp_of_stmt t ]

and sexp_of_conditional e s1 s2 =
  make_sexp "Stmt.Conditional"
    [ sexp_of_expr e; sexp_of_stmt s1; sexp_of_stmt s2 ]

let sexp_of_control_var x e =
  make_sexp "Control.Var" [ Sexp.Atom x; sexp_of_var_init e ]

let sexp_of_control_action_decl name cparams dparams body =
  make_sexp "Control.Action"
    [
      Sexp.Atom name;
      sexp_of_dict sexp_of_type cparams;
      sexp_of_params dparams;
      sexp_of_stmt body;
    ]

let sexp_of_control_table_decl name key actions def =
  make_sexp "Control.Table"
    [
      Sexp.Atom name;
      sexp_of_fields sexp_of_expr sexp_of_string key;
      sexp_of_dict sexp_of_args actions;
      sexp_of_option (sexp_of_pair sexp_of_string sexp_of_exprs)  def
    ]

let sexp_of_control_decl = function
  | Control.Var (x, e) -> sexp_of_control_var x e
  | Control.Action (name, cparams, dparams, body) ->
      sexp_of_control_action_decl name cparams dparams body
  | Control.Table (name, key, actions, def) ->
      sexp_of_control_table_decl name key actions def

let sexp_of_control_inst_type extern_params params =
  make_sexp "TopDecl.ControlInstType"
    [ sexp_of_strings extern_params; sexp_of_params params ]

let sexp_of_parser_inst_type extern_params params =
  make_sexp "TopDecl.ParserInstType"
    [ sexp_of_strings extern_params; sexp_of_params params ]

let sexp_of_extern_inst_type name =
  make_sexp "TopDecl.ExternInstType" [ Sexp.Atom name ]

let sexp_of_constructor_param_type = function
  | TopDecl.ControlInstType (extern_params, params) ->
      sexp_of_control_inst_type extern_params params
  | TopDecl.ParserInstType (extern_params, params) ->
      sexp_of_parser_inst_type extern_params params
  | TopDecl.PackageInstType -> Sexp.Atom "TopDecl.PackageInstType"
  | ExternInstType name -> sexp_of_extern_inst_type name

let sexp_of_constructor_params = sexp_of_dict sexp_of_constructor_param_type

let sexp_of_function_type ({ paramargs; rtrns } : Expr.arrowT) =
  let params_sexp = sexp_of_params paramargs in
  let rtrns_sexp = sexp_of_option sexp_of_type rtrns in
  Sexp.List
    [
      Sexp.List [ Sexp.Atom "paramargs"; params_sexp ];
      Sexp.List [ Sexp.Atom "rtrns"; rtrns_sexp ];
    ]

let sexp_of_instantiate constructor instance type_args cargs es =
  make_sexp "TopDecl.Instantiate"
    [
      Sexp.Atom constructor;
      Sexp.Atom instance;
      sexp_of_types type_args;
      sexp_of_strings cargs;
      sexp_of_exprs es;
    ]

let sexp_of_extern name type_params cparams expr_cparams methods =
  let sexp_of_method_sig ((type_params, extern_params), params) =
    Sexp.List
      [
        sexp_of_int type_params;
        sexp_of_strings extern_params;
        sexp_of_function_type params;
      ]
  in
  make_sexp "TopDecl.Extern"
    [
      Sexp.Atom name;
      sexp_of_int type_params;
      sexp_of_constructor_params cparams;
      sexp_of_types expr_cparams;
      sexp_of_dict sexp_of_method_sig methods;
    ]

let sexp_of_control name cparams expr_cparams eparams params body s =
  make_sexp "TopDecl.Control"
    [
      Sexp.Atom name;
      sexp_of_constructor_params cparams;
      sexp_of_types expr_cparams;
      sexp_of_dict sexp_of_string eparams;
      sexp_of_params params;
      sexp_of_list sexp_of_control_decl body;
      sexp_of_stmt s;
    ]

let sexp_of_parser name cparams expr_cparams eparams params start states =
  make_sexp "TopDecl.Parser"
    [
      Sexp.Atom name;
      sexp_of_constructor_params cparams;
      sexp_of_dict sexp_of_string eparams;
      sexp_of_params params;
      sexp_of_stmt start;
      sexp_of_list sexp_of_stmt states;
    ]

let sexp_of_funct name type_params signature body =
  make_sexp "TopDecl.Funct"
    [
      Sexp.Atom name;
      sexp_of_int type_params;
      sexp_of_function_type signature;
      sexp_of_stmt body;
    ]

let sexp_of_top_decl : TopDecl.d -> Sexp.t = function
  | TopDecl.Instantiate (constructor, instance, type_args, cargs, es) ->
      sexp_of_instantiate constructor instance type_args cargs es
  | TopDecl.Extern (name, type_params, cparams, expr_cparams, methods) ->
      sexp_of_extern name type_params cparams expr_cparams methods
  | TopDecl.Control (name, cparams, expr_cparams, eparams, params, body, s) ->
      sexp_of_control name cparams expr_cparams eparams params body s
  | TopDecl.Parser (name, cparams, expr_cparams, eparams, params, start, states)
    -> sexp_of_parser name cparams expr_cparams eparams params start states
  | TopDecl.Funct (name, type_params, signature, body) ->
      sexp_of_funct name type_params signature body

let sexp_of_prog : TopDecl.prog -> Sexp.t = sexp_of_list sexp_of_top_decl

let print fmt prog = prog |> sexp_of_prog |> Sexp.pp_hum fmt
