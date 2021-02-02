exception IncorrectType of string
exception MultipleMains
exception DeclarationNotFound of string
exception DuplicateDeclarationName
exception MissingDeclaration
module P4 = Types

(** Record for temp control *)
type tempControl = { annotations: P4.Annotation.t list;
                     name: P4.P4String.t;
                     type_params: P4.P4String.t list;
                     params: P4.Parameter.t list;
                     constructor_params: P4.Parameter.t list;
                     locals: P4.Declaration.t list;
                     apply: P4.Block.t }

let control_info (d : P4.Declaration.t) : tempControl = match (snd d) with
  | P4.Declaration.Control { annotations; name; type_params; params; constructor_params; locals; apply } ->
    { annotations = annotations; 
      name = name; 
      type_params = type_params; 
      params = params; 
      constructor_params = constructor_params; 
      locals = locals; 
      apply = apply }
  | _ -> raise (IncorrectType "Control type expected")
(** Record for temp control *)

let get = function 
  | Some x -> x
  | None -> raise (IncorrectType "Got None when expected Some")

let program_to_declarations (prog:P4.program) : P4.Declaration.t list = match prog with
  | Program decls -> decls 

(** Finding main declaration names*)
let get_typename_name (t : P4.Type.t) : string = match (snd t) with 
  | TypeName typename -> P4.name_only typename
  | _ -> raise (IncorrectType "Expected TypeName")

let get_argument_name (a : P4.Argument.t) : string = match (snd a) with 
  | P4.Argument.Expression {value} -> (match (snd value) with 
      | P4.Expression.NamelessInstantiation {typ; args} -> get_typename_name typ
      | _ -> raise (IncorrectType "NamelessInstantiation expected"))
  | _ -> raise (IncorrectType "Argument Expression expected")

let get_parameter_name (p : P4.Parameter.t) : string = match (snd p) with
  | {annotations; direction; typ; variable; opt_value} -> get_typename_name typ

let get_instantiation (prog:P4.Declaration.t) : P4.Declaration.t option = 
  match (snd prog) with 
  | P4.Declaration.Instantiation {annotations; typ; args; name; init} -> 
    Some (Info.dummy, P4.Declaration.Instantiation {annotations; typ; args; name; init})
  | _ -> None

let get_instantiation_args (d : P4.Declaration.t) : P4.Argument.t list option = 
  match (snd d) with 
  | P4.Declaration.Instantiation {annotations; typ; args; name; init} -> Some args
  | _ -> None

let get_declaration_params (p:P4.Declaration.t) : P4.Parameter.t list option = 
  match (snd p) with
  | P4.Declaration.Parser {annotations; name; type_params; params; constructor_params; locals; states} -> Some params
  | P4.Declaration.Control {annotations; name; type_params; params; constructor_params; locals; apply} -> Some params
  | _ -> None

let get_main (prog:P4.Declaration.t list) : P4.Declaration.t = 
  let main = List.filter_map get_instantiation prog in 
  if List.length main == 0 then raise (DeclarationNotFound "main")
  else if List.length main <> 1 then raise MultipleMains
  else (List.hd main)

(** Finding main declaration names from package. 
    For up4, should return [package_name, parser_name, control_name, deparser_name] *)
let get_main_args (prog : P4.Declaration.t list) : string list = 
  let main = (List.filter_map get_instantiation_args prog) in 
  if List.length main == 0 then raise (DeclarationNotFound "main")
  else if List.length main <> 1 then raise MultipleMains
  else (List.map get_argument_name (List.hd main))

let declaration_name (d : P4.Declaration.t) : string = snd (P4.Declaration.name d)

(**Can declarations have same name? (across all of controls, externs, parser, etc) *)
let find_declaration_by_name (prog:P4.Declaration.t list) (name:string) : P4.Declaration.t = 
  let declarations = List.filter (fun p -> declaration_name p == name) prog in 
  if List.length declarations == 0 then raise (DeclarationNotFound name)
  else List.hd declarations

let find_declarations_by_names (prog:P4.Declaration.t list) (names:string list) : P4.Declaration.t list = 
  List.filter (fun p -> List.mem (declaration_name p) names) prog


let remove_declaration (prog:P4.Declaration.t list) (to_remove_name:string) : P4.Declaration.t list = 
  List.filter (fun d -> declaration_name d <> to_remove_name) prog

let remove_declarations (prog:P4.Declaration.t list) (to_remove_names:string list) : P4.Declaration.t list = 
  List.filter (fun d -> not (List.mem (declaration_name d) to_remove_names)) prog

(**creating standard_meta, might be useless? *)
let standard_meta : P4.Type.t = Info.M "Standard Meta", P4.Type.TypeName (P4.BareName (Info.M "Standard Meta", "standard_metadata_t"))

let standard_meta_param (info: Info.t) : P4.Parameter.t = let open P4.Parameter in 
  (info, { annotations = [];
           direction = Some (Info.dummy, P4.Direction.InOut);
           typ = standard_meta;
           variable = (Info.M "Created_standard_meta_param", "standard_metadata");
           opt_value = None})


(** Creating generic/other types*)
let create_P4Int (value:int) : P4.P4Int.t = let open P4.P4Int in
  Info.dummy, {
    value = Bigint.of_int value;
    width_signed = None}

let create_match (expr:P4.Expression.t) : P4.Match.t = 
  Info.dummy, P4.Match.Expression {expr = expr}

let create_block (statements:P4.Statement.t list) : P4.Block.t = 
  Info.dummy, {
    annotations = [];
    statements = statements}

let create_argument_expression (expr:P4.Expression.t) = 
  Info.dummy, P4.Argument.Expression {value = expr}

(**Create P4.type types *)
let create_type_typename (t : string) : P4.Type.t = 
  Info.dummy, P4.Type.TypeName (P4.BareName (Info.dummy, t))
(**Create P4.type types *)

(** Create statement types *)
let create_statement_if (condition : P4.Expression.pre_t) (true_branch : P4.Statement.pre_t)
    (false_branch : P4.Statement.pre_t) : P4.Statement.t =
  (Info.M "Created If", P4.Statement.Conditional {
      cond = Info.M "Created Condition", condition; (**Binop on im_t.getinport *)
      tru = Info.M "Created true branch", true_branch;
      fls = Some (Info.M "Created false branch", false_branch)})

let create_statement_block (block:P4.Block.t) : P4.Statement.t = 
  Info.M "Created Block", P4.Statement.BlockStatement {block = block}

let create_statement_function_call (caller_name:string) (function_name:string) (args:P4.Argument.t list) : P4.Statement.t = 
  Info.M "Created method call", P4.Statement.MethodCall {
    func = (Info.dummy, P4.Expression.ExpressionMember {
        expr = Info.dummy, P4.Expression.Name (P4.BareName (Info.dummy, caller_name));
        name = Info.dummy, function_name});
    type_args = [];
    args = args}
(** Create statement types *)

(** Create expression types *)
let create_expression_int (n:int) : P4.Expression.t = Info.dummy, P4.Expression.Int (create_P4Int n)

let create_expression_binary_op (binop:P4.Op.bin) (args1:P4.Expression.t) (args2:P4.Expression.t) : P4.Expression.t = 
  Info.dummy, P4.Expression.BinaryOp {
    op = binop;
    args = args1, args2
  }

let create_expression_range (low:int) (high:int) : P4.Expression.t = 
  Info.dummy, P4.Expression.Range {
    lo = Info.dummy, P4.Expression.Int (create_P4Int low);
    hi = Info.dummy, P4.Expression.Int (create_P4Int high);
  }

let create_expression_name (name:string) : P4.Expression.t = 
  Info.dummy, P4.Expression.Name (P4.BareName (Info.dummy, name))

let create_expression_function_call (caller_name:string) (function_name:string) (args:P4.Argument.t list) : P4.Expression.t = 
  Info.dummy, P4.Expression.FunctionCall {
    func = (Info.dummy,P4.Expression.ExpressionMember {
        expr = Info.dummy, P4.Expression.Name (P4.BareName (Info.dummy, caller_name));
        name = Info.dummy, function_name});
    type_args = [];
    args = args}

let create_expression_expression_member (expr:P4.Expression.t) (name:string) : P4.Expression.t = 
  Info.dummy, P4.Expression.ExpressionMember {
    expr = expr;
    name = Info.dummy, name}

let create_expression_nameless_instantiation (types:P4.Type.t) (args:P4.Argument.t list) = 
  Info.dummy, P4.Expression.NamelessInstantiation {
    typ = types;
    args = args}
(** Create expression types *)

(** Create parser types *)
let create_parser_case (matches:P4.Match.t list) (next:string) : P4.Parser.case = let open P4.Parser in
  Info.dummy, {
    matches = matches;
    next = Info.dummy, next}

let create_parser_transition_select (exprs:P4.Expression.t list) (cases:P4.Parser.case list) : P4.Parser.transition = 
  let open P4.Parser in 
  Info.dummy, Select {
    exprs = exprs;
    cases = cases}

let create_parser_transition_accept : P4.Parser.transition = let open P4.Parser in 
  Info.dummy, Direct {next = Info.dummy, "accept"}

let create_parser_transition_reject : P4.Parser.transition = let open P4.Parser in 
  Info.dummy, Direct {next = Info.dummy, "reject"}

let create_parser_state (state_name:string) (statements:P4.Statement.t list) (transitions:P4.Parser.transition): P4.Parser.state =
  let open P4.Parser in 
  (Info.dummy, { annotations = [];
                 name = Info.dummy, state_name;
                 statements = statements;
                 transition =  transitions})
(** Create parser states *)

(** Create declarations types *)
let create_declaration_parser (parser_name) (parameters:P4.Parameter.t list) (locals:P4.Declaration.t list) 
    (states:P4.Parser.state list): (P4.Declaration.t) = 
  (Info.dummy, P4.Declaration.Parser {
      annotations = [];
      name = Info.dummy, parser_name;
      type_params = [];
      params = parameters;
      constructor_params = [];
      locals = locals;
      states = states;
    })

let create_declaration_control (control_name) (parameters:P4.Parameter.t list) 
    (locals:P4.Declaration.t list) (apply:P4.Block.t): (P4.Declaration.t) = 
  (Info.dummy, P4.Declaration.Control {
      annotations = [];
      name = Info.dummy, control_name;
      type_params = [];
      params = parameters;
      constructor_params = [];
      locals = locals;
      apply = apply;
    })

(**parser_name could also be controlname. I just picked one *)
let create_declaration_instantiation (parser_name : string) (local_name : string) (args:P4.Argument.t list): P4.Declaration.t = 
  (Info.dummy, P4.Declaration.Instantiation {
      annotations = [];
      typ = create_type_typename local_name;
      args = args;
      name = Info.dummy, parser_name;
      init = None })
(** Create declarations types *)

let params_from_parser (d:P4.Declaration.t) : P4.Parameter.t list option = match (snd d) with
  | P4.Declaration.Parser {annotations; name; type_params; params; constructor_params; locals; states} -> Some params
  | _ -> None

let param_to_arg (p:P4.Parameter.t) : P4.Argument.t = 
  Info.dummy, P4.Argument.Expression {
    value =  create_expression_name (get_parameter_name p)
  }

(** Merging functions *)
let merge_block (b1 : P4.Block.t) (b2 : P4.Block.t) : P4.Block.t = 
  let open P4.Block in
  (fst b1, { annotations = (snd b1).annotations @ (snd b2).annotations;
             statements = (snd b1).statements @ (snd b2).statements })

let merge_deparser (d1 : P4.Declaration.t) (d2: P4.Declaration.t) : P4.Declaration.t = 
  let dp1 = control_info d1 in 
  let dp2 = control_info d2 in 
  ((fst d1), Control { annotations = dp1.annotations;
                       name = Info.dummy, "NewDeparser";
                       type_params = dp1.type_params;
                       params = dp1.params; (**might need to check for difference *)
                       constructor_params = dp1.constructor_params;
                       locals = dp1.locals @ dp2.locals;
                       apply = merge_block dp1.apply dp2.apply})

(**Creating new up4 parser *)
let imt_in_port_expr : (P4.Expression.t) = create_expression_function_call "im" "get_in_port" []

let low_case_match (split_port:int) : P4.Parser.case = 
  let low_range = (create_expression_range 0 split_port) |> create_match in 
  create_parser_case [low_range] "low_ports_state"

let high_case_match (split_port:int) : P4.Parser.case = 
  let high_range = (create_expression_range split_port 65353) |> create_match in 
  create_parser_case [high_range] "high_ports_state"

let new_start_state (split_port:int) : P4.Parser.state = 
  let transitions = create_parser_transition_select [imt_in_port_expr] [low_case_match split_port; high_case_match split_port] in
  create_parser_state "start" [] transitions

let low_ports_state (parser_name:string) (args:P4.Argument.t list) : P4.Parser.state = 
  let low_port_parser_call = create_statement_function_call parser_name "apply" args in 
  create_parser_state "low_ports_state" [low_port_parser_call] create_parser_transition_accept

let high_ports_state (parser_name:string) (args:P4.Argument.t list) : P4.Parser.state = 
  let high_port_parser_call = create_statement_function_call parser_name "apply" args in 
  create_parser_state "high_ports_state" [high_port_parser_call] create_parser_transition_accept

let new_parser (params:P4.Parameter.t list) (parser1:string) (parser2:string) (split_port:int) : P4.Declaration.t = 
  let locals = (create_declaration_instantiation parser2 "parser2" [])::(create_declaration_instantiation parser1 "parser1" [])::[] in 
  let args = List.map param_to_arg params in
  let states = (low_ports_state parser1 args)::(high_ports_state parser2 args)::(new_start_state split_port)::[] in
  create_declaration_parser "NewParser" params locals states

(** Creating new up4 control *)
let merged_if_statement (args:P4.Argument.t list) (split_port:int) : P4.Statement.t = 
  let conditional = create_expression_binary_op (Info.dummy, P4.Op.Le) imt_in_port_expr (create_expression_int split_port) in
  let call_control1 = create_statement_function_call "control1" "apply" args in 
  let call_control2 = create_statement_function_call "control2" "apply" args in 
  create_statement_if (snd conditional) (snd call_control1) (snd call_control2)

let new_control (params:P4.Parameter.t list) (control1:string) (control2:string) (split_port:int) : P4.Declaration.t = 
  let locals = (create_declaration_instantiation control2 "control2" [])::(create_declaration_instantiation control1 "control1" [])::[] in 
  let args = List.map param_to_arg params in 
  let apply = create_block [merged_if_statement args split_port]  in 
  create_declaration_control "NewControl" params locals apply 


(** Checks length of list is 3 *)
let verify_main (l:'a list) : 'a list = if List.length l <> 3 
  then raise MissingDeclaration else l


(** This assumes program1 and program2 have the same argument in their parser.
    names1 is [parser_name, control_name, deparser_name], a string list
    package1 is [parser, control, deparser], a declaration.t list *)
let prog_merge (program1 : P4.program) (program2 : P4.program) (split_port : int) : P4.program = 
  let prog1 = program_to_declarations program1 in 
  let prog2 = program_to_declarations program2 in 
  let names1 = get_main_args prog1 in 
  let names2 = get_main_args prog2 in 
  let package1 = verify_main (find_declarations_by_names prog1 names1) in 
  let package2 = verify_main (find_declarations_by_names prog2 names2) in 
  let package_type = prog1 |> get_main |> declaration_name in 
  let parser_params = (List.hd package1) |> get_declaration_params |> get in
  let control_params = (List.nth package1 1) |> get_declaration_params in 
  let new_parser = new_parser parser_params (List.hd names1) (List.hd names2) split_port in
  let new_deparser = merge_deparser (List.nth package1 2) (List.nth package2 2) in
  let new_control = new_control (get control_params) (List.nth names1 1) (List.nth names2 1) split_port in 
  let package_arguments = List.map2 create_expression_nameless_instantiation (List.map create_type_typename ["NewParser"; "NewControl"; "NewDeparser"]) ([[];[];[]]) in 
  let new_package = create_declaration_instantiation "main" package_type (List.map create_argument_expression package_arguments) in 
  let merged_program = (remove_declarations prog1 [List.nth names1 2]) @ (remove_declarations prog2 [List.nth names2 2]) in
  P4.Program (new_parser::merged_program @ [new_control; new_deparser; new_package])