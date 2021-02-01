exception IncorrectType of string
exception MultipleMains
exception DeclarationNotFound of string
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

let args_from_instantiation (d : P4.Declaration.t) : P4.Argument.t list option = match (snd d) with 
  | P4.Declaration.Instantiation {annotations; typ; args; name; init} -> Some args
  | _ -> None

(** Finding main declaration names from package. 
    For up4, should return [parser_name, control_name, deparser_name] *)
let main_args (prog : P4.Declaration.t list) : string list = 
  let main = (List.filter_map args_from_instantiation prog) in 
  if List.length main <> 1 then raise MultipleMains
  else List.map get_argument_name (List.hd main)

let declaration_name (d : P4.Declaration.t) : string = snd (P4.Declaration.name d)

(**Can declarations have same name? (across all of controls, externs, parser, etc) *)
let find_declaration_by_name (prog:P4.Declaration.t list) (name:string) : P4.Declaration.t = 
  let declarations = List.filter (fun p -> declaration_name p == name) prog in 
  if List.length declarations == 0 then raise (DeclarationNotFound name)
  else List.hd declarations

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
    width_signed = None
  }

let create_match (expr:P4.Expression.t) : P4.Match.t = 
  Info.dummy, P4.Match.Expression {expr = expr}

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

let create_statement_function_call (caller_name:string) (function_name:string) (args:P4.Argument.t list) : P4.Statement.t = 
  Info.dummy, P4.Statement.MethodCall {
    func = (Info.dummy,P4.Expression.ExpressionMember {
        expr = Info.dummy, P4.Expression.Name (P4.BareName (Info.dummy, caller_name));
        name = Info.dummy, function_name});
    type_args = [];
    args = args}
(** Create statement types *)

(** Create expression types *)
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

let create_declaration_instantiation (parser_name : string) (local_name : string) : P4.Declaration.t = 
  (Info.dummy, P4.Declaration.Instantiation {
      annotations = [];
      typ = create_type_typename local_name;
      args = [];
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
let block_merge (b1 : P4.Block.t) (b2 : P4.Block.t) : P4.Block.t = 
  let open P4.Block in
  (fst b1, { annotations = (snd b1).annotations @ (snd b2).annotations;
             statements = (snd b1).statements @ (snd b2).statements })

let deparser_merge (d1 : P4.Declaration.t) (d2: P4.Declaration.t) : P4.Declaration.t = 
  let dp1 = control_info d1 in 
  let dp2 = control_info d2 in 
  ((fst d1), Control { annotations = dp1.annotations;
                       name = dp1.name;
                       type_params = dp1.type_params;
                       params = dp1.params; (**might need to check for difference *)
                       constructor_params = dp1.constructor_params;
                       locals = dp1.locals @ dp2.locals;
                       apply = block_merge dp1.apply dp2.apply})

(* let create_match_range (low:int) (high:int) : P4.Match.t = 
   P4.Match.Expression {
   expr = 
   } *)

(**Creating new up4 parser *)
(** used in transition select exprs - create_parser_transition [imt_in_port_expr] *)
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

(* let up4_new_parser (params:P4.Parameter.t list) : P4.Declaration.t = 
   let parser_locals = create:: [] *)


let prog_merge (prog1 : P4.program) (prog2 : P4.program) (split_port : int) : P4.program = prog1