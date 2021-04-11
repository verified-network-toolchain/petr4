exception IncorrectType of string
exception MultipleMains
exception DeclarationNotFound of string
exception DuplicateDeclarationName
exception MissingDeclaration
exception CompilerError
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

(** None is a hack that (I think) works, because declaration names won't be "" *)
let declaration_name (d : P4.Declaration.t) : string = match P4.Declaration.name_opt d with 
  | Some s -> snd s
  | None -> ""

let program_to_declarations (prog:P4.program) : P4.Declaration.t list = match prog with
  | Program decls -> decls 

let get_program_declaration_name (prog:P4.Declaration.t list) : string list = 
  List.filter (fun x -> compare x "" <> 0) (List.map declaration_name prog)

let get_error (d:P4.Declaration.t): P4.Declaration.t option = match (snd d) with 
  | P4.Declaration.Error{members} -> Some d
  | _ -> None

let get_P4int_value (i:P4.P4Int.t) : int = match (snd i) with 
  | {value;width_signed} -> get (Bigint.to_int value)

let get_matchkind (d:P4.Declaration.t): P4.Declaration.t option = match (snd d) with 
  | P4.Declaration.MatchKind{members} -> Some d
  | _ -> None

let get_error_members (err:P4.Declaration.t) : P4.P4String.t list = match (snd err) with 
  | P4.Declaration.Error {members} -> members
  | _ -> raise (IncorrectType "Expected Error")

let get_matchkind_members (err:P4.Declaration.t) : P4.P4String.t list = match (snd err) with 
  | P4.Declaration.MatchKind {members} -> members
  | _ -> raise (IncorrectType "Expected MatchKind")

let get_typename_name (t : P4.Type.t) : string = match (snd t) with 
  | TypeName typename -> P4.name_only typename
  | _ -> raise (IncorrectType "Expected TypeName")

let get_expression_print (e:P4.Expression.t):string = match (snd e) with 
  | Int i -> string_of_int (get_P4int_value i)
  | _ -> raise (IncorrectType "expression print not implemented yet")

(**Essentially pretty print for type *)
let get_type_print (t:P4.Type.t) : string = match (snd t) with
  | TypeName typename -> P4.name_only typename
  | HeaderStack {header;size} -> (get_typename_name header) ^ "[" ^ (get_expression_print size) ^ "]"
  | Error -> "error"
  | _ -> raise (IncorrectType "type not included yet")

let get_argument_name (a : P4.Argument.t) : string = match (snd a) with 
  | P4.Argument.Expression {value} -> (match (snd value) with 
      | P4.Expression.NamelessInstantiation {typ; args} -> get_typename_name typ
      | P4.Expression.Name n -> P4.name_only n
      | _ -> raise (IncorrectType "NamelessInstantiation expected"))
  | _ -> raise (IncorrectType "Argument Expression expected")

let get_argument_int (a : P4.Argument.t) : int = match (snd a) with
  |  P4.Argument.Expression {value} -> (match (snd value) with 
      | P4.Expression.Int i -> get_P4int_value i
      | _ -> raise (IncorrectType "Int expected"))
  | _ -> raise (IncorrectType "Argument Expression expected")

let get_parameter_type (p:P4.Parameter.t) : P4.Type.t = match (snd p) with 
  | {annotations; direction; typ; variable; opt_value} -> typ

let get_parameter_typename (p:P4.Parameter.t) : string = match (snd p) with 
  | {annotations; direction; typ; variable; opt_value} -> get_typename_name typ

let get_parameter_name (p : P4.Parameter.t) : string = match (snd p) with
  | {annotations; direction; typ; variable; opt_value} -> snd variable



let get_instantiation (prog:P4.Declaration.t) : P4.Declaration.t option = 
  match (snd prog) with 
  | P4.Declaration.Instantiation {annotations; typ; args; name; init} -> 
    Some (Info.dummy, P4.Declaration.Instantiation {annotations; typ; args; name; init})
  | _ -> None

let get_instantiation_args (d : P4.Declaration.t) : P4.Argument.t list option = 
  match (snd d) with 
  | P4.Declaration.Instantiation {annotations; typ; args; name; init} -> Some args
  | _ -> None

(** returns [errors], [matchkinds] *)
let get_unnamed_declarations (prog:P4.Declaration.t list) : P4.Declaration.t list * P4.Declaration.t list = 
  let unnamed = List.filter (fun d -> compare (declaration_name d) "" == 0) prog in 
  (List.filter_map get_error unnamed), (List.filter_map get_matchkind unnamed)

let get_declaration_type (p:P4.Declaration.t) : P4.Type.t option = 
  match (snd p) with 
  | P4.Declaration.Instantiation {annotations; typ; args; name; init} -> Some typ
  | _ -> None

let get_declaration_params (p:P4.Declaration.t) : P4.Parameter.t list option = 
  match (snd p) with
  | P4.Declaration.Parser {annotations; name; type_params; params; constructor_params; locals; states} -> Some params
  | P4.Declaration.Control {annotations; name; type_params; params; constructor_params; locals; apply} -> Some params
  | _ -> None

let get_declaration_fields (p:P4.Declaration.t) : P4.Declaration.field list option = 
  match (snd p) with
  | P4.Declaration.Header {annotations; name; fields} -> Some fields
  | P4.Declaration.HeaderUnion {annotations; name; fields} -> Some fields
  | P4.Declaration.Struct {annotations; name; fields} -> Some fields
  | _ -> None

let get_field_types (f:P4.Declaration.field) : P4.Type.t = match (snd f) with
  | {annotations; typ; name} -> typ

(**Can declarations have same name? (across all of controls, externs, parser, etc) *)
let find_declaration_by_name (prog:P4.Declaration.t list) (name:string) : P4.Declaration.t = 
  let declarations = List.filter (fun p -> compare (declaration_name p) name == 0) prog in 
  if List.length declarations == 0 then raise (DeclarationNotFound name)
  else List.hd declarations

let find_declarations_by_names (prog:P4.Declaration.t list) (names:string list) : P4.Declaration.t list = 
  List.filter (fun p -> List.mem (declaration_name p) names) prog

let remove_declaration (prog:P4.Declaration.t list) (to_remove_name:string) : P4.Declaration.t list = 
  List.filter (fun d -> declaration_name d <> to_remove_name) prog

let remove_declarations (prog:P4.Declaration.t list) (to_remove_names:string list) : P4.Declaration.t list = 
  List.filter (fun d -> not (List.mem (declaration_name d) to_remove_names)) prog

let remove_unnamed_decl (prog:P4.Declaration.t list) : P4.Declaration.t list = 
  List.filter (fun p -> compare (declaration_name p) "" <> 0) prog

let get_main (prog:P4.Declaration.t list) : P4.Declaration.t = 
  find_declaration_by_name prog "main"
(* let main = List.filter_map get_instantiation prog in 
   if List.length main == 0 then raise (DeclarationNotFound "main")
   else if List.length main <> 1 then raise MultipleMains
   else (List.hd main) *)

(** Finding main declaration names from package. 
    For up4, should return [package_name, parser_name, control_name, deparser_name] *)
let get_main_args (prog : P4.Declaration.t list) : P4.Argument.t list = 
  let main = find_declaration_by_name prog "main" in 
  main |> get_instantiation_args |> get 
(* (List.filter_map get_instantiation_args prog) in 
   let main =  in 
   if List.length main == 0 then raise (DeclarationNotFound "main")
   else if List.length main <> 1 then raise MultipleMains
   else (List.map get_argument_name (List.hd main)) *)

let p4strings_to_strings (lst:P4.P4String.t list) : string list = List.map snd lst

let strings_to_p4strings (lst:string list) : P4.P4String.t list = List.map (fun x -> Info.dummy, x) lst

let rec unique_strings (lst:string list) : string list = 
  match lst with 
  | [] -> []
  | hd::tl -> hd::unique_strings (List.filter (fun x -> x <> hd) tl)

(** Removes all but the first the declaration that matches [name] or does nothing 
    if there is no declaration with name of [name] *)
let unique_declarations_by_name (prog:P4.Declaration.t list) (name:string) : P4.Declaration.t list = 
  let rec finding_unique (rest_of_prog:P4.Declaration.t list) (name:string) (found_first:bool) = 
    if found_first then remove_declaration rest_of_prog name
    else if declaration_name (List.hd rest_of_prog) == name then (List.hd rest_of_prog)::finding_unique (List.tl rest_of_prog) name true
    else (List.hd rest_of_prog)::finding_unique (List.tl rest_of_prog) name false in 
  finding_unique prog name false


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
      cond = Info.M "Created Condition", condition;
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

let create_declaration_struct (struct_name : string) (fields : P4.Declaration.field list): P4.Declaration.t = 
  (Info.dummy, P4.Declaration.Struct {
      annotations = [];
      name = Info.dummy, struct_name;
      fields = fields
    })

let create_declaration_field (field_name : string) (type_name : string) : P4.Declaration.field = 
  let open P4.Declaration in 
  Info.dummy, {
    annotations = [];
    typ = create_type_typename type_name;
    name = Info.dummy, field_name;
  }
(** Create declarations types *)

let create_param (dir : P4.Direction.t option) (typ : string) (var : string) : P4.Parameter.t = 
  let open P4.Parameter in 
  Info.dummy, {
    annotations = [];
    direction = dir;
    typ = create_type_typename typ;
    variable = Info.dummy, var;
    opt_value = None
  }

let params_from_parser (d:P4.Declaration.t) : P4.Parameter.t list option = match (snd d) with
  | P4.Declaration.Parser {annotations; name; type_params; params; constructor_params; locals; states} -> Some params
  | _ -> None

let param_to_arg (p:P4.Parameter.t) : P4.Argument.t = 
  Info.dummy, P4.Argument.Expression {
    value =  create_expression_name (get_parameter_name p)
  }

(** Replacing functions *)
let replace_param_type (p:P4.Parameter.t) (new_type:string) : P4.Parameter.t = 
  let open P4.Parameter in 
  match (snd p) with | {annotations; direction; typ; variable; opt_value} ->
    Info.dummy, {
      annotations = annotations;
      direction = direction;
      typ = create_type_typename new_type;
      variable = variable;
      opt_value = opt_value}
(** Replacing functions *)

(** Merging functions *)
let merge_block (b1 : P4.Block.t) (b2 : P4.Block.t) : P4.Block.t = 
  let open P4.Block in
  (fst b1, { annotations = (snd b1).annotations @ (snd b2).annotations;
             statements = (snd b1).statements @ (snd b2).statements })

let merge_error (e1:P4.Declaration.t) (e2:P4.Declaration.t) : P4.Declaration.t = 
  Info.dummy, P4.Declaration.Error 
    {members =((e1 |> get_error_members |> p4strings_to_strings) @ (e2 |> get_error_members |> p4strings_to_strings))
              |> unique_strings |> strings_to_p4strings}

let merge_matchkind (m1:P4.Declaration.t) (m2:P4.Declaration.t) : P4.Declaration.t = 
  Info.dummy, P4.Declaration.MatchKind 
    {members =((m1 |> get_matchkind_members |> p4strings_to_strings) @ (m2 |> get_matchkind_members |> p4strings_to_strings))
              |> unique_strings |> strings_to_p4strings}

let merge_unnamed_declaration (d1:P4.Declaration.t) (d2:P4.Declaration.t) : P4.Declaration.t= 
  match (snd d1), (snd d2) with
  | P4.Declaration.Error{members=m1}, P4.Declaration.Error{members=m2} -> merge_error d1 d2
  | P4.Declaration.MatchKind{members=m1}, P4.Declaration.MatchKind{members=m2} -> merge_matchkind d1 d2
  | _ -> raise (IncorrectType "Expected both errors or both matchkinds")

(** Make sure d1 and d2 length should be != 0 *)
let merge_unnamed_declarations (d1:P4.Declaration.t list) (d2:P4.Declaration.t list) : P4.Declaration.t = 
  if List.length d1 == 0 && List.length d2 == 0 then raise (IncorrectType "SD")
  else if List.length d1 == 0 then List.fold_left merge_unnamed_declaration (List.hd d2) d2
  else if List.length d2 == 0 then List.fold_left merge_unnamed_declaration (List.hd d1) d1
  else List.fold_left merge_unnamed_declaration (List.hd d1) (List.tl d1 @ d2)

let merge_deparser (header_type:string) (header_name:string) (d1 : P4.Declaration.t) (d2: P4.Declaration.t): P4.Declaration.t = 
  let dp1 = control_info d1 in 
  let dp2 = control_info d2 in 
  let params = [create_param None "packet_out" "packet"; create_param (Some (Info.dummy, P4.Direction.In)) header_type header_name ] in 
  ((fst d1), Control { annotations = [];
                       name = Info.dummy, "NewDeparser";
                       type_params = [];
                       params = params; (*might need to check for difference *)
                       constructor_params = [];
                       locals = [];
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
  let transitions = create_parser_transition_select [imt_in_port_expr] [low_case_match split_port; high_case_match (split_port+1)] in
  create_parser_state "start" [] transitions

let low_ports_state (parser_name:string) (args:P4.Argument.t list) : P4.Parser.state = 
  let low_port_parser_call = create_statement_function_call parser_name "apply" args in 
  create_parser_state "low_ports_state" [low_port_parser_call] create_parser_transition_accept

let high_ports_state (parser_name:string) (args:P4.Argument.t list) : P4.Parser.state = 
  let high_port_parser_call = create_statement_function_call parser_name "apply" args in 
  create_parser_state "high_ports_state" [high_port_parser_call] create_parser_transition_accept

(** declaration_types is the types for the two parser params or the types for the two deparsers*)
let new_struct_merge (declaration_types:string list * string list) (structs_names:string list): P4.Declaration.t list = 
  if List.length (fst declaration_types) <> List.length (snd declaration_types) 
  || List.length (fst declaration_types) <> List.length structs_names then raise CompilerError else
    let structs_types = List.map2 (fun x y -> [x; y]) (fst declaration_types) (snd declaration_types) in 
    let new_fields = (List.map2 (fun field_names struct_name -> [create_declaration_field (struct_name ^ "1") ((List.nth field_names 0)); create_declaration_field (struct_name ^ "2") ((List.nth field_names 1))]) ) structs_types structs_names in 
    List.map2 (fun fields struct_name -> create_declaration_struct struct_name fields) new_fields structs_names

let new_parser (param_typenames:string list) (param_names:string list) (parser1:string) (parser2:string) (split_port:int) : P4.Declaration.t = 
  let locals = (create_declaration_instantiation "parser2" parser2 [])::(create_declaration_instantiation "parser1" parser1 [])::[] in 
  let packet_param = create_param None "packet_in" "packet" in 
  let im_t_param = create_param None "im_t" "im" in 
  let dirs = [Some (Info.dummy, P4.Direction.Out);Some (Info.dummy, P4.Direction.InOut);Some (Info.dummy, P4.Direction.In);Some (Info.dummy, P4.Direction.InOut)] in
  let param_temp = List.map2 (fun func name -> func name) (List.map2 (fun dir typ_name -> create_param dir typ_name) dirs param_typenames) param_names in 
  let params = [packet_param; im_t_param] @ param_temp in 
  let args1_temp = List.map2 (fun struct_name name -> create_expression_expression_member (create_expression_name struct_name) name) param_names (List.map (fun x -> x ^ "1") param_typenames) in 
  let args1 = [param_to_arg packet_param; param_to_arg im_t_param] @ (List.map create_argument_expression args1_temp) in 
  let args2_temp = List.map2 (fun struct_name name -> create_expression_expression_member (create_expression_name struct_name) name) param_names (List.map (fun x -> x ^ "2") param_typenames) in 
  let args2 = [param_to_arg packet_param; param_to_arg im_t_param] @ (List.map create_argument_expression args2_temp) in 
  let states = (low_ports_state parser1 args1)::(high_ports_state parser2 args2)::(new_start_state split_port)::[] in
  create_declaration_parser "NewParser" params locals states

(** Creating new up4 control *)
let merged_if_statement (args1:P4.Argument.t list) (args2:P4.Argument.t list) (split_port:int) : P4.Statement.t = 
  let conditional = create_expression_binary_op (Info.dummy, P4.Op.Le) imt_in_port_expr (create_expression_int split_port) in
  let call_control1 = create_statement_function_call "control1" "apply" args1 in 
  let call_control2 = create_statement_function_call "control2" "apply" args2 in 
  create_statement_if (snd conditional) (snd call_control1) (snd call_control2)

let new_control (param_typenames:string list) (param_names:string list) (control1:string) (control2:string) (split_port:int) : P4.Declaration.t = 
  let locals = (create_declaration_instantiation "control2" control2  [])::(create_declaration_instantiation "control1" control1 [])::[] in 
  let im_t_param = create_param None "im_t" "im" in 
  let dirs = [Some (Info.dummy, P4.Direction.InOut);Some (Info.dummy, P4.Direction.InOut);Some (Info.dummy, P4.Direction.In);Some (Info.dummy, P4.Direction.Out);Some (Info.dummy, P4.Direction.InOut)] in
  let param_temp = List.map2 (fun func name -> func name) (List.map2 (fun dir typ_name -> create_param dir typ_name) dirs param_typenames) param_names in 
  let params = [im_t_param] @ param_temp in
  let args1_temp = List.map2 (fun struct_name name -> create_expression_expression_member (create_expression_name struct_name) name) param_names (List.map (fun x -> x ^ "1") param_typenames) in 
  let args1 = [param_to_arg im_t_param] @ (List.map create_argument_expression args1_temp) in 
  let args2_temp = List.map2 (fun struct_name name -> create_expression_expression_member (create_expression_name struct_name) name) param_names (List.map (fun x -> x ^ "2") param_typenames) in 
  let args2 = [param_to_arg im_t_param] @ (List.map create_argument_expression args2_temp) in 
  let apply = create_block [merged_if_statement args1 args2 split_port]  in 
  create_declaration_control "NewControl" params locals apply 


(** Checks length of list is 3 *)
let verify_length (l:'a list) (length:int) : 'a list = if List.length l <> length
  then raise MissingDeclaration else l

(** This assumes program1 and program2 have the same argument in their parser.
    names1 is [parser_name, control_name, deparser_name], a string list
    package1 is [parser, control, deparser], a declaration.t list *)
let prog_merge_package (program : P4.program) : P4.program = 
  let prog = program_to_declarations program in 
  let main_args = get_main_args prog in 
  let names = List.map get_argument_name [(List.nth main_args 0); (List.nth main_args 1)] in 
  let names1 = find_declaration_by_name prog (List.nth names 0) |> get_instantiation_args |> get |> List.map get_argument_name in 
  let names2 = find_declaration_by_name prog (List.nth names 1) |> get_instantiation_args |> get |> List.map get_argument_name in 
  let split_port = get_argument_int (List.nth main_args 2) in 
  let package1 = verify_length (find_declarations_by_names prog names1) 3 in 
  let package2 = verify_length (find_declarations_by_names prog names2) 3 in 
  (* let parser1_params = (List.hd package1) |> get_declaration_params |> get in
     let parser2_params = (List.hd package2) |> get_declaration_params |> get in  *)
  let control1_params = (List.nth package1 1) |> get_declaration_params |> get in
  let control2_params = (List.nth package2 1) |> get_declaration_params |> get in  
  let unnamed_decs = (get_unnamed_declarations prog) in 
  let merged_unnamed_decs = [merge_unnamed_declarations (unnamed_decs |> fst) []; merge_unnamed_declarations (unnamed_decs |> snd) []] in 
  let control_param_type = List.tl (List.map get_parameter_type control1_params), List.tl (List.map get_parameter_type control2_params) in 
  let control_param_names = List.map get_type_print (fst control_param_type), List.map get_type_print (snd control_param_type) in 
  (* let new_parser_structs = new_struct_merge parser_type_params ["parserHdr"; "parserMeta"; "parserInParam"; "parserInOutParam"] in *)
  let new_parser_typename = ["mergedHdr"; "mergedMeta"; "mergedInParam"; "mergedInOutParam"] in 
  let new_control_typename = ["mergedHdr"; "mergedMeta"; "mergedInParam"; "mergedOutParam"; "mergedInOutParam"] in 
  (*print_string "\n\n"; ignore (List.map (fun s -> print_string (s ^ " ")) (fst control_param_names)); print_string "\n";
    print_string "\n\n"; ignore (List.map (fun s -> print_string (s ^ " ")) (snd control_param_names)); print_string "\n\n"; *)
  let new_control_structs = new_struct_merge control_param_names ["mergedHdr"; "mergedMeta"; "mergedInParam"; "mergedOutParam"; "mergedInOutParam"] in 
  let new_parser = new_parser (new_parser_typename) (["hdrs"; "meta"; "in_param"; "inout_param"]) (List.hd names1) (List.hd names2) split_port in
  let new_deparser = merge_deparser "mergedHdr" "hdr" (List.nth package1 2) (List.nth package2 2) in
  let new_control = new_control (new_control_typename) (["hdrs";"meta";"in_param";"out_param";"inout_param"]) (List.nth names1 1) (List.nth names2 1) split_port in 
  let package_arguments = List.map2 create_expression_nameless_instantiation (List.map create_type_typename ["NewParser"; "NewControl"; "NewDeparser"]) ([[];[];[]]) in 
  let new_package = create_declaration_instantiation "main" "uP4Switch" (List.map create_argument_expression package_arguments) in 
  let final_prog = remove_unnamed_decl (remove_declaration prog (prog |> get_main |> declaration_name)) in 
  P4.Program (merged_unnamed_decs @ final_prog @ new_control_structs @ [new_parser; new_control; new_deparser; new_package]) 
