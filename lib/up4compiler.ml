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

let create_typename (t : string) : P4.Type.t = 
  Info.dummy, P4.Type.TypeName (P4.BareName (Info.dummy, t))

(** Finding main declaration names*)
let get_typename_name (t : P4.Type.t) : string = match (snd t) with 
  | TypeName typename -> P4.name_only typename
  | _ -> raise (IncorrectType "Expected TypeName")

let get_argument_name (i : P4.Argument.t) : string = match (snd i) with 
  | P4.Argument.Expression {value} -> (match (snd value) with 
      | P4.Expression.NamelessInstantiation {typ; args} -> get_typename_name typ
      | _ -> raise (IncorrectType "NamelessInstantiation expected"))
  | _ -> raise (IncorrectType "Argument Expression expected")

let args_from_instantiation (d : P4.Declaration.t) : P4.Argument.t list option = match (snd d) with 
  | P4.Declaration.Instantiation {annotations; typ; args; name; init} -> Some args
  | _ -> None

let main_args (prog : P4.Declaration.t list) : string list = 
  let main = (List.filter_map args_from_instantiation prog) in 
  if List.length main <> 1 then raise MultipleMains
  else List.map get_argument_name (List.hd main)
(** Finding main declaration names from package. 
    For up4, should return [parser_name, control_name, deparser_name] *)

let declaration_name (d : P4.Declaration.t) : string = snd (P4.Declaration.name d)

(**Can declarations have same name? (across all of controls, externs, parser, etc) *)
let find_declaration_by_name (prog:P4.Declaration.t list) (name:string) : P4.Declaration.t = 
  let declarations = List.filter (fun p -> declaration_name p == name) prog in 
  if List.length declarations == 0 then raise (DeclarationNotFound name)
  else List.hd declarations

let standard_meta : P4.Type.t = Info.M "Standard Meta", P4.Type.TypeName (P4.BareName (Info.M "Standard Meta", "standard_metadata_t"))

let standard_meta_param (info: Info.t) : P4.Parameter.t = let open P4.Parameter in 
  (info, { annotations = [];
           direction = Some (Info.dummy, P4.Direction.InOut);
           typ = standard_meta;
           variable = (Info.M "Created_standard_meta_param", "standard_metadata");
           opt_value = None})

let create_if (condition : P4.Expression.pre_t) (true_branch : P4.Statement.pre_t) (false_branch : P4.Statement.pre_t) : P4.Statement.t =
  (Info.M "Created If", P4.Statement.Conditional {
      cond = Info.M "Created Condition", condition; (**Binop on im_t.getinport *)
      tru = Info.M "Created true branch", true_branch;
      fls = Some (Info.M "Created false branch", false_branch)})

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

let create_locals (parser_name : string) (local_name : string) : P4.Declaration.t = 
  (Info.dummy, P4.Declaration.Instantiation {
      annotations = [];
      typ = create_typename local_name;
      args = [];
      name = Info.dummy, parser_name;
      init = None })

let merged_state : P4.Parser.state list = []

let create_parser (parser_name) (parameters:P4.Parameter.t list) (locals:P4.Declaration.t list) 
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

let create_control (control_name) (parameters:P4.Parameter.t list) 
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

let prog_merge (prog1 : P4.program) (prog2 : P4.program) : P4.program = prog1