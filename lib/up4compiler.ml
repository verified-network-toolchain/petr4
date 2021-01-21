exception IncorrectType of string
module P4 = Types

let prog_merge (prog1 : P4.program) (prog2 : P4.program) : P4.program = prog1

let parser_merge (p1 : P4.Declaration.t) (p2 : P4.Declaration.t) : P4.Declaration.t = p1



(** Record for temp control *)
type tempControl = { annotations: P4.Annotation.t list;
                     name: P4.P4String.t;
                     type_params: P4.P4String.t list;
                     params: P4.Parameter.t list;
                     constructor_params: P4.Parameter.t list;
                     locals: P4.Declaration.t list;
                     apply: P4.Block.t }

let get_control (d : P4.Declaration.t) : tempControl = match (snd d) with
  | Control { annotations; name; type_params; params; constructor_params; locals; apply } ->
    { annotations = annotations; 
      name = name; 
      type_params = type_params; 
      params = params; 
      constructor_params = constructor_params; 
      locals = locals; 
      apply = apply }
  | _ -> raise (IncorrectType "Control type expected in deparser_merge")

let block_merge (b1 : P4.Block.t) (b2 : P4.Block.t) : P4.Block.t = 
  let open P4.Block in
  (fst b1, { annotations = (snd b1).annotations @ (snd b2).annotations;
             statements = (snd b1).statements @ (snd b2).statements })

let deparser_merge (d1 : P4.Declaration.t) (d2: P4.Declaration.t) : P4.Declaration.t = 
  let dp1 = get_control d1 in 
  let dp2 = get_control d2 in 
  ((fst d1), Control { annotations = dp1.annotations;
                       name = dp1.name;
                       type_params = dp1.type_params;
                       params = dp1.params;
                       constructor_params = dp1.constructor_params;
                       locals = dp1.locals @ dp2.locals;
                       apply = block_merge dp1.apply dp2.apply})

