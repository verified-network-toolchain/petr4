exception IncorrectType of string
module P4 = Types

(** Record for temp control *)
type tempControl = { annotations: P4.Annotation.t list;
                     name: P4.P4String.t;
                     type_params: P4.P4String.t list;
                     params: P4.Parameter.t list;
                     constructor_params: P4.Parameter.t list;
                     locals: P4.Declaration.t list;
                     apply: P4.Block.t }

let get_control (d : P4.Declaration.t) : tempControl = match (snd d) with
  | P4.Declaration.Control { annotations; name; type_params; params; constructor_params; locals; apply } ->
    { annotations = annotations; 
      name = name; 
      type_params = type_params; 
      params = params; 
      constructor_params = constructor_params; 
      locals = locals; 
      apply = apply }
  | _ -> raise (IncorrectType "Control type expected")

let standard_meta : P4.Type.t = Info.M "Standard Meta", P4.Type.TypeName (P4.BareName (Info.M "Standard Meta", "standard_metadata_t"))

let standard_meta_param (info: Info.t) : P4.Parameter.t = let open P4.Parameter in 
  (info, { annotations = [];
           direction = Some (Info.M "Created param", P4.Direction.InOut);
           typ = standard_meta;
           variable = (Info.M "Created param", "standard_metadata");
           opt_value = None})

let if_BareName : P4.name = P4.BareName (Info.M "Created Condition", "condition")

let cond_if : P4.Statement.t =
  (Info.M "Created If", P4.Statement.Conditional {
      cond = Info.M "Created Condition", P4.Expression.Name (if_BareName);
      tru = Info.M "Created Return", P4.Statement.Return {expr = None};
      fls = None})

let add_cond_if (b1 : P4.Block.t) : P4.Block.t = let open P4.Block in 
  (fst b1, { annotations = (snd b1).annotations;
             statements = cond_if :: (snd b1).statements})

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

let match_declaration (d : P4.Declaration.t) (mainProg: bool) : (P4.Declaration.t option) = 
  match (snd d) with
  | Parser { annotations=a; name=n; type_params=tp; params=p; constructor_params=cp; locals=l; states=s} -> 
    Some ((fst d), P4.Declaration.Parser {
        annotations = a;
        name = n;
        type_params = tp;
        params = [standard_meta_param (p |> List.hd |> fst)];
        constructor_params = cp;
        locals = l;
        states = s
      })
  | P4.Declaration.Control { annotations=a; name=n; type_params=tp; params=p; constructor_params=cp; locals=l; apply=app} -> 
    if mainProg then Some ((fst d), P4.Declaration.Control {
        annotations = a;
        name = n;
        type_params = tp;
        params = [standard_meta_param (p |> List.hd |> fst)];
        constructor_params = cp;
        locals = l;
        apply = add_cond_if app }) else None
  | _ -> None

let prog_merge (prog1 : P4.program) (prog2 : P4.program) : P4.program = prog1