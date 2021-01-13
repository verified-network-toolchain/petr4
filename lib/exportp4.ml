open Typed
open Prog
open Format

let print_bool p b =
  match b with
  | true ->
      fprintf p "true"
  | false ->
      fprintf p "false"

let print_string p s =
  fprintf p "%s" s

let print_pair f1 f2 p (a, b) =
  fprintf p "(%a, %a)" f1 a f2 b

let print_option f p a =
  match a with
  | Some a -> () (* failwith "unimplemented" *)
  | None -> () (* failwith "unimplemented" *)

let rec print_list_aux f p l =
  match l with
  | [] -> ()
  | hd :: tl ->
      fprintf p ";@ %a%a" f hd (print_list_aux f) tl

let print_list f p l =
  match l with
  | [] -> fprintf p "nil"
  | hd :: tl ->
      fprintf p "@[<hov 1>[%a%a]@]" f hd (print_list_aux f) tl

let print_nat p n =
  ()
  (* failwith "unimplemented" *)

(* print_info prints a unit now, because we do not have info in Coq in this version. *)
let print_info p info =
  fprintf p "tt"

let p4string p (s : Info.t Poulet4.P4String.t) =
  fprintf p "{| @[<hov 0>tags := %a;@ str := \"%s\" |}@]" print_info s.tags s.str

let p4strings =
  print_list p4string

let print_direction p dir =
  ()
  (* failwith "unimplemented" *)

let print_name p (name : Info.t Poulet4.Typed.name) =
  match name with
  | BareName s ->
      fprintf p "@[<hov 4>(BareName %a)@]"
          p4string s
  | _ -> failwith "unimplemented"

let print_type p (typ : coq_P4Type) =
  match typ with
  | TypTypeName name ->
      fprintf p "@[<hov 4>(TypTypeName %a)@]"
          print_name name
  | _ -> ()
  (* failwith "unimplemented" *)

let print_stmt_type p (typ : coq_StmType) =
  match typ with
  | _ -> ()
  (* failwith "unimplemented" *)

let rec print_expr p (expr : coq_Expression) =
  match expr with
  | MkExpression (info, pre_expr, typ, dir) ->
      fprintf p "(@[<hov 4>(MkExpression %a@ %a@ %a@ %a)@]"
          print_info info
          print_pre_expr pre_expr
          print_type typ
          print_direction dir

and print_pre_expr p (pre_expr : coq_ExpressionPreT) =
  match pre_expr with
  | ExpName name ->
      fprintf p "(ExpName %a)"
          print_name name
  | ExpNamelessInstantiation (typ, args) ->
      fprintf p "(ExpNamelessInstantiation %a@ %a)"
          print_type typ
          (print_list print_expr) args
  | _ -> ()
  (* failwith "unimplemented" *)

let print_exprs =
  print_list print_expr

let rec print_stmt p (stmt : coq_Statement) =
  match stmt with
  | MkStatement (info, pre_stmt, typ) ->
      fprintf p "(MkStatement %a@ %a@ %a)"
          print_info info
          print_pre_stmt pre_stmt
          print_stmt_type typ

and print_pre_stmt p pre_stmt =
  match pre_stmt with
  | StatMethodCall (func, type_args, args) ->
      fprintf p "(StatMethodCall %a@ %a@ %a)"
          print_expr func
          (print_list print_type) type_args
          (print_list (print_option print_expr)) args
  | _ -> ()
  (* failwith "unimplemented" *)

and print_block p (block : coq_Block) =
  match block with
  | BlockEmpty info ->
      fprintf p "(BlockEmpty %a)" print_info info
  | BlockCons (stmt, block) ->
      fprintf p "(BlockCons %a@ %a)"
          print_stmt stmt
          print_block block

let print_param p param =
  match param with
  (* | (info, Poulet4.Typed.MkParameter (opt, direction, typ, default_arg_id, variable)) -> *)
  | Poulet4.Typed.MkParameter (opt, direction, typ, default_arg_id, variable) ->
      fprintf p "@[<hov 4>(MkParameter %a@ %a@ %a@ %a@ %a)@]"
          print_bool opt
          print_direction direction
          print_type typ
          (print_option print_nat) default_arg_id
          p4string variable
  (* failwith "unimplemented" *)

let print_params =
  print_list print_param

let print_state p state =
  ()
  (* failwith "unimplemented" *)

let print_states =
  print_list print_state

let print_decl_field p (decl_field : coq_DeclarationField) =
  match decl_field with
  | MkDeclarationField (info, typ, name) ->
      fprintf p "@[<hov 4>(MkDeclarationField %a@ %a@ %a)@]"
          print_info info
          print_type typ
          p4string name

let print_decl p (decl : coq_Declaration) =
  match decl with
  | DeclAction (info, name, data_params, ctrl_params, body) ->
      fprintf p "(DeclAction %a@ %a@ %a@ %a@ %a)"
          print_info info
          p4string name
          print_params data_params
          print_params ctrl_params
          print_block body
  | _ -> ()
  (* failwith "unimplemented" *)

let print_decls =
  print_list print_decl

let get_decl_name =
  let cnt = ref 0 in
  fun () ->
    cnt := !cnt + 1;
    "decl" ^ string_of_int !cnt

let print_global_decl p (decl : coq_Declaration) : string =
  let print_dummy_decl p () =
    let decl_name = get_decl_name () in
    fprintf p "Axiom %s : Declaration unit.@ @ " decl_name;
    decl_name
  in
  match decl with
  | DeclInstantiation (info, typ, args, name, init) ->
      let decl_name = name.str in
      fprintf p "@[<hov 4>Definition %s := DeclInstantiation %a@ %a@ %a@ %a@ %a.@]@ @ "
          decl_name
          print_info info
          print_type typ
          print_exprs args
          p4string name
          (print_option print_block) init;
      decl_name
  | DeclParser (info, name, type_params, params, constructor_params, locals, states) ->
      let decl_name = name.str in
      fprintf p "@[<hov 4>Definition %s := DeclParser %a@ %a@ %a@ %a@ %a@ %a@ %a.@]@ @ "
          decl_name
          print_info info
          p4string name
          p4strings type_params
          print_params params
          print_params constructor_params
          print_decls locals
          print_states states;
      decl_name
  | DeclControl (info, name, type_params, params, constructor_params, locals, apply) ->
      let decl_name = name.str in
      fprintf p "@[<hov 4>Definition %s := DeclControl %a@ %a@ %a@ %a@ %a@ %a@ %a.@]@ @ "
          decl_name
          print_info info
          p4string name
          p4strings type_params
          print_params params
          print_params constructor_params
          print_decls locals
          print_block apply;
      decl_name
  | DeclStruct (info, name, fields) ->
      let decl_name = name.str in
      fprintf p "@[<hov 4>Definition %s := DeclStruct %a@ %a@ %a.@]@ @ "
          decl_name
          print_info info
          p4string name
          (print_list print_decl_field) fields;
      decl_name
  | DeclError (info, decls) ->
      let decl_name = get_decl_name () in
      fprintf p "@[<hov 4>Definition %s := %a.@]@ @ " decl_name p4strings decls;
      decl_name
  | _ -> print_dummy_decl p ()

let print_program p (program : Prog.program) =
  fprintf p "@[<v 0>";
  let decl_names = List.map (print_global_decl p) program in
  fprintf p "Definition program := %a."
    (print_list print_string) decl_names;
  fprintf p "@]@."