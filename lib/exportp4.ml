open Typed
open Prog
open Format

let print_bool p b =
  let s = 
    match b with
    | true -> "true"
    | false -> "false"
  in fprintf p "%s" s

let print_string p s =
  fprintf p "%s" s

let print_pair f1 f2 p (a, b) =
  fprintf p "(%a, %a)" f1 a f2 b

let print_option f p a =
  match a with
  | Some a -> fprintf p "@[<hov 4>(Some@ %a)@]" f a
  | None -> fprintf p "@[<hov 4>None@]"

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
  fprintf p "%d" n

(* print_info prints a unit now, because we do not have info in Coq in this version. *)
let print_info p info =
  fprintf p "tt"

let p4string p (s : Info.t Poulet4.P4String.t) =
  fprintf p "{| @[<hov 0>tags := %a;@ str := \"%s\" |}@]" print_info s.tags s.str

let p4strings =
  print_list p4string

let print_direction p dir =
  let s = 
    match dir with
    | In -> "In" 
    | Out -> "Out"
    | InOut -> "InOut"
    | Directionless -> "Directionless"
  in fprintf p "%s" s

let print_name p (name : Info.t Poulet4.Typed.name) =
  match name with
  | BareName s ->
      fprintf p "@[<hov 4>(BareName %a)@]"
          p4string s
  | QualifiedName (namespaces, s) -> failwith "QualifiedName unimplemented in print_name"

let print_function_kind p func_kind =
  let s = 
    match func_kind with
    | FunParser -> "FunParser"
    | FunControl -> "FunControl"
    | FunExtern -> "FunExtern"
    | FunTable -> "FunTable"
    | FunAction -> "FunAction"
    | FunFunction -> "FunFunction"
    | FunBuiltin -> "FunBuiltin"
  in fprintf p "%s" s

let rec print_type p (typ : coq_P4Type) =
  match typ with
  | TypBool -> 
      fprintf p "@[<hov 0>(TypBool)@]"
  | TypString ->
      fprintf p "@[<hov 0>(TypString)@]"
  | TypInteger ->
      fprintf p "@[<hov 0>(TypInteger)@]"
  | TypInt n ->
      fprintf p "@[<hov 0>(TypInt@ %a)@]"
          print_nat n
  | TypBit n ->
      fprintf p "@[<hov 0>(TypBit@ %a)@]"
          print_nat n
  | TypVarBit n ->
      fprintf p "@[<hov 0>(TypVarBit@ %a)@]"
          print_nat n
  | TypArray (typ, n) ->
      fprintf p "@[<hov 0>(TypArray@ %a@ %a)@]"
          print_type typ
          print_nat n
  | TypTuple typs ->
      fprintf p "@[<hov 0>(TypTuple@ %a)@]"
          (print_list print_type) typs
  | TypList typs ->
      fprintf p "@[<hov 0>(TypList@ %a)@]"
          (print_list print_type) typs
  | TypRecord fields ->
      fprintf p "@[<hov 0>(TypRecord@ %a)@]"
          (print_list print_field_type) fields
  | TypSet typ ->
      fprintf p "@[<hov 0>(TypSet@ %a)@]"
          print_type typ
  | TypError ->
      fprintf p "@[<hov 0>(TypError)@]"
  | TypMatchKind ->
      fprintf p "@[<hov 0>(TypMatchKind)@]"
  | TypVoid ->
      fprintf p "@[<hov 0>(TypVoid)@]"
  | TypHeader fields ->
      fprintf p "@[<hov 0>(TypHeader@ %a)@]"
          (print_list print_field_type) fields
  | TypHeaderUnion fields ->
      fprintf p "@[<hov 0>(TypHeaderUnion@ %a)@]"
          (print_list print_field_type) fields
  | TypStruct fields ->
      fprintf p "@[<hov 0>(TypStruct@ %a)@]"
          (print_list print_field_type) fields
  | TypEnum (s, typ, members) ->
      fprintf p "@[<hov 0>(TypEnum@ %a@ %a@ %a)@]"
          p4string s
          (print_option print_type) typ
          p4strings members
  | TypTypeName name ->
      fprintf p "@[<hov 0>(TypTypeName@ %a)@]"
          print_name name
  | TypNewType (s, typ) ->
      fprintf p "@[<hov 0>(TypNewType@ %a@ %a)@]"
          p4string s
          print_type typ
  | TypControl ctrl ->
      fprintf p "@[<hov 0>(TypControl@ %a)@]"
          print_control_type ctrl
  | TypParser ctrl ->
      fprintf p "@[<hov 0>(TypParser@ %a)@]"
          print_control_type ctrl
  | TypExtern s ->
      fprintf p "@[<hov 0>(TypExtern@ %a)@]"
          p4string s
  | TypFunction func ->
      fprintf p "@[<hov 0>(TypFunction@ %a)@]"
          print_function_type func
  | TypAction (data_params, ctrl_params) ->
      fprintf p "@[<hov 0>(TypAction@ %a@ %a)@]"
          (print_list print_param) data_params
          (print_list print_param) ctrl_params
  | TypTable s ->
      fprintf p "@[<hov 0>(TypTable@ %a)@]"
          p4string s
  | TypPackage (typ_params, wildcard_params, params) ->
      fprintf p "@[<hov 0>(TypPackage@ %a@ %a@ %a)@]"
          p4strings typ_params
          p4strings wildcard_params
          (print_list print_param) params
  | TypSpecializedType (base, args) ->
      fprintf p "@[<hov 0>(TypSpecializedType@ %a@ %a)@]"
          print_type base
          (print_list print_type) args
  | TypConstructor (typ_params, wildcard_params, params, ret_type) ->
      fprintf p "@[<hov 0>(TypConstructor@ %a@ %a@ %a@ %a)@]"
          p4strings typ_params
          p4strings wildcard_params
          (print_list print_param) params
          print_type ret_type
and print_field_type p field =
  let MkFieldType (s, typ) = field in
      fprintf p "@[<hov 0>(MkFieldType %a@ %a)@]"
          p4string s
          print_type typ
and print_control_type p ctrl =
  let MkControlType (typ_params, params) = ctrl in
      fprintf p "@[<hov 0>(MkControlType %a@ %a)@]"
          p4strings typ_params
          (print_list print_param) params
and print_function_type p func =
  let MkFunctionType (typ_params, params, func_kind, ret_typ) = func in
      fprintf p "@[<hov 0>(MkFunctionType %a@ %a@ %a@ %a)@]"
          p4strings typ_params
          (print_list print_param) params
          print_function_kind func_kind
          print_type ret_typ
and print_param p param =
  let MkParameter (opt, direction, typ, default_arg_id, variable) = param in
      fprintf p "@[<hov 4>(MkParameter %a@ %a@ %a@ %a@ %a)@]"
          print_bool opt
          print_direction direction
          print_type typ
          (print_option print_nat) default_arg_id
          p4string variable

let print_params =
  print_list print_param

let print_stmt_type p (typ : coq_StmType) =
  match typ with
  | StmUnit -> fprintf p "StmUnit"
  | StmVoid -> fprintf p "StmVoid"

let rec print_expr p (expr : coq_Expression) =
  match expr with
  | MkExpression (info, pre_expr, typ, dir) ->
      fprintf p "@[<hov 4>(MkExpression %a@ %a@ %a@ %a)@]"
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
    fprintf p "Axiom %s : @Declaration unit.@ @ " decl_name;
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
      fprintf p "@[<hov 4>Definition %s := DeclError %a@ %a.@]@ @ "
          decl_name
          print_info info
          p4strings decls;
      decl_name
  | _ -> print_dummy_decl p ()

let print_header p =
  fprintf p "Require Import Coq.Lists.List.@ ";
  fprintf p "Require Import Coq.Numbers.BinNums.@ ";
  fprintf p "Require Import Strings.String.@ @ ";
  fprintf p "Require Import Petr4.P4String.@ ";
  fprintf p "Require Import Petr4.Syntax.@ ";
  fprintf p "Require Import Petr4.Typed.@ @ ";
  fprintf p "Open Scope string_scope.@ @ ";
  fprintf p "Import ListNotations.@ @ "

let print_program p (program : Prog.program) =
  fprintf p "@[<v 0>";
  print_header p;
  let decl_names = List.map (print_global_decl p) program in
  fprintf p "Definition program := %a."
    (print_list print_string) decl_names;
  fprintf p "@]@."
