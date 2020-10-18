open Core_kernel
open Pp
open StdLabels
open List 
module P4 = Types 

let print pp = Format.printf "%a" Pp.to_fmt pp

let format_list_sep f sep l = 
  concat_map ~sep:("," |> text) l ~f:f;

module P4Int = struct
  open P4.P4Int
  let format_bigint (u:unit) b = b |> Bigint.to_string |> textf "%s"
  let format_t (u:unit) e =
    let i = snd e in
    (match i.width_signed with
     | None -> failwith "unimplemented"
     | Some (width,signed) -> failwith "unimplemented" )
    (* textf "%d%s" width (if signed then "s" else "w")) *)
end

module P4String = struct 
  let format_t (u:unit) e = e |> snd |> textf "%s"
  let format_t_help (u:unit) e = snd e  
end

let name_format_t (u: unit) (name: Types.name) =
  match name with
  | BareName str -> P4String.format_t_help () str 
  (* | QualifiedName ([], str) -> P4String.format_t_help () "." *)
  | _ -> failwith "unimplemented"

module rec Expression : sig
  val format_t : unit -> P4.Expression.t -> _ Pp.t 
end = struct
  open P4.Expression
  let rec format_t (u:unit) e =
    match snd e with
    | True ->  text "true" 
    | False -> text "false"
    | Int i -> failwith "unimplemented"
    | String s -> textf "\"%s\"" (snd s)
    | Name name -> failwith "unimplemented"
    | ArrayAccess x ->
      textf "@[%a[%a]@]"
        format_t x.array
        format_t x.index
    | _ -> failwith "unimplemented"
end 

and Type : sig
  val format_t : P4.Type.t -> _ Pp.t
  (* val format_typ_args: P4.Type.t list 
     val format_type_params: P4.P4String.t list  *)
end = struct
  open P4.Type
  let rec format_t e =
    match snd e with
    | Bool -> text "bool"
    | Error -> text "error"
    | Integer -> text "int"
    | IntType x -> textf "@[int<%a>@]" Expression.format_t x |> box 
    | BitType e -> string_of_format "hello" 
    (* begin match snd e with 
       | P4.Expression.Int _  -> 
        Format.fprintf fmt "@[bit<%a>@]"
          Expression.format_t e
       | _ -> 
        Format.fprintf fmt "@[bit<(%a)>@]"
          Expression.format_t e
       end *)
    | VarBit x ->
      Format.fprintf fmt "@[varbit@ <%a>@]"
        Expression.format_t x
    | TypeName (BareName x) ->
      Format.fprintf fmt "@[%s@]"
        (snd x)
    | TypeName (QualifiedName ([], x)) ->
      Format.fprintf fmt "@[.%s@]"
        (snd x);
    | TypeName _ ->
      failwith "unimplemented"
    | SpecializedType x ->
      Format.fprintf fmt "@[%a<%a>@]"
        format_t x.base
        (format_list_sep format_t ",") x.args
    | HeaderStack x ->
      Format.fprintf fmt "@[%a[%a]@]"
        format_t x.header
        Expression.format_t x.size
    | Tuple x ->
      Format.fprintf fmt "@[tuple<%a>@]"
        (format_list_sep format_t ",") x
    | String -> 
      Format.fprintf fmt "string"      
    | Void ->
      Format.fprintf fmt "void"
    | DontCare ->
      Format.fprintf fmt "_"
      (* 
  let format_typ_args fmt l =
    if List.is_empty l then
      ()
    else
      Format.fprintf fmt "<%a>"
        (format_list_sep format_t ",") l

  let format_type_params fmt l =
    if List.is_empty l then
      ()
    else
      Format.fprintf fmt "<%a>"
        (format_list_sep P4String.format_t ",") l *)
end


    (* | Int i -> i |> Bigint.to_string |> textf "%s" 
         | String s -> textf "\"%a\"" P4String.format_t_help s 
         | Name name -> textf "%a" name_format_t () name
         | ArrayAccess x ->
         textf "@[%a[%a]@]"
          format_t () x.arrays
          format_t () x.index *)
    | _ -> failwith "f"
(* 
    | String s -> s |> P4String.format_t
    | N=ame name -> name |> name_format_t
    | ArrayAccess x -> failwith "d"
    (* (textf "@[%a[%a]@]"
       format_t x.array
       format_t x.index) |> print  *)
    (* x.array |> format_t;
       "[" |> text |> print; 
       x.index |> format_t; 
       "]" |> text |> print; *)
    (* put it all in a box  *)
    | BitStringAccess x -> 
      x.bits |> format_t;
      "[" |> text |> print; 
      x.hi |> format_t;
      ":" |> text |> print; 
      x.lo |> format_t;
      "]" |> text |> print
    (*put all in box *)
    | List x -> failwith "unimplemented"
    (* "{" |> text |> print;
       concat_map ~sep:("," |> text) x.values ~f: (format_t)  
       "}" |> text |> print; *)
    (* put all in a box, int offset 4 *)
    | Record x -> failwith "unimplemented"
    (* do list first *)
    | UnaryOp x ->
      let uop = match (snd x.op) with
        | Not -> "!"
        | BitNot -> "~"
        | UMinus -> "-"
      in
      uop |> text |> print;
      space |> print; 
      x.arg |> format_t 
    (* put in box with int offset 4  *)
    | BinaryOp x ->
      let bop = match (snd x.op) with
          Plus -> "+"
        | PlusSat -> "|+|"
        | Minus -> "-"
        | MinusSat -> "|-|"
        | Mul -> "*"
        | Div -> "/"
        | Mod -> "%"
        | Shl -> "<<"
        | Shr -> ">>"
        | Le -> "<="
        | Ge -> ">="
        | Lt -> "<"
        | Gt -> ">"
        | Eq -> "=="
        | NotEq -> "!="
        | BitAnd -> "&"
        | BitXor -> "^"
        | BitOr -> "|"
        | PlusPlus -> "++"
        | And -> "&&"
        | Or -> "||"
      in
      x.args |> fst |> format_t; 
      space |> print; 
      bop |> text|> print; 
      space |> print; 
      x.args |> snd |> format_t 
    (* put in box offset 4 *)
    | Cast x ->
      "(" |> text |> print; 
      x.typ |> Type.format_t; 
      ")" |> text |> print; 
      "(" |> text |> print; 
      format_t x.expr; 
      ")" |> text |> print 
    (* put in box offset 4 *)
    | TypeMember x -> 
      name_format_t x.typ; 
      "." |> text |> print; 
      x.name |> snd |> text |> print 
    (* need to put all in one box, offset 4*)
    | ErrorMember x -> failwith "unimplemented"
    (* pp has no way to print errors? should I make a new print function with "@[<4>error.%s@]" ? *)
    | ExpressionMember x -> 
      format_t x.expr; 
      "." |> text |> print; 
      x.name |> snd |> text |> print 
    (* put in box offset 4 *)
    | Ternary x -> 
      "(" |> text |> print; 
      format_t x.cond; 
      "?" |> text |> print; 
      print space; 
      format_t x.tru; 
      print space; 
      ":" |> text |> print;
      print space; 
      format_t x.fls;
      ")" |> text |> print 
    (* put in box offset 4 *)
    | FunctionCall x -> 
      x.func |> format_t; 
      x.type_args |> Type.format_typ_args; 
      "(" |> text |> print;
      (* format_list_sep format_t ("," |> text) x.type_args;   *)
      ")" |> text |> print 
    (* put in box offset 4 *)
    | NamelessInstantiation x ->  
      x.typ |> Type.format_t;  
      "(" |> text |> print; 
      (* format_list_sep format_t ("," |> text) x.args;   *)
      ")" |> text |> print
    (* put in offset 4 box *)
    | Mask x ->
      format_t x.expr; 
      print space; 
      "&&&" |> text |> print; 
      print space;  
      format_t x.mask
    (* box offset 4 *)
    | Range x -> 
      format_t x.lo; 
      print space; 
      ".." |> text |> print; 
      print space; 
      format_t x.hi *)
(* box offset 4 *)
(* end

   and Statement : sig
      val format_t : P4.Statement.t -> unit
    end = struct
                  open P4.Statement

                  let format_switch_label sl =
                    match sl with
                    | Default -> "default" |> text |> print 
                    | Name(sl) -> ("\"" ^ (snd sl) ^ "\"") |> text |> box |> print 

                  let format_switch_case fmt sc =
                    match snd sc with
                    | Action { label; code } -> failwith "unimplemented"
                    | FallThrough { label } -> failwith "unimplemented"   

                  let format_t (e:t) =
                    match snd e with
                    | MethodCall { func; type_args; args } -> failwith "unimplemented"
                    | Assignment { lhs; rhs } -> failwith "unimplemented"
                    | DirectApplication { typ; args } -> failwith "unimplemented"
                    | Conditional { cond; tru; fls } -> failwith "unimplemented"
                    | BlockStatement { block } -> failwith "unimplemented"
                    | Exit -> "exit;" |> text |> print 
                    | EmptyStatement -> ";" |> text |> print 
                    | Return { expr = None } -> "return;" |> text |> print 
                    | Return { expr = Some sexpr } -> failwith "unimplemented"
                    | Switch { expr; cases } -> failwith "unimplemented"
                    | DeclarationStatement { decl } -> failwith "unimplemented"
                end

   and Block : sig
      val format_t :P4.Block.t -> unit
    end = struct
              open P4.Block
              let format_t e =
                match snd e with
                | { annotations=[]; statements=[] } -> "{ }@]" |> text |> print 
                | { annotations; statements } -> failwith "unimplemented"
            end

   and Argument : sig
      val format_t : P4.Argument.t -> unit
      val format_ts : P4.Argument.t list -> unit
    end = struct
                 open P4.Argument
                 let format_t  e =
                   match snd e with
                   | Expression x -> failwith "unimplemented"
                   | KeyValue x -> failwith "unimplemented"
                   | Missing -> "_" |> text |> print 
                 let format_ts l = failwith "unimplemented"
               end

   (* 
   and Type : sig
   val format_typ_args: P4.Type.t list -> unit
   val format_t : P4.Type.t -> unit
   end = struct
   open P4.Type
   let format_t e =
    match snd e with
    | Bool -> "bool" |> text |> print 
    | Error -> "error" |> text |> print 
    | Integer -> "int" |> text |> print 
    | IntType x -> x |> Expression.format_t 
    | BitType e -> 
      begin match snd e with 
        | P4.Expression.Int _  -> 
          Expression.format_t e
        | _ -> 
          Expression.format_t e
      end
    | VarBit x ->
      Expression.format_t x
    | TypeName (BareName x) ->
      (snd x) |> text |> box |> print 
    | TypeName (QualifiedName ([], x)) ->
      "." |> text |> print; 
      (snd x) |> text |> box |> print 
    | TypeName _ ->
      failwith "unimplemented"
    | SpecializedType x ->
      failwith "unimplemented"
    | HeaderStack x ->
      failwith "unimplemented"
    | Tuple x ->
      failwith "unimplemented "
    (* "tuple " |> text |> print; 
       "<" |> text |> print;
       (concat ~sep:(text ", ") (format_t x)) |> print;
       ">" |> text |> print  *)
    | String -> 
      "string" |> text |> print  
    | Void ->
      "void" |> text |> print
    | DontCare ->
      "_" |> text |> print

   let format_typ_args l =
    if (List.length l = 0) then
      ()
    else
      "<" |> text |> print;
    (* (format_list_sep format_t ",") l; *)
    ">" |> text |> print; 
   end  *)

   (* and KeyValue : sig 
   val format_t : Format.formatter -> P4.KeyValue.t -> unit
   end = struct
   open P4.KeyValue
   let format_t fmt kv = 
    match snd kv with 
    | { key; value } -> 
      key |> P4String.format_t; 
      " = " |> text |> print; 
      value |> Expression.format_t; 
   end *)

   and Annotation : sig
      val format_t : P4.Annotation.t -> unit
      val format_ts : P4.Annotation.t list -> unit
    end = struct
                   open P4.Annotation
                   let format_body body = 
                     match snd body with 
                     | Empty -> 
                       ()
                     | Unparsed strings -> failwith "unimplemented"
                     | Expression exprs -> 
                       failwith "unimplemented"
                     | KeyValue kvs -> 
                       failwith "unimplemented"

                   let format_t  e =
                     match snd e with 
                     | { name; body } -> failwith "unimplemented"

                   let format_ts l =
                     match l with
                     | [] ->
                       ()
                     | _ :: _ ->
                       failwith "unimplemented"
                 end

   and Direction : sig
      val format_t : P4.Direction.t -> unit
    end = struct
                  open P4.Direction
                  let format_t e =
                    match snd e with
                    | In -> "in" |> text |> print 
                    | Out -> "out" |> text |> print 
                    | InOut -> "inout" |> text |> print 
                end

   (* and Parameter : sig
   end *)

   (* 
   and Match: sig
   end *)

   (* and Parser : sig
   end *)

   (* and Table : sig
   end *)

   (* and MethodPrototype : sig
   end *)


   (* and Declaration : sig
   end *)

   let format_program fmt p = *)