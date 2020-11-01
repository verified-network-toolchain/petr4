open Common

let to_string pp : string =
  Format.fprintf Format.str_formatter "%a" Pp.to_fmt pp;
  Format.flush_str_formatter ()

type 'a info = Info.t * 'a [@@deriving sexp,show,yojson]
let info (i,_) = i

(* expressions *) 
let t = Prettypp.Expression.format_t (Info.dummy, Types.Expression.True) 
let f = Prettypp.Expression.format_t (Info.dummy, Types.Expression.False)

let i = Prettypp.Expression.format_t 
    (Info.dummy, Types.Expression.Int
       (Info.dummy, {value = Bigint.of_int 0; width_signed = None}))
let s = Prettypp.Expression.format_t 
    (Info.dummy, Types.Expression.String(Info.dummy, "helloworld"))

let barename = Prettypp.Expression.format_t 
    (Info.dummy, Types.Expression.Name(BareName (Info.dummy, "name")))
let qualifiedname = Prettypp.Expression.format_t 
    (Info.dummy, Types.Expression.Name
       (QualifiedName ([], (Info.dummy, "qualname")))) 

let lst = Types.Expression.List
    ({values = [(Info.dummy, Types.Expression.True)]})
let arrayaccess = Prettypp.Expression.format_t 
    (Info.dummy, Types.Expression.ArrayAccess
       ({array = (Info.dummy, lst); 
         index = (Info.dummy, 
                  Types.Expression.Int(Info.dummy, 
                                       {value = Bigint.of_int 0; 
                                        width_signed = None}))})) 
let lst2 = Prettypp.Expression.format_t 
    (Info.dummy, Types.Expression.List
       ({values = [(Info.dummy, Types.Expression.True);
                   (Info.dummy, Types.Expression.False)]}))

(* bitstringaccess? *)

let kv = Types.KeyValue.(
    {key = (Info.dummy, "key"); 
     value = (Info.dummy, Types.Expression.True)})
let kv2 = Types.KeyValue.(
    {key = (Info.dummy, "a"); 
     value = (Info.dummy, Types.Expression.False)})
let record = Prettypp.Expression.format_t 
    (Info.dummy, Types.Expression.Record
       ({entries = [(Info.dummy, kv)]})) 
let record2 = Prettypp.Expression.format_t 
    (Info.dummy, Types.Expression.Record
       ({entries = [(Info.dummy, kv); (Info.dummy, kv2)]})) 

let unaryop = Prettypp.Expression.format_t 
    (Info.dummy, 
     Types.Expression.UnaryOp({op = (Info.dummy, Not); 
                               arg = (Info.dummy, Types.Expression.True)}))
let unaryop2 = Prettypp.Expression.format_t 
    (Info.dummy, 
     Types.Expression.UnaryOp({op = (Info.dummy, BitNot); 
                               arg = (Info.dummy, Types.Expression.True)}))
let unaryop3 = Prettypp.Expression.format_t 
    (Info.dummy, 
     Types.Expression.UnaryOp({op = (Info.dummy, UMinus); 
                               arg = (Info.dummy, Types.Expression.True)}))

(* tests *)
let test = 
  "true" = (to_string t) && 
  "false" = (to_string f) &&
  "0" = (to_string i) &&
  "helloworld" = (to_string s) &&
  "name" = (to_string barename) &&
  ".qualname" = (to_string qualifiedname) &&
  "{true}[0]" = (to_string arrayaccess) &&
  "{true,false}" = (to_string lst2) &&
  "{key = true}" = (to_string record) && 
  "{key = true,a = false}" = (to_string record2) &&
  "(!true)" = (to_string unaryop) &&
  "(~true)" = (to_string unaryop2) &&
  "(-true)" = (to_string unaryop3)

