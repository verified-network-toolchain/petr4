open Types

type t =
  | Bool of bool
  | Integer of Bigint.t
  | Bit of
      { width: int;
        value: Bigint.t }
  | Int of
      { width: int;
        value: Bigint.t }
  | List of t list
  | Set of set
  | String of string
  | Error of P4String.t
  | Header_or_struct of (P4String.t * t) list
  (* | headers and structs as mappings from strings to value *)
  | Objstate of obj 
  (* stateful objects *)

and set = 
  | Singleton of Bigint.t 
  | Universal 
  | Mask of t * t
  | Range of t * t
  | Prod 

and obj =
  { decl: Types.Declaration.t;
    state: (P4String.t * t) list; }
