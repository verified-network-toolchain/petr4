open Types

type env = Context.t

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
  | Struct' of env

and set = 
  | Singleton of Bigint.t 
  | Universal 
  | Mask of t * t
  | Range of t * t
  | Prod 
