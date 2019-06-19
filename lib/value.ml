open Types

type 'env pre_value =
  | VNull
  | VBool of bool
  | VInteger of Bigint.t
  | VBit of int * Bigint.t (* width, value *)
  | VInt of int * Bigint.t
  | VList of ('env pre_value) list
  | VSet of 'env pre_set
  | VString of string
  | VError of P4String.t
  | VClosure of Parameter.t list * Block.t * 'env
  | VHeader_or_struct of (P4String.t * 'env pre_value) list
  (* | headers and structs as mappings from strings to value *)
  | VObjstate of 'env pre_obj
  (* stateful objects *)

and 'env pre_set =
  | SSingleton of Bigint.t
  | SUniversal
  | SMask of 'env pre_value * 'env pre_value
  | SRange of 'env pre_value * 'env pre_value
  | SProd

and 'env pre_obj =
  { decl: Types.Declaration.t;
    state: (P4String.t * 'env pre_value) list; }

type 'env pre_signal =
  | SContinue
  | SReturn of 'env pre_value
  | SExit
