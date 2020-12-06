open Typed
open Prog
    
val interp_binary_op: coq_OpBin -> coq_Value -> coq_Value -> coq_Value
val interp_unary_op: coq_OpUni -> coq_Value -> coq_Value
val interp_cast: type_lookup:(Types.name -> coq_P4Type) -> coq_P4Type -> coq_Value -> coq_Value
