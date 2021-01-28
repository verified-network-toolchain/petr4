open Typed
open Prog
    
val interp_binary_op: coq_OpBin -> coq_ValueBase -> coq_ValueBase -> coq_ValueBase
val interp_unary_op: coq_OpUni -> coq_ValueBase -> coq_ValueBase
val interp_cast: type_lookup:(P4name.t -> coq_P4Type) -> coq_P4Type -> coq_ValueBase -> coq_ValueBase
