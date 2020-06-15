module V = Prog.Value
module Op = Typed.Op
open Target

val interp_binary_op: 'a State.t -> Op.bin -> V.value -> V.value -> V.value
val interp_unary_op:  'a State.t -> Op.uni -> V.value -> V.value
val interp_cast: type_lookup:(Types.name -> Typed.Type.t) -> Typed.Type.t -> V.value -> V.value
