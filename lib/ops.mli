module V = Prog.Value
module Op = Typed.Op

val interp_binary_op: Op.bin -> V.value -> V.value -> V.value
val interp_unary_op:  Op.uni -> V.value -> V.value
val interp_cast: type_lookup:(Types.name -> Typed.Type.t) -> Typed.Type.t -> V.value -> V.value
