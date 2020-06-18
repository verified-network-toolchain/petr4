module V = Prog.Value
module Op = Types.Op

val interp_binary_op: Op.bin -> V.value -> V.value -> V.value
val interp_unary_op: Op.uni -> V.value -> V.value
val interp_cast: type_lookup:(Types.name -> Prog.Type.t) -> Prog.Type.t -> V.value -> V.value
