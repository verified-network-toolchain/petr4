module V = Prog.Value
module Op = Typed.Op

val interp_binary_op: Op.bin -> V.value -> V.value -> V.value
val interp_unary_op:  Op.uni -> V.value -> V.value
val interp_cast: type_lookup:(Types.name -> Typed.Type.t) -> val_lookup:(Types.name -> V.value) -> Typed.Type.t -> V.value -> V.value
