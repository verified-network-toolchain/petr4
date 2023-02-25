open Poulet4

val interp :
  (P4info.t, P4info.t P4light.pre_Expression)
    Target.coq_Target ->
  P4info.t P4light.pre_program ->
  Obj.t Maps.PathMap.t ->
  Bigint.t ->
  bool list ->
  (Target.Exn.t,
   (Obj.t Maps.PathMap.t * Bigint.t) * bool list)
    Result.result

val v1_interp :
  P4light.program ->
  Obj.t Maps.PathMap.t ->
  Bigint.t ->
  bool list ->
  (Target.Exn.t,
   (Obj.t Maps.PathMap.t * Bigint.t) * bool list)
  Result.result

