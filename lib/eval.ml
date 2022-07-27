open Poulet4.Interpreter
open P4light

let rec infinite_fuel : coq_Fuel = MoreFuel infinite_fuel

let interp
      (target: (P4info.t, coq_Expression) Poulet4.Target.coq_Target)
      (prog: program)
      (st: (P4info.t, coq_Expression) Poulet4.Target.extern_state)
      (in_port: Bigint.t)
      (pkt: bool list)
    : (((P4info.t, coq_Expression) Poulet4.Target.extern_state *
          Bigint.t) *
         bool list)
        option =
  Poulet4.Interpreter.interp P4info.dummy target infinite_fuel prog st in_port pkt

open Poulet4.V1ModelTarget
let v1_interp =
  interp coq_V1Model
