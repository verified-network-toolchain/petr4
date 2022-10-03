open Poulet4.Interpreter
open Poulet4.V1ModelTarget

let rec infinite_fuel : coq_Fuel = MoreFuel infinite_fuel

let interp target prog st in_port pkt =
  Poulet4.Interpreter.interp P4info.dummy target infinite_fuel prog st in_port pkt

let v1_interp =
  interp (Obj.magic coq_V1Model)
