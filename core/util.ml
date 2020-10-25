(** Function composition. *)
let ($$) (f : 'b -> 'c) (g : 'a -> 'b) =
 fun (x : 'a) -> x |> g |> f
