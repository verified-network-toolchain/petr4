(** Function composition. *)
let ($$) (f : 'b -> 'c) (g : 'a -> 'b) : 'a -> 'c =
 fun (x : 'a) -> x |> g |> f

(** Lifting declaration lists to programs. *)
let pgm (ds : Petr4.Prog.Declaration.t list) : Petr4.Prog.program = Petr4.Prog.Program ds
