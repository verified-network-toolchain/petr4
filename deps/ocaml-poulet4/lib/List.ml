
(** val last : 'a1 list -> 'a1 -> 'a1 **)

let rec last l d =
  match l with
  | [] -> d
  | a :: l0 -> (match l0 with
                | [] -> a
                | _ :: _ -> last l0 d)

(** val removelast : 'a1 list -> 'a1 list **)

let rec removelast = function
| [] -> []
| a :: l0 -> (match l0 with
              | [] -> []
              | _ :: _ -> a :: (removelast l0))

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)
