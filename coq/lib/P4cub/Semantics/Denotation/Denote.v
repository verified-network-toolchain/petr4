Require Export Poulet4.P4cub.Syntax.Syntax.

Fixpoint denote_list (l : list Set) : Set :=
  match l with
  | []    => unit
  | h :: t => h * denote_list t
  end.

(* TODO: some denotations are  incomplete. *)
Fail Fixpoint denote_typ (t : Typ.t) : Set :=
  let fix denote_typs (ts : list Typ.t) : Set :=
      match ts with
      | []     => unit
      | t :: ts => (denote_typ t * denote_typs ts)%type
      end in
  match t with
  | Typ.Bool => bool
  | Typ.Bit _ => N
  | Typ.Int _ => Z
  | Typ.Error => String.string
  | Typ.Struct ts _ => denote_typs ts
  | Typ.VarBit _ => N
  | Typ.Array _ t => list $ denote_typ t
  end.
