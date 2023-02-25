Require Export Poulet4.P4cub.Syntax.Syntax.
Import AllCubNotations String.

Fixpoint denote_list (l : list Set) : Set :=
  match l with
  | []    => unit
  | h :: t => h * denote_list t
  end.

(* TODO: some denotations are  incomplete. *)
Fail Fixpoint denote_t (t : Expr.t) : Set :=
  let fix denote_ts (ts : list Expr.t) : Set :=
      match ts with
      | []     => unit
      | t :: ts => (denote_t t * denote_ts ts)%type
      end in
  match t with
  | Expr.TBool => bool
  | Expr.TBit _ => N
  | Expr.TInt _ => Z
  | Expr.TError => string
  | Expr.TStruct ts _ => denote_ts ts
  end.
