Require Export Poulet4.P4cub.Syntax.Syntax.
Import AllCubNotations.

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
  let fix denote_fs (ts : Field.fs string Expr.t) : Set :=
      match ts with
      | []          => unit
      | (x, t) :: ts => (denote_t t * denote_fs ts)%type (* TODO *)
      end in
  match t with
  | {{ Bool }} => bool
  | {{ bit<_> }} => Z
  | {{ int<_> }} => Z
  | {{ error }} => string
  | {{ matchkind }} => string
  | {{ tuple ts }} => denote_ts ts
  | {{ struct { ts } }} => denote_fs ts
  | {{ hdr { ts } }} => (denote_fs ts * bool)%type
  | {{ stack ts[n] }} =>  _
  end.
