Require Import Poulet4.P4cub.BigStep.Value
        Coq.PArith.BinPos Coq.ZArith.BinInt.
Import Val ValueNotations P.P4cubNotations.

(** Intial/Default value from a type. *)
Fixpoint vdefault (τ : E.t) : v :=
  let fix lstruct (ts : list E.t) : list v :=
      match ts with
      | [] => []
      | τ :: ts => vdefault τ :: lstruct ts
      end in
  let fix fields_struct
          (ts : F.fs string E.t) : F.fs string v :=
      match ts with
      | [] => []
      | (x, τ) :: ts => (x, vdefault τ) :: fields_struct ts
      end in
  match τ with
  | {{ error }}      => VError None
  | {{ matchkind }}  => VMatchKind E.MKExact
  | {{ Bool }}       => VBool false
  | {{ bit<w> }}     => VBit w 0%Z
  | {{ int<w> }}     => VInt w 0%Z
  | {{ tuple ts }}   => VTuple (lstruct ts)
  | {{ struct { ts } }} => VStruct (fields_struct ts)
  | {{ hdr { ts } }} => VHeader (fields_struct ts) false
  | {{ stack fs[n] }} => VHeaderStack
                          fs (repeat (false, fields_struct fs)
                                     (Pos.to_nat n)) n 0
  end.
(**[]*)

Fixpoint match_pattern (p : PR.pat) (V : v) : bool :=
  match p, V with
  | [{ ?? }], _ => true
  | [{ (w PW a) &&& (_ PW b) }], ~{ _ VW c }~
    => (Z.land a b =? Z.land c b)%Z
  | [{ (w PW a) .. (_ PW b) }], ~{ _ VW c }~
    => (a <=? c)%Z && (c <=? b)%Z
  | [{ w1 PW n1 }], ~{ w2 VW n2 }~ =>
    (w1 =? w2)%positive && (n1 =? n2)%Z
  | [{ w1 PS n1 }], ~{ w2 VS n2 }~ =>
    (w1 =? w2)%positive && (n1 =? n2)%Z
  | [{ PTUP ps }], ~{ TUPLE vs }~ =>
    (fix F ps vs :=
       match ps, vs with
       | [], [] => true
       | p::ps, v::vs => match_pattern p v && F ps vs
       | _, _ => false
       end) ps vs
  | _,_ => false
  end.
(**[]*)

Section Util.
  Context {tags_t : Type}.
  
  (* TODO: uhhh... *)
  Fail Fixpoint expr_of_value (i : tags_t) (V : v) : E.e tags_t :=
    let fix lstruct (vs : list v) : list (E.e tags_t) :=
        match vs with
        | []      => []
        | hv :: tv => expr_of_value i hv :: lstruct tv
        end in
    let fix fstruct (vs : F.fs string v)
        : F.fs string (E.t * E.e tags_t) :=
        match vs with
        | [] => []
        | (x, hv) :: vs => (x, (_, expr_of_value i hv)) :: fstruct vs (* TODO *)
        end in
    let fix stkstruct (hs : list (bool * F.fs string v))
        : list (E.e tags_t) :=
        match hs with
        | [] => []
        | (b, vs) :: hs
          => E.EHeader (fstruct vs) <{ BOOL b @ i }> i :: stkstruct hs
        end in
    match V with
    | ~{ VBOOL b }~ => <{ BOOL b @ i }>
    | ~{ w VW n }~ => <{ w W n @ i }>
    | ~{ w VS z }~ => <{ w S z @ i }>
    | ~{ ERROR err }~ => <{ Error err @ i }>
    | ~{ MATCHKIND mk }~ => <{ Matchkind mk @ i }>
    | ~{ TUPLE vs }~ => E.ETuple (lstruct vs) i
    | ~{ STRUCT { vs } }~ => E.EStruct (fstruct vs) i
    | ~{ HDR { vs } VALID:=b }~
      => E.EHeader (fstruct vs) <{ BOOL b @ i }> i
    | ~{ STACK vs:ts[n] NEXT:=ni }~
      => E.EHeaderStack ts (stkstruct vs) n ni
    end.
End Util.
