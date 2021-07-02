Set Warnings "custom-entry-overridden,parsing".
Require Import Coq.PArith.BinPosDef Coq.PArith.BinPos
        Coq.ZArith.BinIntDef Coq.ZArith.BinInt.
Require Import Poulet4.P4Arith Poulet4.P4cub.Syntax.AST.

Module P := P4cub.
Module F := P.F.
Module E := P.Expr.
Module PRSR := P.Parser.

(** Custom induction principle for [t]. *)
Section TypeInduction.
  Import E TypeNotations.
  
  (** An arbitrary property. *)
  Variable P : t -> Prop.
  
  Hypothesis HTBool : P {{ Bool }}.
  
  Hypothesis HTBit : forall w, P {{ bit<w> }}.
  
  Hypothesis HTInt : forall w, P {{ int<w> }}.
  
  Hypothesis HTError : P {{ error }}.
  
  Hypothesis HTMatchKind : P {{ matchkind }}.
  
  Hypothesis HTTuple : forall ts,
      Forall P ts -> P {{ tuple ts }}.
  
  Hypothesis HTStruct : forall fields,
      F.predfs_data P fields -> P {{ struct { fields } }}.
  
  Hypothesis HTHeader : forall fields,
      F.predfs_data P fields -> P {{ hdr { fields } }}.
  
  Hypothesis HTHeaderStack : forall fields size,
      F.predfs_data P fields -> P {{ stack fields[size] }}.
  
  (** A custom induction principle.
      Do [induction ?t using custom_t_ind]. *)
  Definition custom_t_ind : forall ty : t, P ty :=
    fix custom_t_ind (type : t) : P type :=
      let fix list_ind (ts : list t) :
            Forall P ts :=
          match ts with
          | [] => Forall_nil _
          | h :: ts => Forall_cons _ (custom_t_ind h) (list_ind ts)
          end in
      let fix fields_ind
              (flds : F.fs string t) : F.predfs_data P flds :=
          match flds with
          | [] => Forall_nil (F.predf_data P)
          | (_, hft) as hf :: tf
            => Forall_cons hf (custom_t_ind hft) (fields_ind tf)
          end in
      match type with
      | {{ Bool }} => HTBool
      | {{ bit<w> }} => HTBit w
      | {{ int<w> }} => HTInt w
      | {{ error }} => HTError
      | {{ matchkind }} => HTMatchKind
      | {{ tuple ts }}  => HTTuple ts (list_ind ts)
      | {{ struct { fields } }} => HTStruct fields (fields_ind fields)
      | {{ hdr { fields } }} => HTHeader fields (fields_ind fields)
      | {{ stack fields[n] }} => HTHeaderStack fields n (fields_ind fields)
      end.
  (**[]*)
End TypeInduction.

(** A custom induction principle for [e]. *)
Section ExprInduction.
  Import E.
  Import TypeNotations.
  Import UopNotations.
  Import ExprNotations.
  Import BopNotations.
  Import MatchkindNotations.
  
  (** An arbitrary predicate. *)
  Variable tags_t : Type.
  
  Variable P : e tags_t -> Prop.
  
  Hypothesis HEBool : forall b i, P <{ BOOL b @ i }>.
  
  Hypothesis HEBit : forall w n i, P <{ w W n @ i }>.
  
  Hypothesis HEInt : forall w n i, P <{ w S n @ i }>.
  
  Hypothesis HEVar : forall (ty : t) (x : string) i,
      P <{ Var x : ty @ i }>.
  
  Hypothesis HESlice : forall n τ hi lo i,
      P n -> P <{ Slice n:τ [ hi : lo ] @ i }>.
  
  Hypothesis HECast : forall τ exp i,
      P exp -> P <{ Cast exp:τ @ i }>.
  
  Hypothesis HEUop : forall (op : uop) (ty : t) (ex : e tags_t) i,
      P ex -> P <{ UOP op ex : ty @ i }>.
  
  Hypothesis HEBop : forall (op : bop) (lt rt : t) (lhs rhs : e tags_t) i,
      P lhs -> P rhs -> P <{ BOP lhs:lt op rhs:rt @ i }>.
  
  Hypothesis HETuple : forall es i,
      Forall P es -> P <{ tup es @ i }>.
  
  Hypothesis HEStruct : forall fields i,
      F.predfs_data (P ∘ snd) fields -> P <{ struct {fields} @ i }>.
  
  Hypothesis HEHeader : forall fields b i,
      P b -> F.predfs_data (P ∘ snd) fields ->
      P <{ hdr {fields} valid:=b @ i }>.
  
  Hypothesis HEExprMember : forall x ty expr i,
      P expr -> P <{ Mem expr:ty dot x @ i }>.
  
  Hypothesis HEError : forall err i, P <{ Error err @ i }>.
  
  Hypothesis HEMatchKind : forall mkd i, P <{ Matchkind mkd @ i }>.
  
  Hypothesis HEStack : forall ts hs size ni i,
      Forall P hs ->
      P <{ Stack hs:ts [size] nextIndex:=ni @ i }>.
  
  Hypothesis HAccess : forall e1 e2 i,
      P e1 -> P <{ Access e1[e2] @ i }>.
  
  (** A custom induction principle.
      Do [induction ?e using custom_e_ind]. *)
  Definition custom_e_ind : forall exp : e tags_t, P exp :=
    fix eind (expr : e tags_t) : P expr :=
      let fix fields_ind {A:Type} (flds : F.fs string (A * e tags_t))
          : F.predfs_data (P ∘ snd) flds :=
          match flds with
          | [] => Forall_nil (F.predf_data (P ∘ snd))
          | (_, (_, hfe)) as hf :: tf
            => Forall_cons hf (eind hfe) (fields_ind tf)
          end in
      let fix list_ind (es : list (e tags_t)) : Forall P es :=
          match es with
          | [] => Forall_nil P
          | exp :: ees => Forall_cons exp (eind exp) (list_ind ees)
          end in
      match expr with
      | <{ BOOL b @ i }> => HEBool b i
      | <{ w W n @ i }>  => HEBit w n i
      | <{ w S n @ i }>  => HEInt w n i
      | <{ Var x:ty @ i }> => HEVar ty x i
      | <{ Slice n:τ [h:l] @ i }> => HESlice n τ h l i (eind n)
      | <{ Cast exp:τ @ i }> => HECast τ exp i (eind exp)
      | <{ UOP op exp:ty @ i }> => HEUop op ty exp i (eind exp)
      | <{ BOP lhs:lt op rhs:rt @ i }>
        => HEBop op lt rt lhs rhs i
                (eind lhs) (eind rhs)
      | <{ tup es @ i }>         => HETuple es i (list_ind es)
      | <{ struct { fields } @ i }> => HEStruct fields i (fields_ind fields)
      | <{ hdr { fields } valid:=b @ i }>
        => HEHeader fields b i (eind b) (fields_ind fields)
      | <{ Mem exp:ty dot x @ i }> => HEExprMember x ty exp i (eind exp)
      | <{ Error err @ i }> => HEError err i
      | <{ Matchkind mkd @ i }> => HEMatchKind mkd i
      | <{ Stack hs:ts [n] nextIndex:=ni @ i }>
        => HEStack ts hs n ni i (list_ind hs)
      | <{ Access e1[e2] @ i }> => HAccess e1 e2 i (eind e1)
      end.
  (**[]*)
End ExprInduction.

(** A custom induction principle for select patterns. *)
Section PatternInduction.
  Import PRSR.
  Import ParserNotations.
      
  Variable P : pat -> Prop.
      
  Hypothesis HWild : P [{ ?? }].
  
  Hypothesis HMask : forall p1 p2,
      P p1 -> P p2 -> P [{ p1 &&& p2 }].
  
  Hypothesis HRange : forall p1 p2,
      P p1 -> P p2 -> P [{ p1 .. p2 }].
  
  Hypothesis HBit : forall w n, P [{ w PW n }].
  
  Hypothesis HInt : forall w n, P [{ w PS n }].
  
  Hypothesis HTuple : forall ps,
      Forall P ps -> P [{ PTUP ps }].
  
  (** A custom induction principle,
      do [induction ?H using custom_pat_ind]. *)
  Definition custom_pat_ind : forall (p : pat), P p :=
    fix pind (p : pat) : P p :=
      let fix lind (ps : list pat) : Forall P ps :=
          match ps with
          | [] => Forall_nil _
          | p::ps => Forall_cons p (pind p) (lind ps)
          end in
      match p with
      | [{ ?? }] => HWild
      | [{ p1 &&& p2 }] => HMask p1 p2 (pind p1) (pind p2)
      | [{ p1 .. p2 }] => HRange p1 p2 (pind p1) (pind p2)
      | [{ w PW n }] => HBit w n
      | [{ w PS z }] => HInt w z
      | [{ PTUP ps }] => HTuple ps (lind ps)
      end.
  (**[]*)
End PatternInduction.

(** A custom induction principle for parser expressions. *)
Section ParserExprInduction.
  Import PRSR.
  Import ParserNotations.
  Import E.ExprNotations.
  
  Context {tags_t : Type}.
  
  (** An arbitrary predicate. *)
  Variable P : e tags_t -> Prop.
  
  Hypothesis HState : forall st i, P p{ goto st @ i }p.
  
  Hypothesis HSelect : forall exp st cases i,
      F.predfs_data P cases ->
      P p{ select exp { cases } default:=st @ i }p.
  (**[]*)
  
  (** A custom induction principle,
      do [induction ?H using pe_ind] *)
  Definition pe_ind : forall pe : e tags_t, P pe :=
    fix peind pe : P pe :=
      let fix fsind {A : Type} (es : F.fs A (e tags_t))
          : F.predfs_data P es :=
          match es with
          | [] => Forall_nil _
          | (_,pe) as epe :: es =>
            Forall_cons epe (peind pe) (fsind es)
          end in
      match pe with
      | p{ goto st @ i }p => HState st i
      | p{ select exp { cases } default:=st @ i }p
        => HSelect exp st _ i (fsind cases)
      end.
  (**[]*)
End ParserExprInduction.
