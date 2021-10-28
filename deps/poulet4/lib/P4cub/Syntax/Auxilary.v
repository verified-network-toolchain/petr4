Set Warnings "custom-entry-overridden,parsing".
Require Import Coq.PArith.BinPosDef Coq.PArith.BinPos
        Coq.ZArith.BinIntDef Coq.ZArith.BinInt
        Poulet4.Monads.Monad Poulet4.Monads.Option.
Require Import Poulet4.P4Arith Poulet4.P4cub.Syntax.AST
        Poulet4.P4cub.Syntax.CubNotations
        Poulet4.P4cub.Syntax.Equality.
Import Expr TypeNotations UopNotations BopNotations ExprNotations MatchkindNotations.

Fixpoint width_of_typ (τ : t) : option nat :=
  match τ with
  | {{ Bool }} => Some 1%nat
  | {{ bit<w> }}
  | {{ int<w> }} => Some $ Pos.to_nat w
  | {{ error }}
  | {{ matchkind }} => Some 0%nat
  | {{ tuple ts }} =>
    ns <<| sequence $ List.map width_of_typ ts ;;
    List.fold_left Nat.add ns 0%nat
  | {{ struct { fs } }}
  | {{ hdr { fs } }} =>
    ns <<| sequence $ List.map (fun '(_,t) => width_of_typ t) fs ;;
    List.fold_left Nat.add ns 0%nat
  | {{ stack fs[s] }} =>
    ns <<| sequence $ List.map (fun '(_,t) => width_of_typ t) fs ;;
    (Pos.to_nat s * List.fold_left Nat.add ns 0%nat)%nat
  | TVar _ => None
  end.

(** Expected result type of uop. *)
Definition t_of_uop (op : uop) (ty : t) : option t :=
  match op, ty with
  | _{ ! }_                            , {{ Bool }}
  | (_{ ~ }_ | _{ - }_)                , ({{ bit<_> }} | {{ int<_> }})
  | (_{ setValid }_ | _{ setInValid }_), {{ hdr { _ } }}   => Some ty
  | _{ isValid }_                      , {{ hdr { _ } }}   => Some {{ Bool }}
  | _{ Next }_                         , {{ stack ts[_] }} => Some {{ hdr { ts } }}
  | _{ Size }_                         , {{ stack _[_] }}  => Some $ TBit 32%positive
  | _                                  , _                 => None
  end.

(** Expected result type of bop. *)
Definition t_of_bop (op : bop) (l r : t) : option t :=
  match op, l, r with
  | (+{ +  }+ | +{ |+| }+ | +{ -  }+ | +{ |-| }+ |
     +{ ×  }+ | +{  &  }+ | +{ ^  }+ | +{  |  }+ |
     +{ << }+ | +{ >>  }+ | +{ && }+ | +{  ||  }+),
    _, _ => Some l
  | (+{ <= }+ | +{ >= }+ | +{ < }+ | +{ > }+ | +{ == }+ | +{ != }+),
    _, _ => Some {{ Bool }}
  | +{ ++ }+, {{ bit<wl> }}, ({{ bit<wr> }} | {{ int<wr> }})
    => Some $ TBit (wl + wr)%positive
  | +{ ++ }+, {{ int<wl> }}, ({{ bit<wr> }} | {{ int<wr> }})
    => Some $ TInt (wl + wr)%positive
  | _, _, _ => None
  end.

Definition t_of_mem (x : string) (ty : t) : option t :=
  match ty with
  | {{ struct { ts } }}
  | {{ hdr    { ts } }} => F.get x ts
  | _                   => None
  end.

Definition t_of_access (ty : t) : option t :=
  match ty with
  | {{ stack ts[_] }} => Some {{ hdr { ts } }}
  | _                 => None
  end.

Section TofE.
  Context {tags_t : Type}.
  
  (** Syntactic type of an expression. *)
  Fixpoint t_of_e (expr: e tags_t) : option t := 
    match expr with
    | <{ BOOL _   @ _ }> => Some {{ Bool }}
    | <{ w W  _   @ _ }> => Some {{ bit<w> }}
    | <{ w S  _   @ _ }> => Some {{ int<w> }}
    | <{ Var  _:ty @ _ }> => Some ty
    | <{ Cast _:ty @ _ }> => Some ty
    | <{ Slice _ [hi:lo] @ _ }> => Some $ TBit (hi - lo + 1)
    | <{ UOP op e @ _ }> => t_of_e e >>= t_of_uop op
    | <{ BOP e1 op e2 @ _ }> =>
      l <- t_of_e e1;; r <- t_of_e e2;; t_of_bop op l r
    | <{ tup es @ _ }> =>
      ts <<| sequence $ List.map t_of_e es;; {{ tuple ts }}
    | <{ struct { es } @ _ }> =>
      ts <<| sequence $
         List.map (fun '(x,e) => t <<| t_of_e e;; (x,t)) es;;
      {{ struct { ts } }}
    | <{ hdr { es } valid:=_ @ _ }> => 
      ts <<| sequence $
         List.map (fun '(x,e) => t <<| t_of_e e;; (x,t)) es;;
      {{ hdr { ts } }}
    | <{ Mem e dot x @ _ }> => t_of_e e >>= t_of_mem x
    | <{ Error     _ @ _ }> => Some {{ error }}
    | <{ Matchkind _ @ _ }> => Some {{ matchkind }}
    | <{ Stack hs:ts nextIndex:= _ @ _ }> => 
      Some $ THeaderStack ts $ Pos.of_nat $ length hs
    | <{ Access e[_] @ _ }> => t_of_e e >>= t_of_access
    end.
  
  Definition t_of_e_default (default : t) (expr : e tags_t) : t :=
    match t_of_e expr with
    | Some ty => ty
    | None    => default
    end.
End TofE.

(** Restrictions on type-nesting. *)
Module ProperType.
  Import Expr TypeNotations TypeEquivalence.
  
  Section ProperTypeNesting.
    (** Evidence a type is a base type. *)
    Inductive base_type : t -> Prop :=
    | base_bool : base_type {{ Bool }}
    | base_bit (w : positive) : base_type {{ bit<w> }}
    | base_int (w : positive) : base_type {{ int<w> }}.
    
    (** Allowed types within headers. *)
    Inductive proper_inside_header : t -> Prop :=
    | pih_bool (τ : t) :
        base_type τ ->
        proper_inside_header τ
    | pih_struct (ts : F.fs string t) :
        F.predfs_data base_type ts ->
        proper_inside_header {{ struct { ts } }}.
    
    (** Properly nested type. *)
    Inductive proper_nesting : t -> Prop :=
    | pn_base (τ : t) :
        base_type τ -> proper_nesting τ
    | pn_error : proper_nesting {{ error }}
    | pn_matchkind : proper_nesting {{ matchkind }}
    | pn_struct (ts : F.fs string t) :
        F.predfs_data
          (fun τ => proper_nesting τ /\ τ <> {{ matchkind }}) ts ->
        proper_nesting {{ struct { ts } }}
    | pn_tuple (ts : list t) :
        Forall
          (fun τ => proper_nesting τ /\ τ <> {{ matchkind }}) ts ->
        proper_nesting {{ tuple ts }}
    | pn_header (ts : F.fs string t) :
        F.predfs_data proper_inside_header ts ->
        proper_nesting {{ hdr { ts } }}
    | pn_header_stack (ts : F.fs string t)
                      (n : positive) :
        BitArith.bound 32%positive (Zpos n) ->
        F.predfs_data proper_inside_header ts ->
        proper_nesting {{ stack ts[n] }}.
    
    Import F.FieldTactics.
    
    Lemma proper_inside_header_nesting : forall τ,
        proper_inside_header τ ->
        proper_nesting τ.
    Proof.
      intros τ H. induction H.
      - inv H; repeat econstructor.
      - apply pn_struct.
        ind_predfs_data; constructor; auto; cbv.
        inv H; split; try (repeat constructor; assumption);
          try (intros H'; inv H'; contradiction).
    Qed.
  End ProperTypeNesting.
  
  Ltac invert_base_ludicrous :=
    match goal with
    | H: base_type {{ tuple _ }} |- _ => inv H
    | H: base_type {{ struct { _ } }} |- _ => inv H
    | H: base_type {{ hdr { _ } }} |- _ => inv H
    | H: base_type {{ stack _[_] }} |- _ => inv H
    end.
  (**[]*)
  
  Ltac invert_proper_nesting :=
    match goal with
    | H: proper_nesting _
      |- _ => inv H; try invert_base_ludicrous
    end.
  (**[]*)
End ProperType.
