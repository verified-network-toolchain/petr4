From Coq Require Import
     NArith
     String
     Classes.EquivDec.
From ITree Require Import
     ITree
     Events.Exception
     Events.MapDefault
     Events.FailFacts.
From Poulet4 Require Import
     TLang.
From ExtLib Require Import
     Structures.Monad
     Data.Monads.EitherMonad
     Data.String
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

Inductive value :=
| VBool (b : bool)
| VInt (i : p4int).

(*TODO put this with p4int's definition *)
Global Instance EqDec_p4int : EqDec p4int eq.
red.
intros [xw xv] [yw yv].
destruct (xw == yw).
- destruct (xv == yv).
  + left.
    unfold equiv in *.
    congruence.
  + right.
    intro.
    unfold equiv in *.
    congruence.
- right.
  intro.
  unfold equiv in *.
  congruence.
Defined.

Global Instance EqDec_value : EqDec value eq.
red. unfold Equivalence.equiv, RelationClasses.complement.
intros x y.
change (x = y -> False) with (~(x = y)).
decide equality.
apply Bool.bool_dec.
apply EqDec_p4int.
Defined.

Inductive err :=
| TypeError
| Unimplemented.

Inductive Store : Type -> Type :=
| GetVar (x : string) : Store value
| SetVar (x : string) (v : value) : Store unit.

Section Denote.
  Context {eff : Type -> Type}.
  Context {HasStore : Store -< eff}.
  Context {HasException : exceptE err -< eff}.

  Definition get_bool (v : value) : itree eff bool :=
    match v with
    | VBool b => ret b
    | _       => throw TypeError
    end.

  Definition get_int (v : value) : itree eff p4int :=
    match v with
    | VInt i  => ret i
    | _       => throw TypeError
    end.

  Definition get_val (res : value + unit) : itree eff value :=
    match res with
    | inl v => ret v
    | _     => throw TypeError
    end.

  (* The type tm is really expr + stmt due to egg's single-sort
  restriction so we return value + unit here. *)
  Fixpoint denote_tm (t : tm) : itree eff (value + unit) :=
    match t with
    | TBool b => ret (inl (VBool b))
    | TInt i => ret (inl (VInt i))
    | TEq e1 e2 =>
        v1 <- denote_tm e1 >>= get_val;;
        v2 <- denote_tm e2 >>= get_val;;
        ret (inl (VBool (v1 ==b v2)))
    | TIf e1 c1 c2 =>
        b <- denote_tm e1
             >>= get_val
             >>= get_bool;;
        if (b : bool)
        then denote_tm c1
        else denote_tm c2
    | TAnd e1 e2 =>
        b1 <- denote_tm e1
              >>= get_val
              >>= get_bool;;
        b2 <- denote_tm e2
              >>= get_val
              >>= get_bool;;
        ret (inl (VBool (b1 && b2)))
    | TNot e1 =>
        b <- denote_tm e1
             >>= get_val
             >>= get_bool;;
        ret (inl (VBool (negb b)))
    | TVar x =>
        v <- trigger (GetVar x);;
        ret (inl v)
    | TSet x c =>
        v <- denote_tm c
             >>= get_val;;
        trigger (SetVar x v);;
        ret (inr tt)
    | TSeq c1 c2 =>
        _ <- denote_tm c1;;
        _ <- denote_tm c2;;
        ret (inr tt)
    | TNop =>
        ret (inr tt)
    end.
  
End Denote.

(** These enable typeclass instances for Maps keyed by strings and values *)
Instance RelDec_string : RelDec (@eq string) :=
  { rel_dec := fun s1 s2 => if string_dec s1 s2 then true else false}.

Instance RelDec_string_Correct: RelDec_Correct RelDec_string.
Proof.
  constructor; intros x y.
  split.
  - unfold rel_dec; simpl.
    destruct (string_dec x y) eqn:EQ; [intros _; apply string_dec_sound; assumption | intros abs; inversion abs].
  - intros EQ; apply string_dec_sound in EQ; unfold rel_dec; simpl; rewrite EQ; reflexivity.
Qed.
(* end hide *)

Definition handle_Store {E: Type -> Type} `{@mapE string value (VBool false) -< E}: Store ~> itree E :=
  fun _ e =>
    match e with
    | GetVar x => lookup_def x
    | SetVar x v => insert x v
    end.

Definition sumT (E : Type) (M : Type -> Type) :=
  fun (T : Type) => M (sum E T).

Instance Functor_sumT
         (E : Type)
         (M : Type -> Type)
         `{Functor.Functor M}
  : Functor.Functor (sumT E M)
  := {| Functor.fmap A B f :=
          Functor.fmap (FunUtil.map_sum id f) |}.

Instance Monad_sumT
         (E : Type)
         (M : Type -> Type)
         `{Monad M}
  : Monad (sumT E M).
Admitted.

Instance MonadIter_sumT
         (E : Type)
         (M : Type -> Type)
         `{MonadIter M}
  : MonadIter (sumT E M).
Admitted.

Definition pure_sum (err : Type) (E : Type -> Type) (T : Type) (e : E T) : itree E (err + T) :=
  Vis e (fun x => Ret (inr x)).

Definition handle_exceptE (err : Type) (E : Type -> Type) (T : Type) :
  exceptE err T -> sumT err (itree E) T :=
  fun ev =>
    match ev in exceptE _ _ return itree E (err + T) with
    | Throw err => ret (inl err)
    end.

Definition store := alist string value.

Definition interp_store {A eff} (t : itree (Store +' eff) A) : stateT store (itree eff) A :=
  let t' := interp (bimap handle_Store (id_ eff)) t in
  interp (case_ (handle_map (V:=value)) State.pure_state) t'.

Definition interp_except
           (eff : Type -> Type)
           (A : Type)
           (t : itree (exceptE err +' eff) A)
           : sumT err (itree eff) A :=
  interp (case_ (handle_exceptE err eff) (pure_sum err eff)) t.
Eval compute in (stateT store (sumT err (itree void1)) unit).

Definition interp_tm {eff : Type -> Type} (A : Type) (t : itree (exceptE err +' Store +' eff) A) : sumT err (stateT store (itree eff)) A :=
  interp_store (interp_except _ _ t).

Definition eval_tm (t : tm) : itree void1 (store * (err + (value + unit))) :=
  interp_tm _ (denote_tm t) empty.
