Require Import Coq.Lists.List.

Class Monad (M : Type -> Type) : Type :=
  { mret : forall {A}, A -> M A;
    mbind : forall {A B}, M A -> (A -> M B) -> M B
  }.

Global Hint Unfold mret mbind : core.

(* Adapted from coq-ext-lib *)
(* https://github.com/coq-community/coq-ext-lib/blob/v8.5/theories/Structures/Monad.v*)

Declare Scope monad_scope.
Delimit Scope monad_scope with monad.

Notation "c >>= f" := (@mbind _ _ _ _ c f) (at level 50, left associativity) : monad_scope.
Notation "f =<< c" := (@mbind _ _ _ _ c f) (at level 51, right associativity) : monad_scope.

Notation "x <- c1 ;; c2" := (@mbind _ _ _ _ c1 (fun x => c2))
  ( at level 100, c1 at next level,
    format "x  '<-'  c1 ';;' '//' c2",
    right associativity
  ) : monad_scope.

Notation "e1 ;; e2" := (_ <- e1%monad ;; e2%monad)%monad
  (at level 100, right associativity) : monad_scope.

Notation "'let*' x ':=' c1 'in' c2" := (@mbind _ _ _ _ c1 (fun x => c2))
  ( at level 61, x pattern, 
    format "'let*'  x  ':='  c1  'in' '//' c2", c1 at next level, 
    right associativity
  ) : monad_scope.

Notation "'let*' ' x ':=' c1 'in' c2" := (@mbind _ _ _ _ c1 (fun x => c2))
  ( at level 61, x pattern, 
    format "'let*'  ' x  ':='  c1  'in' '//' c2", c1 at next level, 
    right associativity
  ) : monad_scope.

Open Scope monad.

Fixpoint sequence {A} {m: Type -> Type} {M : Monad m} (acts: list (m A)) : m (list A) := 
  match acts with
  | nil => mret nil
  | x :: xs => 
    let* t    := x in
    let* rest := @sequence A m M xs in 
      mret (t :: rest)
  end.

Definition lift_monad {A B} {m: Type -> Type} {M : Monad m} (f: A -> B) (ma : m A) : m B :=
  ma >>= fun a => mret (f a).

Notation "c '>>|' f" := (lift_monad f c) (at level 50, left associativity) : monad_scope.

Lemma map_bind_pair :
  forall (M : Type -> Type) `{MM: Monad M}
    (T U V W : Type) (f : T -> V) (g : U -> M W) tus,
    List.map (fun '(t,u) => g u >>| pair (f t)) tus =
    List.map
      (fun '(v,ow) => ow >>| @pair V W v)
      (combine (map f (map fst tus)) (map g (map snd tus))).
Proof.
  intros M MM T U V W f g tus.
  induction tus as [| [t u] tus IHtus];
    cbn in *; f_equal; auto.
Qed.

Notation "x '<<|' c1 ;; c2" := (lift_monad (fun x => c2) c1)
  ( at level 100, c1 at next level,
    format "x  '<<|'  c1 ';;' '//' c2",
    right associativity
  ) : monad_scope.

Notation "'let^' x ':=' c1 'in' c2" := (@lift_monad _ _ _ _ (fun x => c2) c1)
  ( at level 61, x pattern, 
    format "'let^'  x  ':='  c1  'in' '//' c2", c1 at next level, 
    right associativity
  ) : monad_scope.

Notation "'let^' ' x ':=' c1 'in' c2" := (@lift_monad _ _ _ _ (fun x => c2) c1)
  ( at level 61, x pattern, 
    format "'let^'  ' x  ':='  c1  'in' '//' c2", c1 at next level, 
    right associativity
  ) : monad_scope.
