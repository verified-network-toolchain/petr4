Require Import Poulet4.Monads.Monad.

Open Scope monad.
Open Scope list_scope.


Definition error_monad {Error Result: Type} :=
  (Result + Error)%type.

Definition error_ret {E R: Type} (r: R) : @error_monad E _ := inl r.

Definition err {E R: Type} (e: E) : @error_monad _ R := inr e.


Definition error_bind {E A B: Type} (c: @error_monad E A) (f: A -> @error_monad E B) : error_monad :=
  match c with
  | inl a => f a
  | inr b => inr b
  end.

Global Instance error_monad_inst {Error: Type} : Monad (@error_monad Error) :=
  { mret := @error_ret Error;
    mbind := @error_bind Error;
  }.

Definition error_map {E A B : Type} (c: @error_monad E A) (f: A -> B) : @error_monad E B :=
  match c with 
  | inl a => inl (f a)
  | inr b => inr b
  end.

Definition lift_opt_error {Error Result: Type} (e: Error) (x: option Result) : @error_monad Error Result :=
  match x with 
  | Some x' => mret x'
  | None => err e
  end.

Definition strip_error {Error Result: Type} (x: @error_monad Error Result) : option Result := 
  match x with 
  | inl x' => Some x'
  | inr _ => None
  end.

Hint Unfold error_ret error_bind : core.
