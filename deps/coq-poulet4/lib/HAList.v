Require Import Coq.Classes.EquivDec.
Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Equations.Equations.
Import ListNotations.

Set Universe Polymorphism.

Definition signature (K: Type) : Type :=
  list (K * Type).

Section HAList.
  Context {K: Type}.
  Context `{KEqDec: EquivDec.EqDec K eq}.

  Notation signature := (signature K).

  Inductive key : signature -> Type -> Type :=
  | KHd: forall k t s, key ((k, t)::s) t
  | KTl: forall h t s, key s t -> key (h::s) t.

  Inductive t: signature -> Type :=
  | REmp: t []
  | RCons: forall {k typ rest} (x:typ),
      t rest ->
      t ((k, typ)::rest).

  Equations get_k {T} {sig: signature} : t sig -> key sig T -> T :=
    {
      get_k (RCons val _) (KHd _ _ _)     := val;
      get_k (RCons _ rec') (KTl _ _ _ pf) := get_k rec' pf
    }.

  Equations set_k {T} {sig: signature} : t sig -> key sig T -> T -> t sig :=
    {
      set_k (RCons val rec) (KHd _ _ _) val'     := RCons val' rec;
      set_k (RCons val rec') (KTl _ _ _ pf) val' := RCons val (set_k rec' pf val')
    }.

  Inductive key_exists : signature -> K -> Type :=
  | KEHd: forall k t sig', key_exists ((k, t)::sig') k
  | KETl: forall k h sig', key_exists sig' k -> key_exists (h::sig') k.

  Equations get_key_type {sig: signature} {k: K} : key_exists sig k -> {T: Type & key sig T} :=
    {
      get_key_type (KEHd k t sig') := existT (key ((k, t)::sig')) t (KHd k t _);
      get_key_type (KETl k h sig' ke') :=
        let '(existT _ t key_rest) := get_key_type ke' in
        existT (key (h::sig')) t (KTl h t _ key_rest)
    }.

  Fixpoint alist_In {A} (k: K) (l: list (K * A)) :=
    match l with
    | (k0, x0) :: l =>
      if KEqDec k0 k
      then True
      else alist_In k l
    | [] => False
    end.

  Definition valid_key {A} (l: list (K * A)) :=
    {k: K | alist_In k l}.

  Definition mk_key {sig: signature} (k: valid_key sig) : key_exists sig (proj1_sig k).
  Proof.
    induction sig as [|[k' T] sig].
    - cbv in k.
      exfalso.
      exact (proj2_sig k).
    - destruct k as [k HIn].
      pose proof (g := HIn).
      simpl in g.
      destruct (KEqDec k' k).
      + unfold equiv in *.
        subst.
        apply KEHd.
      + apply KETl.
        set (Hvalid := exist (fun k => alist_In k sig) k g).
        specialize (IHsig Hvalid).
        eauto.
  Defined.

  Definition get {sig: signature} (rec: t sig) (k: valid_key sig) : (projT1 (get_key_type (mk_key k))) :=
    get_k rec (projT2 (get_key_type (mk_key k))).

  Definition set {sig: signature} (rec: t sig) (k: valid_key sig) (v: (projT1 (get_key_type (mk_key k)))) : t sig :=
    set_k rec (projT2 (get_key_type (mk_key k))) v.

End HAList.
