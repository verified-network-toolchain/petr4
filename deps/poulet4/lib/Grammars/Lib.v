Require Import Ascii.
Require Import Coq.Lists.List.
Require Import Grammar.
Require Import Strings.String.
Require Import Vector.
Require Import Bool.


Infix "$" := (Times_g) (at level 100).
Infix "<$" := (Times_l) (at level 100).
Infix "$>" := (Times_r) (at level 100).
Infix "<|>" := (Plus_g) (at level 100).
Notation "g >= f" := (Bind_g g f) (at level 70).
Notation "a @ f" := (Map_g a f) (at level 110).
Notation "g ?" := (option_g g) (at level 90).
Infix "<||>" := (fun l r => (l @ inl) <|> (r @ inr)) (at level 100).

Lemma inv_Map_g {T U: Set} s v (g: grammar T) (f: T -> U) (v': T):
   matches (g @ f) s v -> exists v', matches g s v' /\ f v' = v.
Proof.
  admit.
Admitted.

Definition filter {T: Set} (g:grammar T) (pred : T -> bool) : grammar T :=
  (g >= (fun v => if pred v then One_g else gzero)) @ (fun x => projT1 x).

Lemma matches_filter {T} (g:grammar T) (pred : T -> bool) s v :
  matches (filter g pred) s v <-> matches g s v /\ pred v = true.
Proof.
  unfold filter. split ; intro.
  myinv H. clear H. rewrite inv_Bind_g in H5.
  unfold filter. split ; 
  destruct H5 as [s1 [s2 [v1 [v2 [H1 [H2 [H3 H4]]]]]]]. subst.
  destruct (pred v1). myinv H2. rewrite <- app_nil_end. auto.
  contradiction (not_matches_gzero _ _ H2).
  rewrite H4.
  simpl projT1.
  induction (pred v1). reflexivity.
  contradiction (not_matches_gzero _ _ H2).
  destruct H. 
  eapply (m_Map_g (Bind_g g (fun v => if pred v then One_g else gzero)) s (existT _ v tt)).
  replace (s) with (s ++ List.nil). econstructor. auto. rewrite H0. eauto. 
  rewrite app_nil_end. auto.
Qed.

Fixpoint prod (T:Set) (n:nat) : Set :=
  match n with
    | 0   => unit
    | S m => T * (prod T m)
  end.
  
Definition whitespace : grammar ascii := glit "032" <|> glit "000" <|> glit "009" <|> glit "012" <|> glit "010" <|> glit "013".

Definition gplus {A} (g:grammar A) := g $ (gstar g) @ fun p => (fst p)::(snd p).

Definition ret {T: Set} (t: T) : grammar T := gone @ fun _ => t.
Definition glitr {T: Set} (c: ascii) (t: T) := glit c @ fun _ => t.


Lemma match_ret {T:Set} {v: T} :
  matches (ret v) List.nil v.
Proof.
  unfold ret.
  eapply (m_Map_g gone List.nil tt). auto.
Qed.

Fixpoint gprod {A S: Set} (f: A -> S -> S) (gs : list (grammar A)) (base : S) : grammar S :=
  match gs with
  | List.nil => gone @ fun _ => base
  | g::gs' => g $ (gprod f gs' base) @ fun p => let (a', s) := p in f a' s
  end.  

Lemma matches_times {A B: Set} (g1: grammar A) (g2: grammar B) s1 v1 s2 v2:
  matches g1 s1 v1 /\ matches g2 s2 v2 -> matches (g1 $ g2) (s1 ++ s2) (v1, v2).
Proof.
  intros. 
  destruct H as [H1 H2].
  apply matches_Times_g.
  exists s1. exists s2. simpl. 
  split. auto.
  split. auto.
  auto.
Qed.


Definition gstr (str: string) := gprod List.cons (List.map glit (list_ascii_of_string str)) List.nil.

Lemma match_gstr s : 
  matches (gstr s) (list_ascii_of_string s) (list_ascii_of_string s).
Proof.
  
  induction s. 
  unfold gstr.
  unfold gprod. simpl. apply match_ret.
  simpl. unfold gstr. unfold gprod. simpl. 
  unfold gstr in IHs. unfold gprod in IHs.
  remember ((fix gprod
  (A S : Set) (f : A -> S -> S) (gs : list (grammar A)) 
  (base : S) {struct gs} : grammar S :=
  match gs with
  | Datatypes.nil => gone @ (fun _ : unit => base)
  | g :: gs' =>
      g $ gprod A S f gs' base @
      (fun p : A * S => let (a', s) := p in f a' s)
  end) ascii (list ascii) Datatypes.cons
 (List.map glit (list_ascii_of_string s)) Datatypes.nil) as g2.

  pose proof (m_Lit_g a) as mlit.
  remember (Lit_g a) as g1.

  pose proof (matches_times g1 g2) as mtimes.
  specialize (mtimes (a :: Datatypes.nil) a (list_ascii_of_string s) (list_ascii_of_string s)).
  remember (conj mlit IHs) as mtimes_arg.
  specialize (mtimes mtimes_arg). clear Heqmtimes_arg. clear mtimes_arg.
  unfold glit.
  rewrite <- Heqg1. 
  rewrite <- app_comm_cons in mtimes. 
  rewrite app_nil_l in mtimes. 
  apply (m_Map_g (g1 $ g2) (a :: list_ascii_of_string s) (a, list_ascii_of_string s) (fun p : ascii * list ascii => let (a', s0) := p in a' :: s0)) in mtimes.
  auto.
  
Qed.

Lemma match_gstr_uniq s v1 v2 v3: 
  matches (gstr s) v1 v1 /\ matches (gstr s) v2 v3 -> v1 = v2 /\ v2 = v3.
Proof.
  intros.
  induction s. unfold gstr in H. unfold list_ascii_of_string in H. simpl.
  unfold List.map in H. simpl.
  destruct H as [H1 H2].
  apply inv_Map_g in H1.
  apply inv_Map_g in H2.
  destruct H1 as [u1 [mv1 v1eq]].
  destruct H2 as [u2 [mv2 v3eq]].

  rewrite <- v1eq. rewrite <- v3eq.
  myinv mv2. auto.
  remember tt as u. auto.
  remember tt as u. auto.

  destruct H as [H1 H2].
  myinv H1. myinv H2. simpl. fold (gstr s) in H6.
  fold (gstr s) in H7. myinv H6. apply inv_Bind_g in H8. simpl.

  destruct H8 as [s1 [s2 [v2' [v3 [Bod]]]]].


  unfold gprod in H. simpl.
  myinv H. myinv H0.
  destruct v1. destruct v2. destruct v3. auto. auto.
  unfold List.map in H.
  admit.
Admitted.


Fixpoint repeat {T: Set} (n: nat) (g: grammar T) : grammar (Vector.t T n) := 
  match n return grammar (Vector.t T n) with 
    | 0     => ret (nil T)
    | (S x) => g $ repeat x g @ (fun p => let (h, t) := p in Vector.cons _ h _ t)
  end.

Definition vec2prod {T: Set} (n: nat) (xs: Vector.t T n) : prod T n. 
Admitted.

Definition repeat_prod {T: Set} (n: nat) (g: grammar T) : grammar (prod T n) :=
  repeat n g @ (vec2prod n).

Definition filt_vec {T: Set} {n} (g: grammar (Vector.t T n)) (pred: T -> bool) : grammar (Vector.t T n) :=
  filter g (fun row => fold_left andb true (map pred row))
.

Lemma lift_Forall {T: Set} {n} (vect: Vector.t T n) (pred : T -> bool) :
  fold_left andb true (map pred vect) = true <-> Forall (fun t => Is_true (pred t)) vect
.
Proof.
  admit.
Admitted.

Theorem matches_filt_vec {T: Set} {n} (g:grammar (Vector.t T n)) (pred : T -> bool) s v :
  matches (filt_vec g pred) s v <-> matches g s v /\ Forall (fun t => Is_true (pred t)) v.
Proof.
  split. intros. apply matches_filter in H.
  destruct H as [H1 H2].
  split. auto.
  apply lift_Forall. auto.
  intros.
  myinv H. clear H. unfold filt_vec.
  rewrite <- lift_Forall in H1.
  apply matches_filter. auto.
Qed.

Lemma opt_eq {A} (x: option A) (y: option A) a b:
  x = Some a /\ y = Some b -> a = b.
Proof.
  admit.
Admitted.

Lemma list_cons_hdeq {T} (h1: T) tl1 (h2: T) tl2:
  h1 :: tl1 = h2 :: tl2 -> h1 = h2 /\ tl1 = tl2.
Proof.
  intros.
  pose proof f_equal as feq.
  specialize (feq (list T) (option T) (@List.hd_error T) (h1 :: tl1) (h2 :: tl2)).
  (* remember H as H'. *)
  apply feq in H as H'. clear feq.
  unfold hd_error in H'. simpl.
  split.
  
  remember (Some h1) as x.
  remember (Some h2) as y.
  pose proof (opt_eq x y) as opt_eq.
  specialize (opt_eq h1 h2).

  specialize (opt_eq (conj Heqx Heqy)). auto.

  pose proof f_equal as feq.
  specialize (feq (list T) (list T) (@List.tl T) (h1 :: tl1) (h2 :: tl2)).
  apply feq in H.
  auto.
Qed.

Lemma vect_tolist_cons T h n tl:
  to_list (Vector.cons T h n tl) = List.cons h (to_list tl).
Proof.
  unfold to_list. auto.
Qed.

Lemma vsize_z {T} (v: t T 0) :
  v = nil T.
Proof.
  admit.
Admitted.

Lemma to_list_inj {T} n (v1: t T n) (v2: t T n):
  to_list v1 = to_list v2 -> v1 = v2.
Proof.
  admit.
Admitted.


Lemma vect_cons_eq T n h1 h2 tl1 tl2:
  cons T h1 n tl1 = cons T h2 n tl2 -> h1 = h2 /\ tl1 = tl2.
Proof.
  intros. pose proof f_equal as feq.

  specialize (feq (t T (S n)) (list T) to_list (cons T h1 n tl1) (cons T h2 n tl2)).
  apply feq in H.
  rewrite vect_tolist_cons in H.
  rewrite vect_tolist_cons in H.

  apply list_cons_hdeq in H.
  destruct H as [heq tleq].
  apply to_list_inj in tleq.
  split. auto. auto.
Qed.

Lemma repeat_prefix {T: Set} (gi: grammar T) (hd: T) s n tail:
  matches (repeat (S n) gi) s (Vector.cons T hd n tail) -> 
  exists s1 s2, s1 ++ s2 = s /\ matches gi s1 hd /\ matches (repeat n gi) s2 tail.
Proof.
  intros. 
  myinv H. apply matches_Times_g in H5.
  destruct H5 as [s1 [s2 [msv [mstl s12eq]]]].
  exists s1. exists s2.
  split. auto.
  remember (fst v, snd v) as v'.
  assert (v = v').
  rewrite Heqv'. apply surjective_pairing. 
  rewrite <- H1 in Heqv'.
  rewrite Heqv' in H0.
  simpl. split.

  apply vect_cons_eq in H0.
  destruct H0 as [fvh svtl].
  rewrite <- fvh. assumption.

  apply vect_cons_eq in H0.
  destruct H0 as [fvh svtl].
  rewrite <- svtl. assumption.
Qed.

Lemma repeat_filter {T: Set} (g : grammar T) s (f: T -> bool) l (v: Vector.t T l):
  matches (repeat l (filter g f)) s v <-> matches (filter (repeat l g) (fun x => fold_left andb true (map f v))) s v.
Proof.
  split. intros.
  myinv H.
  (* apply matches_filter in H. *)
  admit.
Admitted.

Lemma false_fold n (v: Vector.t bool n):
  fold_left andb false v = false.
Proof.
  induction v.
  unfold fold_left. auto.
  unfold fold_left. simpl. fold (fold_left andb false v).
  auto.
Qed.

Lemma is_true_fold x n (v: Vector.t bool n):
  Is_true (fold_left andb (true && x) v) <-> Is_true (fold_left andb true v) /\ Is_true x.
Proof.
  split.
  intros. induction v. unfold fold_left. simpl. auto.
  unfold fold_left in H. simpl. fold (fold_left andb) in H.
  rewrite andb_true_l in H. rewrite andb_true_l in IHv.
  destruct x. split.
  rewrite andb_true_l in H. assumption. unfold Is_true. auto.
  rewrite false_fold in H. unfold Is_true in H.
  contradiction.
  intros. destruct H as [truf itru].
  destruct x. simpl. auto.
  contradiction.
Qed.

Lemma is_true_vect f n h (v: Vector.t nat n):
  Is_true (fold_left andb true (map f (cons nat h n v))) ->
  Is_true (f h) /\ Is_true (fold_left andb true (map f v)).
Proof.
  intros. induction v. simpl. split.
  unfold map in H. unfold fold_left in H. simpl. auto. auto.

  unfold map in H. unfold fold_left in H. simpl.
  fold (map f v) in H.
  fold (fold_left andb (true && f h && f h0) (map f v)) in H.
  pose proof (is_true_fold (f h && f h0) n (map f v)) as itiff.
  destruct itiff as [itf itfr].
  specialize (itf H).
  destruct itf as [rem it].
  auto.
  apply andb_prop_elim in it. destruct it as [itt ith0].

  split.
  auto.

  pose proof (is_true_fold (f h0) n (map f v)) as recpf.
  destruct recpf as [_ recpfrev].
  specialize (recpfrev (conj rem ith0)). auto.
Qed.

Lemma push_is_true f n (v: Vector.t nat n):
  Is_true (fold_left andb true (map f v)) -> Forall (fun x: nat => Is_true (f x)) v.
Proof.
  intros. induction v. apply Forall_nil.
  apply is_true_vect in H. destruct H as [pfh pftl].
  specialize (IHv pftl).
  apply Forall_cons. auto. auto.
Qed.

Fixpoint between_helper (base: nat) (remainder: nat) : grammar ascii := match remainder with
  | 0   => Lit_g (ascii_of_nat base)
  | S x => Lit_g (ascii_of_nat base) <|> between_helper (S base) x
end.

Definition between (lo: ascii) (hi: ascii) : grammar ascii := 
  between_helper (nat_of_ascii lo) ((nat_of_ascii hi) - (nat_of_ascii lo)).

Definition Choose {A B} (proj : A -> grammar B) (choices: list A) : grammar B := gsum (List.map proj choices).

Definition Star_Bound {A} (n: nat) (g: grammar A): grammar (list A) := filter (Star_g g) (fun xs => Nat.leb n (List.length xs)). 
(* Definition Many {A} (g: grammar A)  *)

Definition any : grammar ascii := between "000" "255".