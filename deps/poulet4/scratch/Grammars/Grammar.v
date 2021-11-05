(* 
   Parsing with dependent regular expressions.  Here, we add a dependently typed Bind operator
   for regular expressions that subsumes the usual concatenation (multiplication) operator and
   allows for grammars of the form (g >>= f) where f can depend upon the result returned by g.

   This allows us to define some gramamrs, such as parsing a number n, followed by n copies
   of something (e.g., a packet header followed by a payload whose length is determined by
   the header.)  Another example is parsing only strings that return values that satisfy some
   predicate.  Both are given as examples at the end.  

   What's fascinating about this is that we can use a derivative-based approach for this.  
   Critical is the fact that for any grammar g, we can calculate the (finite) list of values 
   [v1,v2,...,vn] such that g associates the empty list with one of these values.  

   Note, however, that we must make a slight restriction on the semantics of Kleene-star
   so that we have:

        matches (Star g) nil nil 

        matches (Star g) s v if s = s1++s2, v = v1::v2, matches g s1 v1,
                                matches (Star g) s2 v2, and most importantly,
                                s1 <> nil

   The s1<>nil is crucial for ensuring that we only have a finite set of values associated
   with the empty string by any grammar.  Without this restriction, we can't calculate derivatives
   as finite grammars.  (We'd need an infinite sum.)  For instance, consider the grammar

       Star One

   Without the non-empty restriction, we can get nil, tt::nil, tt::tt::nil, tt::tt::tt::nil, ...
   matching the empty list. 

   We can define concatenation (Times) in terms of Bind.  It's also interesting
   that to be effective, the Bind needs to return a dependent pair (see the packet example
   at the end.)  

*)

Require Import Ascii.
Require Import Coq.Lists.List.
Require Import Eqdep.

Ltac depinv := 
  match goal with
  | [ H : existT _ ?T _ = existT _ ?T _ |- _ ] => generalize (inj_pair2 _ _ _ _ _ H) ; clear H ; intro
  end.

Ltac myinv H := inversion H ; subst ; repeat depinv ; subst.

Inductive void : Set := .

Definition Token : Set := bool.
Definition Tok_dec : forall a b: Token, {a = b} + {a <> b} := Bool.bool_dec.
                                                             
Inductive grammar : Set -> Type :=
| Zero_g : grammar void  (* matches nothing *)
| One_g : grammar unit  (* matches empty string, returns unit *)
| Lit_g : Token -> grammar Token (* matches single character and returns it *)
| Plus_g : forall {A:Set}, grammar A -> grammar A -> grammar A (* alternation *)
| Star_g : forall {A:Set}, grammar A -> grammar (list A) (* kleene star *)
| Map_g : forall {A B:Set}, grammar A -> (A->B) -> grammar B (* fmap for grammars *)
| Bind_g : forall {A:Set} {F:A->Set}, grammar A -> (forall (x:A), grammar (F x)) -> grammar {x:A & F x}.
   (* Bind -- note that this returns a dependent pair *)


(* The semantics as a relation between strings (list Token) and values. *)
Inductive matches : forall {T}, grammar T -> list Token -> T -> Prop :=
| m_One_g : matches One_g nil tt
| m_Lit_g : forall c, matches (Lit_g c) (c::nil) c
| m_l_Plus_g : forall {A:Set} (g1 g2:grammar A) s v, matches g1 s v -> matches (Plus_g g1 g2) s v
| m_r_Plus_g : forall {A:Set} (g1 g2:grammar A) s v, matches g2 s v -> matches (Plus_g g1 g2) s v
| m_l_Star_g : forall {A:Set} (g:grammar A), matches (Star_g g) nil nil
| m_r_Star_g : forall {A:Set} (g:grammar A) s1 s2 v1 v2, matches g s1 v1 -> s1 <> nil ->
                                                         matches (Star_g g) s2 v2 ->
                                                         matches (Star_g g) (s1 ++ s2) (v1::v2)
| m_Map_g : forall {A B:Set} (g:grammar A) s v (f:A->B), matches g s v -> matches (Map_g g f) s (f v)
| m_Bind_g : forall {A:Set} {F:A->Set} (g:grammar A) (f : forall x, grammar (F x)) s1 s2 v1 v2,
    matches g s1 v1 -> matches (f v1) s2 v2 -> matches (Bind_g g f) (s1 ++ s2) (existT _ v1 v2).
Hint Constructors matches : core.

(* Some smart constructors that simplify grammars. Correctness is established below. *)
Definition gzero {S:Set} : grammar S := Map_g Zero_g (fun v => match v with end).
Definition gone := One_g.
Definition glit (c:Token) := Lit_g c.

Fixpoint gmap {A:Set} (g:grammar A) : forall {B:Set}, (A -> B) -> grammar B :=
  match g in grammar A' return forall {B:Set}, (A' -> B) -> grammar B with
  | Zero_g => fun B f => gzero
  | One_g => fun B f => let v := f tt in Map_g One_g (fun x => v)  (* note partial eval *)
  | Map_g g f1 => fun B f2 => gmap g (fun x => f2 (f1 x))
  | g' => fun B f => Map_g g' f
  end.

Definition isZero {A} (g:grammar A) : bool :=
  match g with
  | Zero_g => true
  | Map_g g1 f =>
    match g1 with
    | Zero_g => true
    | _ => false
    end
  | _ => false
  end.

Definition gplus {A} (g1:grammar A) (g2:grammar A) : grammar A :=
  if isZero g1 then g2
  else if isZero g2 then g1
       else Plus_g g1 g2.

Definition isMapOne {A} (g:grammar A) : option (unit -> A) := 
  match g with
  | Map_g g1 f =>
    match g1 with
    | One_g => fun f => Some f
    | _ => fun _ => None
    end f
  | One_g => Some (fun x => tt)
  | _ => None
  end.

Definition gbind {A F} (g:grammar A) : (forall (x:A), grammar (F x)) -> grammar { x:A & F x } := 
  if isZero g then fun f => gzero
  else match isMapOne g with
       | Some f' => fun f => Map_g (f (f' tt)) (fun x => existT _ _ x)
       | None => fun f => Bind_g g f
       end.

Definition Times_g {A B} (g1:grammar A) (g2:grammar B) : grammar (A*B) :=
  gmap (@gbind A (fun x => B) g1 (fun x => g2)) (fun p => match p with
                                                          | existT _ x y => (x,y)
                                                          end).

Lemma not_matches_gzero : forall {T:Set} s (v:T), ~ matches gzero s v.
Proof.
  intros ; intro. unfold gzero in H. inversion H ; subst ; repeat depinv ; subst.
  inversion H5.
Qed.

Lemma not_matches_isZero : forall {T:Set} (g:grammar T) s (v:T), true = isZero g -> ~ matches g s v.
Proof.
  destruct g ; simpl ; intros ; intro ; try discriminate.
  inversion H0. destruct g ; try discriminate. inversion H0 ; subst ; repeat depinv ; subst.
  inversion H6.
Qed.

Lemma inv_Bind_g1 {A} (g:grammar A) s v : 
  matches g s v ->
  match g in grammar A' return A' -> Prop with
  | @Bind_g B F g1 f =>
    fun (v': { x: B & F x}) => exists s1, exists s2, exists v1, exists v2,
              matches g1 s1 v1 /\ matches (f v1) s2 v2 /\
              s = s1 ++ s2 /\ v' = (existT _ v1 v2)
  | _ => fun v' => True
  end v.
Proof.
  induction 1 ; auto.
  clear IHmatches1 IHmatches2.
  exists s1. exists s2.
  exists v1. exists v2. split ; auto.
Qed.
  
Lemma inv_Bind_g {A F} (g:grammar A) (f:forall x:A, grammar (F x)) s v :
  matches (Bind_g g f) s v <->
  exists s1, exists s2, exists v1, exists v2,
          matches g s1 v1 /\
          matches (f v1) s2 v2 /\
          s = s1 ++ s2 /\
          v = (existT F v1 v2).
Proof.
  split.
  intro. generalize (inv_Bind_g1 _ _ _ H). auto.
  intros. destruct H as [s1 [s2 [v1 [v2 [H1 [H2 [H3 H4]]]]]]]. subst.
  eauto.
Qed.
  
Lemma matches_gbind {A F} (g:grammar A) (f : forall x:A, grammar (F x)) s v : 
  matches (gbind g f) s v <-> matches (Bind_g g f) s v.
Proof.
  unfold gbind.
  remember (isZero g). destruct b. split ; intro.
  contradiction (not_matches_gzero _ _ H).
  destruct v.
  rewrite inv_Bind_g in H.
  destruct H as [s1 [s2 [v1 [v2 [H1 [H2 [H3 H4]]]]]]].
  contradiction (not_matches_isZero g s1 v1 Heqb).
  remember (isMapOne g) as x.
  destruct x ; try tauto.
  destruct g ; try discriminate.
  injection Heqx ; intros ; subst. clear Heqb Heqx.
  destruct v. destruct x.
  split ; intro.
  myinv H. clear H. depinv. subst.
  rewrite inv_Bind_g. exists nil. exists s. exists tt. exists f0. auto.
  rewrite inv_Bind_g in H. destruct H as [s1 [s2 [v1 [v2 [H1 [H2 [H3 H4]]]]]]].
  myinv H1. clear H1. simpl. econstructor. depinv. subst ; auto.
  destruct g ; try discriminate. simpl in *. clear Heqb.
  injection Heqx ; intros ; subst. clear Heqx.
  rewrite inv_Bind_g. split ; intros.
  myinv H. clear H. exists nil. exists s. exists (b tt). exists v0. auto.
  destruct H as [s1 [s2 [v1 [v2 [H1 [H2 [H3 H4]]]]]]]. subst.
  myinv H1. clear H1. myinv H6. clear H6. simpl.
  eauto.
Qed.
  
Lemma matches_gmap : forall {T1 T2:Set} (g:grammar T1) (f:T1 -> T2) s v,
    matches (gmap g f) s v <-> matches (Map_g g f) s v.
Proof.
  induction g ; simpl ; intros ; split ; intros ; auto.
  contradiction (not_matches_gzero _ _ H).
  inversion H ; subst ; repeat depinv ; subst. inversion H5.
  inversion H ; subst ; repeat depinv ; subst. inversion H5 ; eauto.
  inversion H ; subst ; repeat depinv ; subst.
  inversion H5 ; subst ; repeat depinv ; subst.
  apply (m_Map_g One_g nil tt (fun _ => f tt)). auto.
  rewrite IHg in H. inversion H ; subst ; repeat depinv ; subst. clear H.
  eauto. rewrite IHg. inversion H ; subst ; repeat depinv ; subst ; clear H.
  inversion H5 ; subst ; repeat depinv ; subst; clear H5.
  apply (m_Map_g g s v (fun x : A => f (b x))). auto.
Qed.

Lemma matches_Times_g {A B} (g1:grammar A) (g2:grammar B) s v : 
  matches (Times_g g1 g2) s v <-> exists s1, exists s2, matches g1 s1 (fst v) /\ matches g2 s2 (snd v) /\ s = s1++s2.
Proof.
  unfold Times_g. split ; intro.
  rewrite matches_gmap in H.
  myinv H ; clear H.
  rewrite matches_gbind in H5. rewrite inv_Bind_g in H5.
  destruct H5 as [s1 [s2 [v1 [v2 [H1 [H2 [H3 H4]]]]]]]. subst.
  exists s1. exists s2. split ; auto.
  destruct H as [s1 [s2 [H1 [H2 H3]]]]. subst. destruct v ; simpl in *.
  rewrite matches_gmap.
  eapply (m_Map_g (gbind g1 (fun _:A => g2)) (s1++s2) (existT _ a b) (fun p => let (x,y) := p in (x,y))).
  rewrite matches_gbind. rewrite inv_Bind_g.
  exists s1. exists s2. exists a. exists b. eauto.
Qed.

Fixpoint gtimes2 {A} (g1:grammar A) {B} (g2:grammar B) :=
  match g2 in grammar B' return grammar (A*B') with
  | Zero_g => gzero
  | One_g => gmap g1 (fun x => (x,tt))
  | Map_g g2' f => gmap (gtimes2 g1 g2') (fun x => (fst x, f (snd x)))
  | g2' => Times_g g1 g2'
  end.

Fixpoint gtimes {A} (g1:grammar A) :
  forall {B}, grammar B -> grammar (A * B) :=
  match g1 in grammar A' return forall {B}, grammar B -> grammar (A' * B)
  with
  | Zero_g => fun {B} (g2:grammar B) => gzero
  | One_g => fun {B} (g2:grammar B) => gmap g2 (fun x => (tt,x))
  | Map_g g1' f => fun B g2 => gmap (gtimes g1' g2) (fun x => (f (fst x), snd x))
  | g1' => fun {B} g2 => gtimes2 g1' g2
  end.

Lemma matches_gtimes2 {A B} (g1:grammar A) (g2:grammar B) s v :
  matches (gtimes2 g1 g2) s v <-> matches (Times_g g1 g2) s v.
Proof.
  induction g2 ; simpl ; split ; intro ; auto.
  destruct v.  destruct v.
  rewrite matches_Times_g in H.
  destruct H as [s1 [s2 [H1 [H2 H3]]]]. inversion H2.
  rewrite matches_gmap in H. myinv H ; clear H.
  eapply matches_Times_g. exists s. exists nil. simpl.
  split ; eauto. split ; eauto. rewrite <- app_nil_end. auto.
  rewrite matches_Times_g in H.
  destruct H as [s1 [s2 [H1 [H2 H3]]]]. inversion H2.
  subst. clear H2. depinv. destruct v.
  rewrite matches_gmap. rewrite <- app_nil_end. simpl in *.
  subst. eapply (m_Map_g g1 s1 a). auto.
  rewrite matches_gmap in H. myinv H. clear H.
  rewrite IHg2 in H5. rewrite matches_Times_g in H5.
  destruct H5 as [s1 [s2 [H1 [H2 H3]]]]. subst.
  destruct v0 ; simpl in *.
  rewrite matches_Times_g. exists s1. exists s2.
  simpl in *. split ; auto.
  rewrite matches_gmap. destruct v; simpl in *.
  rewrite matches_Times_g in H.
  destruct H as  [s1 [s2 [H1 [H2 H3]]]]. subst. simpl in *.
  myinv H2. clear H2.
  eapply (m_Map_g (gtimes2 g1 g2) (s1 ++ s2) (a,v)).
  rewrite IHg2. rewrite matches_Times_g. eauto.
Qed.

Lemma matches_gtimes {A B}(g1:grammar A) (g2:grammar B) s v :
  matches (gtimes g1 g2) s v <-> matches (Times_g g1 g2) s v.
Proof.
  induction g1 ; simpl ; split ; intro ; eauto using matches_gtimes2 ;
    try (rewrite matches_gtimes2 in H ; auto) ;
    try (rewrite matches_gtimes2 ; auto).
  rewrite matches_gmap in H. myinv H. clear H.
  rewrite IHg1 in H5. rewrite matches_Times_g in H5.
  destruct H5 as [s1 [s2 [H1 [H2 H3]]]]. subst.
  rewrite matches_Times_g. exists s1. exists s2.  destruct v0 ; simpl in *.
  eauto. rewrite matches_gmap. destruct v. simpl in *.
  rewrite matches_Times_g in H. destruct H as [s1 [s2 [H1 [H2 H3]]]]. subst.
  myinv H1. clear H1.
  eapply (m_Map_g (gtimes g1 g2) (s1 ++ s2) (v,b1)). simpl in *.
  rewrite IHg1. rewrite matches_Times_g. eauto.
  rewrite matches_gtimes2 in H0. auto.
Qed.
  
(* This version does not lift maps, but simply reduces:
      gtimes' 0 g = gtimes g 0 = g
      gtimes' (1 @ f1) (1 @ f2) = 1 @ (\x.(f1 tt, f2 tt))
*)
     
Definition gtimes' {A} (g1:grammar A) {B} (g2:grammar B) : grammar (A * B) := 
  if (isZero g1 || isZero g2)%bool then gzero
  else
    match isMapOne g1, isMapOne g2 with
    | Some f1, Some f2 => gmap gone (fun x => (f1 tt, f2 tt))
    | _, _ => Times_g g1 g2
    end.

Lemma matches_isMapOne {A} (g:grammar A) : 
  match isMapOne g with
  | Some f1 => forall s v, matches g s v <-> matches (Map_g One_g f1) s v
  | _ => True
  end.
Proof.
  destruct g ; simpl ; auto.
  intros ; split ; intro. myinv H.
  eapply (m_Map_g One_g nil tt). auto.
  myinv H ; clear H. destruct v0 ; auto.
  destruct g ; simpl ; auto. tauto.
Qed.
  
Lemma matches_gtimes' {A B} (g1:grammar A) (g2:grammar B) s v : 
  matches (gtimes' g1 g2) s v <-> exists s1, exists s2, matches g1 s1 (fst v) /\
                                                        matches g2 s2 (snd v) /\ s = s1 ++ s2.
Proof.
  unfold gtimes'.
  remember (isZero g1) as b1.
  remember (isZero g2) as b2.
  destruct b1. simpl. split ; intros.
  contradiction (not_matches_gzero _ _ H).
  destruct H as [s1 [s2 [H1 [H2 H3]]]].
  contradiction (not_matches_isZero _ _ _ Heqb1 H1). simpl.
  destruct b2 ; simpl ; split ; intros.
  contradiction (not_matches_gzero _ _ H).
  destruct H as [s1 [s2 [H1 [H2 H3]]]].
  contradiction (not_matches_isZero _ _ _ Heqb2 H2). simpl.
  generalize (matches_isMapOne g1).
  generalize (matches_isMapOne g2). intros.
  destruct (isMapOne g1). destruct (isMapOne g2).
  myinv H. clear H. myinv H7. clear H7. exists nil. exists nil.
  simpl. split. rewrite H1. eauto.
  split. rewrite H0 ; eauto. auto.
  rewrite matches_Times_g in H. destruct H as [s1 [s2 [H2 [H3 H4]]]].
  subst. exists s1. exists s2. auto.
  rewrite matches_Times_g in H. destruct H as [s1 [s2 [H2 [H3 H4]]]].
  subst. exists s1. exists s2. auto.
  destruct H as [s1 [s2 [H1 [H2 H3]]]]. subst.
  generalize (matches_isMapOne g2).
  generalize (matches_isMapOne g1). intros.
  destruct (isMapOne g1) ; destruct (isMapOne g2).
  destruct v ; simpl in *.
  rewrite H in H1. rewrite H0 in H2. clear H H0. myinv H1. myinv H2.
  clear H1 H2. myinv H6. myinv H7. 
  eapply (m_Map_g One_g (nil ++ nil) tt). auto.
  rewrite matches_Times_g. eauto.
  rewrite matches_Times_g. eauto.
  rewrite matches_Times_g. eauto.
Qed.
  
Definition gstar {A} (g:grammar A) : grammar (list A) :=
  match g in grammar A' return grammar (list A') with
  | Zero_g => gmap gone (fun _ => nil)
  | g' => Star_g g'
  end.

Lemma matches_gstar {T} (g:grammar T) s v :
  matches (gstar g) s v <-> matches (Star_g g) s v.
Proof.
  destruct g ; simpl ; split ; intro ; eauto.
  myinv H. myinv H5. eauto.
  myinv H. eapply (m_Map_g One_g nil tt). eauto.
  destruct v1.
Qed.

Fixpoint gsum {S} (gs : list (grammar S)) : grammar S :=
  match gs with
  | nil => gzero
  | g::gs' => gplus g (gsum gs')
  end.

Lemma matches_gplus : forall {T:Set} (g1 g2:grammar T) s v,
    matches (Plus_g g1 g2) s v <-> matches (gplus g1 g2) s v.
Proof.
  intros. unfold gplus.
  remember (isZero g1) as b1 ; destruct b1. split ; intro.
  inversion H ; subst ; repeat depinv ; subst ; eauto.
  contradiction (not_matches_isZero g1 s v Heqb1).
  eauto.
  remember (isZero g2) as b2 ; destruct b2 ; split ; intros ; eauto.
  inversion H ; subst ; repeat depinv ; subst. auto.
  contradiction (not_matches_isZero g2 s v Heqb2).
Qed.

Lemma matches_gsum : forall {T} (gs: list (grammar T)) s v,
    matches (gsum gs) s v <-> exists g, In g gs /\ matches g s v.
Proof.
  induction gs ; simpl ; intros ; split ; intro.
  contradiction (not_matches_gzero _ _ H).
  destruct H as [_ [H _]]. contradiction.
  rewrite <- matches_gplus in H.
  inversion H ; subst ; repeat depinv ; subst ; clear H.
  exists a. auto.
  specialize (IHgs s v). rewrite IHgs in H4. destruct H4 as [g [H1 H2]].
  eauto.
  rewrite <- matches_gplus.
  destruct H as [g [H1 H2]].
  destruct H1. subst ; eauto.
  eapply m_r_Plus_g. rewrite IHgs. eauto.
Qed.

(* Extract the finite list of values the grammar associates with the empty string. *)
Fixpoint extract {S} (g:grammar S) : list S := 
  match g in grammar S' return list S' with
  | Zero_g => nil
  | One_g => tt::nil
  | Lit_g _ => nil
  | Plus_g g1 g2 => (extract g1) ++ (extract g2)
  | Map_g g f => List.map f (extract g)
  | Star_g g => nil::nil
  | @Bind_g A F g f =>
    List.concat
      (List.map (fun v => List.map (fun (x:F v) => existT F v x) (extract (f v))) (extract g))
  end.


Lemma extract_corr1 : forall {T} (g:grammar T) s v, matches g s v -> s = nil -> In v (extract g).
Proof.
  induction 1 ; simpl ; intros ; auto.
  discriminate.
  eapply in_or_app. left ; auto.
  eapply in_or_app. right ; auto.
  destruct s1. contradiction H0 ; auto. discriminate.
  apply in_map. auto.
  destruct s1 ; try discriminate. destruct s2 ; simpl in * ; try discriminate.
  specialize (IHmatches1 eq_refl). specialize (IHmatches2 eq_refl).
  rewrite <- flat_map_concat_map.
  apply in_flat_map. exists v1. split ; auto.
  rewrite in_map_iff.
  exists v2. split ; auto.
Qed.

Lemma extract_corr2 : forall {T} (g:grammar T) v, In v (extract g) -> matches g nil v.
Proof.
  induction g ; simpl ; intros ; try contradiction.
  destruct H ; try contradiction ; subst ; auto.
  rewrite in_app_iff in H. destruct H ; auto.
  destruct H ; try contradiction ; subst ; auto.
  rewrite in_map_iff in H. destruct H as [x [H1 H2]]. subst ; auto.
  replace (@nil Token) with (@nil Token ++ nil) ; auto.
  destruct v. specialize (IHg x). specialize (H x f).
  rewrite <- flat_map_concat_map in H0.
  rewrite in_flat_map in H0.
  destruct H0 as [x0 [H1 H2]].
  rewrite in_map_iff in H2.
  destruct H2 as [x1 [H3 H4]].
  inversion H3. subst. depinv. subst.
  constructor ; auto.
Qed.

Lemma extract_corr : forall {T} (g:grammar T) v, In v (extract g) <-> matches g nil v.
Proof.
  intros ; split ; eauto using extract_corr1, extract_corr2.
Qed.


(* Calculate the derivative of a grammar with respect to the character a. *)
Fixpoint deriv {S} (a:Token) (g:grammar S) : grammar S :=
  match g with
  | Zero_g => gzero
  | One_g => gzero
  | Lit_g b => if Tok_dec a b then gmap gone (fun _ => a) else gzero
  | Plus_g g1 g2 => gplus (deriv a g1) (deriv a g2)
  | Star_g g => gmap (gtimes' (deriv a g) (gstar g))
                     (fun p => (fst p)::(snd p))
  | Map_g g f => gmap (deriv a g) f
  | Bind_g g f =>
    gplus (gbind (deriv a g) f)
          (gsum (List.map (fun x => gmap (deriv a (f x)) (fun v => existT _ _ v)) (extract g)))
  end.

Lemma deriv_corr1 {T} (g:grammar T) : forall s v c, matches (deriv c g) s v -> matches g (c::s) v.
Proof.
  induction g ; simpl ; intros.
  contradiction (not_matches_gzero _ _ H).
  contradiction (not_matches_gzero _ _ H).
  destruct (Tok_dec c t).
  subst. inversion H ; subst ; repeat depinv ; subst ; clear H.
  inversion H5. subst ; repeat depinv ; subst. eauto.
  contradiction (not_matches_gzero _ _ H).
  rewrite <- matches_gplus in H.
  inversion H ; subst ; repeat depinv ; subst ; eauto.
  rewrite matches_gmap in H. inversion H ; subst. repeat depinv ; subst ; clear H.
  rewrite matches_gtimes' in H5.
  destruct H5 as [s1 [s2 [H1 [H2 H3]]]]. subst.
  specialize (IHg s1 (fst v0) c H1).
  eapply (m_r_Star_g g (c::s1) s2 (fst v0) (snd v0)) ; eauto. intro ; discriminate.
  rewrite matches_gstar in H2. auto.
  rewrite matches_gmap in H. myinv H. specialize (IHg _ _ _ H5).
  eauto.
  rewrite <- matches_gplus in H0. myinv H0 ; clear H0.
  rewrite matches_gbind in H5. rewrite inv_Bind_g in H5.
  destruct H5 as [s1 [s2 [v1 [v2 [H1 [H2 [H3 H4]]]]]]]. subst.
  specialize (IHg _ _ _ H1).
  replace (c::s1++s2) with ((c::s1) ++ s2) ; [ idtac | auto ].
  eapply m_Bind_g ; eauto.
  rewrite matches_gsum in H5. destruct H5 as [g1 [H1 H2]].
  rewrite in_map_iff in H1. destruct H1 as [x [H3 H4]]. subst.
  rewrite extract_corr in H4.
  rewrite matches_gmap in H2.
  myinv H2. clear H2. specialize (H _ _ _ _ H7).
  replace (c::s) with (nil ++ (c::s)) ; [idtac | auto].
  eauto.
Qed.

Lemma deriv_corr2 {T} (g:grammar T) : forall s v c, matches g (c::s) v -> matches (deriv c g) s v.
Proof.
  induction g ; simpl ; intros.
  inversion H. inversion H.
  destruct (Tok_dec c t). subst. inversion H. subst.
  depinv. subst. eapply (m_Map_g One_g nil tt). auto.
  inversion H. congruence.
  myinv H ; clear H ; rewrite <- matches_gplus ; eauto.
  myinv H ; clear H. destruct s1. contradiction H7 ; auto.
  simpl in H4. injection H4. intros ; subst.
  rewrite matches_gmap.
  eapply (m_Map_g (gtimes' (deriv c g) (gstar g)) (s1 ++ s2) (v1,v2) (fun p => fst p::snd p)).
  rewrite matches_gtimes'.
  exists s1. exists s2. simpl. split. apply IHg ; auto. split.
  rewrite matches_gstar. eauto. auto.
  myinv H; clear H. rewrite matches_gmap. eauto.
  rewrite inv_Bind_g in H0. destruct H0 as [s1 [s2 [v1 [v2 [H1 [H2 [H3 H4]]]]]]]. subst.
  rewrite <- matches_gplus.
  destruct s1. simpl in *. subst. specialize (H _ _ _ _ H2).
  eapply m_r_Plus_g. rewrite matches_gsum.
  specialize (extract_corr1 _ _ _ H1 eq_refl). intros.
  exists (gmap (deriv c (g0 v1)) (fun v => existT _ v1 v)).
  split. rewrite in_map_iff. exists v1. split ; auto.
  rewrite matches_gmap. eauto.
  eapply m_l_Plus_g. simpl in *. injection H3 ; intros ; subst.
  rewrite matches_gbind. eauto.
Qed.

Lemma deriv_corr {T} (g:grammar T) c s v : matches (deriv c g) s v <-> matches g (c::s) v.
Proof.
  split. apply deriv_corr1. apply deriv_corr2.
Qed.


(* Calculate the derivative with respect to the string a. *)
Fixpoint derivs {S} (a:list Token) (g:grammar S) : grammar S :=
  match a with
  | nil => g
  | c::cs => derivs cs (deriv c g)
  end.

Lemma derivs_corr s1 : forall {T} (g:grammar T) s2 v, matches (derivs s1 g) s2 v <-> matches g (s1 ++ s2) v.
Proof.
  induction s1 ; simpl ; try tauto.
  intros. rewrite <- deriv_corr.
  eapply IHs1.
Qed.

(* To parse s, calculate the derivative with respect to s and then
   extract the values associated with the empty string. *)
Definition parse {S} (g:grammar S) (str: list Token) : list S :=
  extract (derivs str g).

Lemma parse_corr : forall {T} (g:grammar T) (s:list Token) v,
    In v (parse g s) <-> matches g s v.
Proof.
  unfold parse. intros.
  rewrite extract_corr. rewrite derivs_corr.
  rewrite <- app_nil_end. tauto.
Qed.

Definition Times_l {A B:Set} (g1:grammar A) (g2:grammar B) : grammar A :=
  Map_g (Times_g g1 g2) (fun p => fst p).

Definition Times_r {A B:Set} (g1:grammar A) (g2:grammar B) : grammar B :=
  Map_g (Times_g g1 g2) (fun p => snd p).
  
Definition option_g{A:Set}(g:grammar A) : grammar (option A) :=
  Plus_g (Map_g g Some) (Map_g One_g (fun _ => None)).