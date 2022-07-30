From Coq Require Export Lists.List micromega.Lia.
Require Export Poulet4.Utils.Util.ListUtil.
Export ListNotations.

(** * Utility Lemmas & Definitions for Lists. *)

Lemma nth_error_app3 : forall {U : Type} (l us : list U) n,
    nth_error (l ++ us) (length l + n) = nth_error us n.
Proof.
  intros U l us; induction l as [| h t ih];
    intros [| n]; cbn; auto.
  - rewrite ih; reflexivity.
  - rewrite ih; reflexivity.
Qed.

Lemma length_nth_error_some : forall (U : Type) n us,
    n < List.length us -> exists u : U, nth_error us n = Some u.
Proof.
  intros U n; induction n as [| n IHn];
    intros [| u us] H; cbn in *; try lia; eauto.
  assert (n < List.length us) by lia; auto.
Qed.

Section MapCombine.
  Variables U V : Type.
  
  Lemma combine_map_fst_snd : forall (l : list (U * V)),
      combine (map fst l) (map snd l) = l.
  Proof.
    intro l; induction l as [| [u v] l IHl];
      simpl; f_equal; auto.
  Qed.
  
  Lemma map_fst_combine : forall (us : list U) (vs : list V),
      List.length us = List.length vs ->
      map fst (combine us vs) = us.
  Proof.
    intro us; induction us as [| u us IHus];
      intros [| v vs] Hl; simpl in *;
        inversion Hl; subst; f_equal; auto.
  Qed.
  
  Lemma map_snd_combine : forall (us : list U) (vs : list V),
      List.length us = List.length vs ->
      map snd (combine us vs) = vs.
  Proof.
    intro us; induction us as [| u us IHus];
      intros [| v vs] Hl; simpl in *;
        inversion Hl; subst; f_equal; auto.
  Qed.
End MapCombine.

Lemma Forall_impl_Forall : forall (U : Type) (P Q : U -> Prop) us,
    Forall (fun u => P u -> Q u) us -> Forall P us -> Forall Q us.
Proof.
  intros; rewrite Forall_forall in *; auto.
Qed.

Section Forall.
  Variables (A B : Type) (R : A -> B -> Prop).
  
  Lemma Forall_exists_factor : forall l : list A,
      Forall (fun a => exists b, R a b) l <-> exists bs, Forall2 R l bs.
  Proof.
    intro l; split.
    - intro H; induction H; eauto.
      destruct H as [b HRb];
      destruct IHForall as [bs HRbs]; eauto.
    - intros [bs HRlbs].
      induction HRlbs; eauto.
  Qed.

  Lemma forall_Forall2 : forall (l : list A),
      (forall a, In a l -> forall b, R a b) ->
      forall bs, List.length l = List.length bs -> Forall2 R l bs.
  Proof.
    intro l;
      induction l as [| a l IHl];
      intros H [| b bs] Hbs; simpl in *; try discriminate; auto.
  Qed.

  Lemma Forall2_length : forall la lb,
      Forall2 R la lb -> List.length la = List.length lb.
  Proof.
    intros la lb H; induction H;
      simpl; f_equal; auto.
  Qed.

  Lemma Forall2_flip : forall la lb,
      Forall2 (fun b a => R a b) lb la <-> Forall2 R la lb.
  Proof.
    intros la lb; split; intros H;
      induction H; auto.
  Qed.
  
  Variable Q : A -> B -> Prop.
  
  Lemma Forall2_impl : forall la lb,
      Forall2 (fun a b => R a b -> Q a b) la lb ->
      Forall2 R la lb -> Forall2 Q la lb.
  Proof.
    intros la lb HRQ HR;
      induction HRQ; inversion HR; subst; auto.
  Qed.

  Lemma Forall2_conj : forall us vs,
      Forall2 (fun u v => R u v /\ Q u v) us vs <->
      Forall2 R us vs /\ Forall2 Q us vs.
  Proof.
    intros us vs; split.
    - intros H; induction H; simpl in *; intuition.
    - intros [HR HQ]; induction HR; inversion HQ;
        simpl in *; auto.
  Qed.
End Forall.

Section ForallMap.
  Variables (A B C : Type) (R : A -> B -> Prop).
  
  Lemma Forall2_map_l : forall (f : C -> A) lc lb,
      Forall2 (fun c b => R (f c) b) lc lb <-> Forall2 R (map f lc) lb.
  Proof.
    intros f lc lb; split; intros H.
    - induction H; simpl in *; auto.
    - remember (map f lc) as la eqn:Heqla;
        generalize dependent lc.
      induction H; intros [| ? ?] Heqla;
      simpl in *; inversion Heqla; subst; auto.
  Qed.
  
  Lemma Forall2_map_r : forall (f : C -> B) la lc,
      Forall2 (fun a c => R a (f c)) la lc <-> Forall2 R la (map f lc).
  Proof.
    intros f la lc; split; intros H.
    - induction H; simpl in *; auto.
    - remember (map f lc) as mflc eqn:Hmflc.
      generalize dependent lc.
      induction H; intros lc Hmflc.
      + symmetry in Hmflc; apply map_eq_nil in Hmflc; subst; auto.
      + destruct lc as [| c lc]; simpl in *;
          inversion Hmflc; subst; auto.
  Qed.
End ForallMap.

Lemma Forall2_map_both :
  forall (T U V W : Type) (R : V -> W -> Prop) (f : T -> V) (g : U -> W) ts us,
    Forall2 (fun t u => R (f t) (g u)) ts us <-> Forall2 R (map f ts) (map g us).
Proof.
  intros; rewrite <- Forall2_map_l, <- Forall2_map_r; reflexivity.
Qed.

Lemma reduce_inner_impl : forall (A : Type) (Q : Prop) (P R : A -> Prop),
    (forall a, P a -> Q -> R a) -> Q -> forall a, P a -> R a.
Proof.
  intuition.
Qed.

Lemma reduce_inner_impl_forall : forall (A : Type) (P Q R : A -> Prop),
    (forall a, P a -> Q a -> R a) -> (forall a, P a -> Q a) -> forall a, P a -> R a.
Proof.
  intuition.
Qed.

Lemma reduce_inner_impl_forall_impl : forall (A : Type) (P Q R S : A -> Prop),
    (forall a, S a -> Q a) -> (forall a, P a -> Q a -> R a) ->
    (forall a, P a -> S a) -> forall a, P a -> R a.
Proof.
  intuition.
Qed.


Lemma split_impl_conj : forall (A : Type) (P Q R : A -> Prop),
    (forall a, P a -> Q a /\ R a) <->
    (forall a, P a -> Q a) /\ forall a, P a -> R a.
Proof.
  firstorder.
Qed.

Lemma Forall2_Forall : forall (U : Type) (R : U -> U -> Prop) us,
    Forall2 R us us <-> Forall (fun u => R u u) us.
Proof.
  intros U R us; split;
    induction us as [| u us IHus];
    intros H; inversion H; subst; simpl in *; auto.
Qed.

Section MapMap.
  Variables (U V W X : Type)
            (f : U -> W) (g : V -> X).

  Lemma map_fst_map : forall (uvs : list (U * V)),
      map fst (map (fun '(u,v) => (f u, g v)) uvs) = map f (map fst uvs).
  Proof.
    intro uvs; induction uvs as [| [u v] uvs IHuvs];
      simpl in *; f_equal; auto.
  Qed.
  
  Lemma map_snd_map : forall (uvs : list (U * V)),
      map snd (map (fun '(u,v) => (f u, g v)) uvs) = map g (map snd uvs).
  Proof.
    intro uvs; induction uvs as [| [u v] uvs IHuvs];
      simpl in *; f_equal; auto.
  Qed.
End MapMap.
  
Lemma map_only_fst : forall (U V W : Type) (f : U -> V) (uws : list (U * W)),
    map (fun '(u,w) => (f u, w)) uws =
    let '(us,ws) := split uws in
    combine (map f us) ws.
Proof.
  intros U V W f uws;
    induction uws as [| [u w] uws IHuws];
    simpl in *; auto.
  destruct (split uws) as [us ws] eqn:Hequws;
    simpl in *; f_equal; auto.
Qed.

Lemma map_only_snd : forall (U V W : Type) (f : V -> W) (uvs : list (U * V)),
    map (fun '(u,v) => (u, f v)) uvs =
    let '(us,vs) := split uvs in
    combine us (map f vs).
Proof.
  intros U V W f uvs;
    induction uvs as [| [u v] uvs IHuvs];
    simpl in *; auto.
  destruct (split uvs) as [us vs] eqn:Hequws;
    simpl in *; f_equal; auto.
Qed.

Lemma Forall_fst : forall (U V : Type) (P : U -> Prop) (uvs : list (U * V)),
    Forall (fun '(u,_) => P u) uvs <-> Forall (fun uv => P (fst uv)) uvs.
Proof.
  intros U V P uvs; split; intro H;
    induction uvs as [| [u v] uvs IHuvs];
    inversion H; subst; simpl in *; auto.
Qed.

Lemma Forall_snd : forall (U V : Type) (P : V -> Prop) (uvs : list (U * V)),
    Forall (fun '(_,v) => P v) uvs <-> Forall (fun uv => P (snd uv)) uvs.
Proof.
  intros U V P uvs; split; intro H;
    induction uvs as [| [u v] uvs IHuvs];
    inversion H; subst; simpl in *; auto.
Qed.

Lemma Forall2_eq : forall (U : Type) (us vs : list U),
    Forall2 eq us vs <-> us = vs.
Proof.
  intros U us vs; split; intros H; subst.
  - induction H; subst; auto.
  - induction vs; auto.
Qed.

Lemma map_pat_both : forall (U V W : Type) (f : U -> V -> W) luv,
    map (fun '(u,v) => f u v) luv = map (fun uv => f (fst uv) (snd uv)) luv.
Proof.
  intros U V W f luv;
    induction luv as [| [u v] luv IHluv];
    simpl; f_equal; auto.
Qed.

Lemma Forall2_destr_pair_eq :
  forall {U V W : Type}
    (f : V -> option W)
    (luv : list (U * V)) (luw : list (U * W)),
    Forall2 (fun uv uw =>
               match f (snd uv) with
               | Some w => Some (fst uv, w)
               | None   => None
               end = Some uw) luv luw <->
    map fst luv = map fst luw /\
    Forall2 (fun v w => f v = Some w) (map snd luv) (map snd luw).
Proof.
  intros U V W f luv luw; split;
    generalize dependent luw;
    induction luv as [| [u v] luv IHluv];
    intros [| [u' w] luw]; simpl in *; intros H; auto.
  - inversion H.
  - inversion H.
  - inversion H; subst; clear H; simpl in *.
    destruct (f v) as [w' |] eqn:Heqfv; simpl in *;
      inversion H3; subst; clear H3.
    apply IHluv in H5 as [Hfst Hsnd];
      rewrite Hfst; split; auto.
  - destruct H as [H _]; inversion H.
  - destruct H as [H _]; inversion H.
  - destruct H as [Hfst Hsnd];
      inversion Hfst; inversion Hsnd; subst; clear Hfst Hsnd;
        constructor; simpl; auto.
    rewrite H4; auto.
Qed.

Section Forall2Impl.
  Variables (T U V : Type).
  Variables (R : T -> V -> Prop) (S : U -> V -> Prop).

  Lemma Forall2_forall_impl_Forall2 : forall ts us,
      Forall2 (fun t u => forall v, R t v -> S u v) ts us ->
      forall vs, Forall2 R ts vs -> Forall2 S us vs.
  Proof.
    intros ts us H;
      induction H as [| t u ts us Htu Htsus IHtsus];
      intros vs Htsvs; inversion Htsvs; clear Htsvs; subst; auto.
  Qed.
End Forall2Impl.

Lemma Forall2_forall_specialize :
  forall (T U V : Type) (Q : T -> U -> V -> Prop) us vs,
    Forall2 (fun u v => forall t, Q t u v) us vs ->
    forall t, Forall2 (Q t) us vs.
Proof.
  intros T U V Q us vs H;
    induction H as [| u v us vs Huv Husvs IHusvs];
    intro t; auto.
Qed.

Lemma Forall2_forall : forall (U V : Type) (R : U -> V -> Prop) us vs,
    Forall2 R us vs <->
    List.length us = List.length vs /\
    forall u v, In (u,v) (combine us vs) -> R u v.
Proof.
  intros U V R us vs; split; intros H.
  - split; eauto using Forall2_length.
    induction H; intros u v Hin; simpl in *; try contradiction.
    destruct Hin as [Heq | Hin]; try inversion Heq; subst; auto.
  - destruct H as [Hlen Hcomb].
    generalize dependent vs.
    induction us as [| u us IHus];
      intros [| v vs] Hlen Hcomb; simpl in *; inversion Hlen; subst; auto.
Qed.

Lemma Forall2_Forall_combine : forall (U V : Type) (R : U -> V -> Prop) us vs,
    Forall2 R us vs <->
    List.length us = List.length vs /\
    Forall (uncurry R) (combine us vs).
Proof.
  intros U V R us vs.
  rewrite Forall_forall, Forall2_forall.
  apply and_iff_compat_l; split.
  - intros H [u v]; cbn; auto.
  - firstorder.
Qed.

Lemma nth_error_combine :
  forall (U V : Type) n us vs (u : U) (v : V),
    nth_error us n = Some u ->
    nth_error vs n = Some v ->
    nth_error (combine us vs) n = Some (u,v).
Proof.
  intros U V n; induction n as [| n IHn];
    intros [| u us] [| v vs] u' v' Hus Hvs; cbn in *;
      try discriminate; auto;
        inversion Hus; inversion Hvs; subst; reflexivity.
Qed.

Lemma nth_error_in_combine :
  forall (U V : Type) n us vs (u : U) (v : V),
    nth_error us n = Some u ->
    nth_error vs n = Some v ->
    In (u,v) (combine us vs).
Proof.
  Local Hint Resolve nth_error_combine : core.
  eauto using nth_error_In.
Qed.

Lemma Forall2_forall_nth_error : forall (U V : Type) (R : U -> V -> Prop) us vs,
    Forall2 R us vs <->
    List.length us = List.length vs /\
    forall n u v,
      nth_error us n = Some u ->
      nth_error vs n = Some v ->
      R u v.
Proof.
  intros U V R us vs.
  rewrite Forall2_forall.
  split; intros [Hlen H]; split;
    eauto using nth_error_in_combine.
  intros u v Husvs.
  apply In_nth_error in Husvs as [n Hn].
  apply map_nth_error with (f:=fst) in Hn as Hnus.
  apply map_nth_error with (f:=snd) in Hn as Hnvs.
  rewrite map_fst_combine in Hnus by assumption;
    rewrite map_snd_combine in Hnvs by assumption; eauto.
Qed.

(** Why I'm I getting goals such as these? *)
Lemma Forall2_dumb : forall (U V : Type) (Q : Prop) (R : U -> V -> Prop) us vs,
    Q -> Forall2 (fun u v => Q -> R u v) us vs -> Forall2 R us vs.
Proof.
  intros U V Q R us vs q H; induction H; auto.
Qed.

Lemma Forall_remove :
  forall (U : Type) (P : U -> Prop) {HU : forall u₁ u₂, {u₁ = u₂} + {u₁ <> u₂}} u us,
    Forall P us -> Forall P (remove HU u us).
Proof.
  intros U P HU u us H.
  generalize dependent HU;
    generalize dependent u.
  induction H
    as [| u us Hus IHus]; intros u' HU;
    cbn in *; auto.
  destruct (HU u' u) as [Hu'u | Hu'u]; subst; auto.
Qed.

Lemma split_inj : forall (U V : Type) (uvs₁ uvs₂ : list (U * V)),
    split uvs₁ = split uvs₂ -> uvs₁ = uvs₂.
Proof.
  intros U V usv1;
    induction usv1 as [| [u1 v1] usv1 IHusv1];
    intros [| [u2 v2] usv2] H;
    simpl in *; auto.
  - destruct (split usv2) as [us2 vs2] eqn:H2; inversion H.
  - destruct (split usv1) as [us1 vs1] eqn:H1; inversion H.
  - specialize IHusv1 with usv2.
    destruct (split usv1) as [us1 vs1] eqn:H1;
      destruct (split usv2) as [us2 vs2] eqn:H2.
    inversion H; subst; f_equal; auto.
Qed.

Lemma map_pat_combine : forall (T U V W: Type) (f : T -> V) (g : U -> W) tus,
    map (fun '(t,u) => (f t, g u)) tus =
    combine (map f (map fst tus)) (map g (map snd tus)).
Proof.
  intros T U V W f g tus;
    induction tus as [| [t u] tus IHtus];
    simpl; f_equal; auto.
Qed.

Lemma nth_error_some_length : forall {A : Type} n l (a : A),
    nth_error l n = Some a -> n < List.length l.
Proof.
  intros A n;
    induction n as [| n IHn];
    intros [| h l] a Hnth; cbn in *;
      try discriminate; firstorder lia.
Qed.

Lemma Forall2_only_l_Forall : forall (U V : Type) (P : U -> Prop) us (vs : list V),
    Forall2 (fun u _ => P u) us vs -> Forall P us.
Proof.
  intros U V P us;
    induction us as [| u us IHus];
    intros [| v vs] H; inversion H; subst;
      cbn in *; eauto.
Qed.

Corollary Forall2_only_r_Forall : forall (U V : Type) (P : V -> Prop) (us : list U) vs,
    Forall2 (fun _ v => P v) us vs -> Forall P vs.
Proof.
  intros U V P us vs H.
  rewrite Forall2_flip in H.
  eauto using Forall2_only_l_Forall.
Qed.

Lemma Forall_Forall2_only_l : forall (U V : Type) (P : U -> Prop) us (vs : list V),
    Forall P us -> length us = length vs -> Forall2 (fun u _ => P u) us vs.
Proof.
  intros U V P us vs hus hlen.
  rewrite Forall2_forall_nth_error.
  rewrite Forall_forall in hus.
  split; assumption || intros n u _ hu _; eauto using nth_error_In.
Qed.

Corollary Forall_Forall2_only_r : forall (U V : Type) (P : V -> Prop) (us : list U) vs,
    Forall P vs -> length us = length vs -> Forall2 (fun _ v => P v) us vs.
Proof.
  intros U V P us vs hus hlen.
  rewrite Forall2_flip.
  symmetry in hlen.
  auto using Forall_Forall2_only_l.
Qed.  

Section Forall3.
  Context {T U V : Type}.
  Variable R : T -> U -> V -> Prop.

  Inductive Forall3 : list T -> list U -> list V -> Prop :=
  | Forall3_nil :
      Forall3 [] [] []
  | Forall3_cons t u v ts us vs :
      R t u v ->
      Forall3 ts us vs ->
      Forall3 (t :: ts) (u :: us) (v :: vs).

  Local Hint Constructors Forall3 : core.
  
  Lemma Forall2_ex_factor : forall ts us,
      Forall2 (fun t u => exists v, R t u v) ts us ->
      exists vs, Forall3 ts us vs.
  Proof.
    intros ts us H;
      induction H as [| t u ts us [v Htuv] Htsus [vs IHtsus]];
      eauto.
  Qed.

  Lemma Forall3_forall : forall ts us vs,
      Forall3 ts us vs <->
      List.length ts = List.length us /\ List.length us = List.length vs /\
      forall n t u v,
        nth_error ts n = Some t ->
        nth_error us n = Some u ->
        nth_error vs n = Some v ->
        R t u v.
  Proof.
    intros ts us vs; split.
    - intros H.
      induction H as [| t u v ts us vs Htuv Htsusvs [Htsus [Husvs IHtsusvs]]]; cbn;
        repeat split; try lia;
          intros [| n] t' u' v' Ht' Hu' Hv'; cbn in *; try discriminate; eauto.
      inversion Ht'; subst; inversion Hu'; subst;
        inversion Hv'; subst; clear Ht' Hu' Hv'; assumption.
    - intros (Htsus & Husvs & H).
      generalize dependent vs; generalize dependent us.
      induction ts as [| t ts IHts];
        intros [| u us] Htsus [| v vs] Husvs H; cbn in *; try lia; auto.
      injection Htsus as Htus; injection Husvs as Huvs.
      constructor.
      + apply H with (n := 0); reflexivity.
      + apply IHts; auto.
        intros n t' u' v' Ht' Hu' Hv'.
        specialize H with (n := S n); cbn in *; auto.
  Qed.

  Local Hint Resolve nth_error_combine : core.
  Local Hint Resolve nth_error_in_combine : core.

  Lemma Forall3_Forall2_combine_l : forall ts us vs,
      Forall3 ts us vs <->
      List.length ts = List.length us /\
      Forall2 (fun '(t,u) v => R t u v) (combine ts us) vs.
  Proof.
    intros ts us vs.
    rewrite Forall3_forall.
    split.
    - rewrite Forall2_forall_nth_error, combine_length.
      intros (Htsus & Husvs & H).
      repeat split; try lia.
      intros n [u t] v Hnthtsus Hnthvs.
      apply map_nth_error with (f:=fst) in Hnthtsus as Hnthts.
      apply map_nth_error with (f:=snd) in Hnthtsus as Hnthus.
      rewrite map_fst_combine in Hnthts by assumption;
        rewrite map_snd_combine in Hnthus by assumption; eauto.
    - rewrite Forall2_forall, combine_length.
      intros (Htsus & Htsusvs & H).
      repeat split; try lia.
      intros n t u v Hts Hus Hvs.
      specialize H with (u:=(t,u)) (v:=v); cbn in *; eauto.
  Qed.

  Lemma Forall3_Forall2_combine_r : forall ts us vs,
      Forall3 ts us vs <->
      List.length us = List.length vs /\
      Forall2 (fun t '(u,v) => R t u v) ts (combine us vs).
  Proof.
    intros ts us vs.
    rewrite Forall3_Forall2_combine_l;
      repeat rewrite Forall2_forall_nth_error, combine_length.
    split; intros (Htsus & Htsusvs & H); repeat split; try lia.
    - intros n t [u v] Hnthts Hnthusvs.
      specialize H with (n:=n) (u:=(t,u)) (v:=v); cbn in *.
      apply map_nth_error with (f := fst) in Hnthusvs as Hnthus.
      apply map_nth_error with (f := snd) in Hnthusvs as Hnthvs.
      rewrite map_fst_combine in Hnthus by lia.
      rewrite map_snd_combine in Hnthvs by lia; cbn in *; eauto.
    - intros n [t u] v Hnthtsus Hnthvs.
      specialize H with (n:=n) (u:=t) (v:=(u,v)); cbn in *.
      apply map_nth_error with (f := fst) in Hnthtsus as Hnthts.
      apply map_nth_error with (f := snd) in Hnthtsus as Hnthus.
      rewrite map_fst_combine in Hnthts by lia.
      rewrite map_snd_combine in Hnthus by lia; cbn in *; eauto.
  Qed.
End Forall3.

Lemma Forall3_permute_12 : forall T U V (R : T -> U -> V -> Prop) ts us vs,
    Forall3 R ts us vs <-> Forall3 (fun u t => R t u) us ts vs.
Proof.
  intros T U V R ts us vs.
  repeat rewrite Forall3_forall.
  split; intros (H₁ & H₂ & H); repeat split; try lia; eauto.
Qed.

Lemma Forall3_permute_13 : forall T U V (R : T -> U -> V -> Prop) ts us vs,
    Forall3 R ts us vs <-> Forall3 (fun v u t => R t u v) vs us ts.
Proof.
  intros T U V R ts us vs.
  repeat rewrite Forall3_forall.
  split; intros (H₁ & H₂ & H); repeat split; try lia; eauto.
Qed.

Lemma Forall3_permute_23 : forall T U V (R : T -> U -> V -> Prop) ts us vs,
    Forall3 R ts us vs <-> Forall3 (fun t v u => R t u v) ts vs us.
Proof.
  intros T U V R ts us vs.
  repeat rewrite Forall3_forall.
  split; intros (H₁ & H₂ & H); repeat split; try lia; eauto.
Qed.

Lemma Forall3_conj_sep : forall T U V (Q : T -> V -> Prop) (R : U -> V -> Prop) ts us vs,
    Forall3 (fun t u v => Q t v /\ R u v) ts us vs <->
    Forall2 Q ts vs /\ Forall2 R us vs.
Proof.
  Local Hint Resolve nth_error_some_length : core.
  Local Hint Resolve length_nth_error_some : core.
  intros T U V Q R ts us vs.
  rewrite Forall3_forall.
  repeat rewrite Forall2_forall_nth_error; split.
  - intros (Htsus & Husvs & H).
    repeat split; try lia.
    + intros n t v Hnthts Hnthvs.
      assert (Hu: exists u, nth_error us n = Some u).
      { apply nth_error_some_length in Hnthts.
        rewrite Htsus in Hnthts; auto. }
      destruct Hu as [u Hnthus].
      pose proof H _ _ _ _ Hnthts Hnthus Hnthvs as [Hq _]; assumption.
    + intros n u v Hnthus Hnthvs.
      assert (Ht: exists t, nth_error ts n = Some t).
      { apply nth_error_some_length in Hnthus.
        rewrite <- Htsus in Hnthus; auto. }
      destruct Ht as [t Hnthts].
      pose proof H _ _ _ _ Hnthts Hnthus Hnthvs as [_ Hr]; assumption.
  - intros [[Htsvs HQ] [Husvs HR]]; do 2 (split; try lia); eauto.
Qed.

Lemma Forall_specialize_Forall2 : forall (U V : Type) (R : U -> V -> Prop) us,
    Forall (fun u => forall v, R u v) us -> forall vs,
      List.length us = List.length vs -> Forall2 R us vs.
Proof.
  intros U V R us H vs Hvs.
  rewrite Forall_forall in H.
  rewrite Forall2_forall; split; eauto using in_combine_l.
Qed.

Lemma Forall2_specialize_Forall3 : forall (U V W : Type) (R : U -> V -> W -> Prop) us vs,
    Forall2 (fun u v => forall w, R u v w) us vs -> forall ws,
      List.length vs = List.length ws -> Forall3 R us vs ws.
Proof.
  intros U V W R us vs Husvs ws Hws.
  rewrite Forall2_forall_nth_error in Husvs.
  destruct Husvs as [Hlen Husvs].
  rewrite Forall3_forall; repeat split; eauto.
Qed.

Lemma Forall2_Forall_impl_Forall : forall (U V : Type) (R : U -> V -> Prop) (Q : V -> Prop) us vs,
    Forall2 R us vs -> Forall (fun u => forall v, R u v -> Q v) us -> Forall Q vs.
Proof.
  intros U V R Q us vs Husvs Hus.
  apply Forall_specialize_Forall2 with (vs:=vs) in Hus; eauto using Forall2_length.
  apply Forall2_impl with
      (R:=R) (Q:=fun _ v => Q v) in Hus; auto.
  eauto using Forall2_only_r_Forall.
Qed.

Lemma Forall3_Forall2_Forall2_impl_Forall2 :
  forall (T U V : Type) (P : T -> U -> Prop) (Q : T -> V -> Prop) (R : U -> V -> Prop) ts us vs,
    Forall3 (fun t u v => P t u -> Q t v -> R u v) ts us vs ->
    Forall2 P ts us -> Forall2 Q ts vs -> Forall2 R us vs.
Proof.
  intros T U V P Q R ts us vs HF3 Htsus Htsvs.
  rewrite Forall3_forall in HF3.
  rewrite Forall2_forall_nth_error in *.
  destruct HF3 as (Hlen_ts_us & Hlen_us_vs & Htsusvs).
  destruct Htsus as [_ Htsus].
  destruct Htsvs as [Hlen_ts_vs Htsvs].
  split; try assumption; intros n u v Hu Hv.
  assert (Ht: exists t, nth_error ts n = Some t).
  { apply length_nth_error_some.
    rewrite Hlen_ts_us; eauto using nth_error_some_length. }
  firstorder eauto.
Qed.

Lemma Forall3_map_1 : forall T U V W (R : U -> V -> W -> Prop) (f : T -> U) ts vs ws,
    Forall3 (fun t v w => R (f t) v w) ts vs ws <-> Forall3 R (map f ts) vs ws.
Proof.
  intros T U V W R f ts vs ws.
  repeat rewrite Forall3_Forall2_combine_r.
  apply and_iff_compat_l.
  pose proof Forall2_map_l as H.
  specialize H with
      (f:=f) (lc:=ts) (lb:=combine vs ws)
      (R := fun u '(v,w) => R u v w); cbn in *.
  assumption.
Qed.

Lemma Forall3_map_2 : forall T U V W (R : U -> V -> W -> Prop) (f : T -> V) us ts ws,
    Forall3 (fun u t w => R u (f t) w) us ts ws <-> Forall3 R us (map f ts) ws.
Proof.
  intros T U V W R f us ts ws.
  rewrite Forall3_permute_12 with (us:=ts).
  rewrite Forall3_permute_12 with (us:=map f ts).
  rewrite <- Forall3_map_1; reflexivity.
Qed.

Lemma Forall3_map_3 : forall T U V W (R : U -> V -> W -> Prop) (f : T -> W) us vs ts,
    Forall3 (fun u v t => R u v (f t)) us vs ts <-> Forall3 R us vs (map f ts).
Proof.
  intros T U V W R f us vs ts.
  rewrite Forall3_permute_23 with (vs:=ts).
  rewrite Forall3_permute_23 with (vs:=map f ts).
  rewrite <- Forall3_map_2; reflexivity.
Qed.

Lemma Forall3_map_12 : forall T U V W Z (R : V -> W -> Z -> Prop) (f : T -> V) (g : U -> W) ts us zs,
    Forall3 (fun t u z => R (f t) (g u) z) ts us zs <->
    Forall3 R (map f ts) (map g us) zs.
Proof.
  intros T U V W Z R f g ts us zs.
  rewrite <- Forall3_map_1,<- Forall3_map_2; reflexivity.
Qed.

Lemma Forall3_map_13 : forall T U V W Z (R : V -> W -> Z -> Prop) (f : T -> V) (g : U -> Z) ts ws us,
    Forall3 (fun t w u => R (f t) w (g u)) ts ws us <->
    Forall3 R (map f ts) ws (map g us).
Proof.
  intros T U V W Z R f g ts ws us.
  rewrite <- Forall3_map_1,<- Forall3_map_3; reflexivity.
Qed.

Lemma Forall3_map_23 : forall T U V W Z (R : V -> W -> Z -> Prop) (f : T -> W) (g : U -> Z) vs ts us,
    Forall3 (fun v t u => R v (f t) (g u)) vs ts us <->
    Forall3 R vs (map f ts) (map g us).
Proof.
  intros T U V W Z R f g vs ts us.
  rewrite <- Forall3_map_2,<- Forall3_map_3; reflexivity.
Qed.

Lemma Forall3_map_123 :
  forall R S T U V W (Q: U -> V -> W -> Prop) (f: R -> U) (g: S -> V) (h: T -> W) rs ss ts,
    Forall3 (fun r s t => Q (f r) (g s) (h t)) rs ss ts <->
    Forall3 Q (map f rs) (map g ss) (map h ts).
Proof.
  intros R S T U V W Q f g h rs ss ts.
  rewrite <- Forall3_map_23, <- Forall3_map_1; reflexivity.
Qed.

Lemma Forall3_impl_Forall2_12_Forall2_23 :
  forall (U V W : Type) (R : U -> V -> Prop) (Q : V -> W -> Prop) us vs ws,
    Forall3 (fun u v w => R u v -> Q v w) us vs ws ->
    Forall2 R us vs -> Forall2 Q vs ws.
Proof.
  intros U V W R Q us vs ws hf3 hf2.
  rewrite Forall3_forall in hf3.
  rewrite Forall2_forall_nth_error in *.
  destruct hf3 as (hlen_us_vs & hlen_vs_ws & hrq_us_vs_ws).
  destruct hf2 as [_ hr_us_vs].
  split; auto. intros n v w hnthv hnthw.
  assert (hnthu: exists u, nth_error us n = Some u).
  { apply length_nth_error_some.
    rewrite hlen_us_vs.
    eauto using nth_error_some_length. }
  destruct hnthu; eauto.
Qed.

Lemma Forall3_impl_Forall2_12_Forall2_13 :
  forall (U V W : Type) (R : U -> V -> Prop) (Q : U -> W -> Prop) us vs ws,
    Forall3 (fun u v w => R u v -> Q u w) us vs ws ->
    Forall2 R us vs -> Forall2 Q us ws.
Proof.
  intros U V W R Q us vs ws hf3 hf2.
  rewrite Forall3_permute_12 in hf3.
  rewrite Forall2_flip in hf2.
  eapply Forall3_impl_Forall2_12_Forall2_23;
    eauto; cbn; assumption.
Qed.

Lemma Forall3_impl_Forall2_13_Forall2_12 :
  forall (U V W : Type) (R : U -> W -> Prop) (Q : U -> V -> Prop) us vs ws,
    Forall3 (fun u v w => R u w -> Q u v) us vs ws ->
    Forall2 R us ws -> Forall2 Q us vs.
Proof.
  intros U V W R Q us vs ws hf3 hf2.
  rewrite Forall3_permute_23 in hf3.
  eauto using Forall3_impl_Forall2_12_Forall2_13.
Qed.

Lemma Forall3_impl_Forall2_13_Forall2_23 :
  forall (U V W : Type) (R : U -> W -> Prop) (Q : V -> W -> Prop) us vs ws,
    Forall3 (fun u v w => R u w -> Q v w) us vs ws ->
    Forall2 R us ws -> Forall2 Q vs ws.
Proof.
  intros U V W R Q us vs ws hf3 hf2.
  rewrite Forall3_permute_23 in hf3.
  rewrite Forall2_flip.
  eauto using Forall3_impl_Forall2_12_Forall2_23.
Qed.

Lemma Forall3_impl_Forall2_23_Forall2_12 :
  forall (U V W : Type) (R : V -> W -> Prop) (Q : U -> V -> Prop) us vs ws,
    Forall3 (fun u v w => R v w -> Q u v) us vs ws ->
    Forall2 R vs ws -> Forall2 Q us vs.
Proof.
  intros U V W R Q us vs ws hf3 hf2.
  rewrite Forall3_permute_13 in hf3.
  rewrite Forall2_flip in *.
  eapply Forall3_impl_Forall2_12_Forall2_23; eauto;
    cbn; assumption.
Qed.

Lemma Forall3_impl_Forall2_23_Forall2_13 :
  forall (U V W : Type) (R : V -> W -> Prop) (Q : U -> W -> Prop) us vs ws,
    Forall3 (fun u v w => R v w -> Q u w) us vs ws ->
    Forall2 R vs ws -> Forall2 Q us ws.
Proof.
  intros U V W R Q us vs ws hf3 hf2.
  rewrite Forall3_permute_12 in hf3.
  eauto using Forall3_impl_Forall2_13_Forall2_23.
Qed.

Lemma Forall2_repeat_l : forall (U V : Set) (R : U -> V -> Prop) u vs,
    Forall (R u) vs -> Forall2 R (repeat u (List.length vs)) vs.
Proof.
  intros U V R u vs h;
    induction h as [| v vs ruv hvs ihvs]; cbn; auto.
Qed.

Lemma Forall2_repeat_r : forall (U V : Set) (R : U -> V -> Prop) v us,
    Forall (fun u => R u v) us -> Forall2 R us (repeat v (List.length us)).
Proof.
  intros; rewrite Forall2_flip; auto using Forall2_repeat_l.
Qed.

Lemma Forall2_repeat_both : forall (U V : Set) (R : U -> V -> Prop) u v n,
    R u v -> Forall2 R (repeat u n) (repeat v n).
Proof.
  intros U V R u v n ruv.
  replace n with
    (length (repeat v n)) at 1;
    try (rewrite repeat_length; reflexivity).
  apply Forall2_repeat_l; auto using repeat_Forall.
Qed.

Section Forall_Map_Forall2.
  Variables U V : Type.
  Variable R : U -> V -> Prop.
  Variable f : U -> V.

  Lemma Forall_map_Forall2 : forall us,
      Forall (fun u => R u (f u)) us -> Forall2 R us (map f us).
  Proof.
    intros us h; induction h; cbn; auto.
  Qed.

  Lemma Forall2_map_Forall : forall us,
      Forall2 R us (map f us) -> Forall (fun u => R u (f u)) us.
  Proof.
    intros us h; induction us as [| u us ih]; inv h; auto.
  Qed.

  Local Hint Resolve Forall_map_Forall2 : core.
  Local Hint Resolve Forall2_map_Forall : core.

  Lemma Forall_map_Forall2_iff : forall us,
      Forall (fun u => R u (f u)) us <-> Forall2 R us (map f us).
  Proof. intuition. Qed.
End Forall_Map_Forall2.
