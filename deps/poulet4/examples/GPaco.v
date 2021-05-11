Require Import Paco.paco.
(* Infinite trees, following the development in paco's tutorial.v. *)
CoInductive inftree :=
  | node : inftree -> inftree -> inftree.

Definition tunf t : inftree :=
  match t with node tl tr => node tl tr end.

Lemma tunf_eq : forall t, t = tunf t.
Proof.
  destruct t; auto.
Qed.

Inductive teq_gen teq : inftree -> inftree -> Prop :=
  | _teq_gen : forall t1l t1r t2l t2r (Rl : teq t1l t2l : Prop) (Rr : teq t1r t2r),
                 teq_gen teq (node t1l t1r) (node t2l t2r).
Hint Constructors teq_gen : core.

Definition teq t1 t2 : Prop := paco2 teq_gen bot2 t1 t2.
Hint Unfold teq : core.
Lemma teq_gen_mon: monotone2 teq_gen.
Proof.
 pmonauto.
Qed.
Hint Resolve teq_gen_mon : paco.

CoFixpoint i := node a b
with a := node e e
with b := node e e
with e := node i i.

CoFixpoint ii := node aa bb
with aa := node ee ee
with bb := node ee ee
with ee := node ii ii.

Theorem teq_i_ii:
  teq i ii.
Proof.
  ginit.
  Unshelve.
  3:exact (fun x => x).
  - constructor; auto.
    intros.
    inversion PR; subst.
    constructor; constructor; apply rclo2_base; tauto.
  - gcofix CIH.
    rewrite (tunf_eq i).
    rewrite (tunf_eq ii).
    gstep.
    simpl.
    constructor.
    + gcofix CIHa.
      rewrite (tunf_eq a).
      rewrite (tunf_eq aa).
      gstep.
      simpl.
      constructor;
        gcofix CIHe;
        rewrite (tunf_eq e);
        rewrite (tunf_eq ee);
        gstep;
        simpl;
        constructor; gbase; eauto.
    + gcofix CIHb.
      rewrite (tunf_eq b).
      rewrite (tunf_eq bb).
      gstep.
      simpl.
      constructor;
        gcofix CIHe;
        rewrite (tunf_eq e);
        rewrite (tunf_eq ee);
        gstep;
        simpl;
        constructor; gbase; eauto.
Qed.

Theorem teq_i_ii_better:
  teq i ii.
Proof.
  ginit.
  Unshelve.
  3:exact id.
  {
    unfold id.
    constructor; auto.
    intros.
    inversion PR; subst.
    constructor; constructor; apply rclo2_base; tauto.
  }
  gcofix CIH.
  rewrite (tunf_eq i).
  rewrite (tunf_eq ii).
  gstep.
  simpl.
  rewrite (tunf_eq a), (tunf_eq aa), (tunf_eq b), (tunf_eq bb).
  simpl.
  cut (gpaco2 teq_gen id r r (node e e) (node ee ee)).
  { eauto. }
  rewrite (tunf_eq e), (tunf_eq ee).
  simpl.
  gstep.
  cut (gpaco2 teq_gen id r r (node i i) (node ii ii)).
  { eauto. }
  gstep.
  constructor; gbase; auto.
Qed.

Theorem teq_i_ii_better_without_gpaco:
  teq i ii.
Proof.
  pcofix CIH.
  rewrite (tunf_eq i).
  rewrite (tunf_eq ii).
  pfold.
  simpl.
  rewrite (tunf_eq a), (tunf_eq aa), (tunf_eq b), (tunf_eq bb).
  simpl.
  cut (upaco2 teq_gen r (node e e) (node ee ee)).
  { eauto. }
  rewrite (tunf_eq e), (tunf_eq ee).
  simpl.
  left.
  cut (upaco2 teq_gen r (node i i) (node ii ii)).
  { eauto. }
  left.
  pfold.
  constructor; right; auto.
Qed.

