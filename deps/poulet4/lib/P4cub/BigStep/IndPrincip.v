Set Warnings "-custom-entry-overridden".
Require Import Poulet4.P4cub.Envn
        Poulet4.P4cub.Syntax.AST
        Poulet4.P4cub.BigStep.Value.Value
        Poulet4.P4cub.BigStep.Semantics
        Coq.ZArith.BinInt.
Import Step P.P4cubNotations Val.ValueNotations.

(** A custom induction principle for
    the expression big-step relation. *)
Section ExprEvalInduction.
  Variable (tags_t: Type).
  
  Variable P : epsilon -> E.e tags_t -> V.v -> Prop.
  
  Hypothesis HBool : forall ϵ b i, P ϵ <{ BOOL b @ i }> ~{ VBOOL b }~.
  
  Hypothesis HBit : forall ϵ w n i, P ϵ <{ w W n @ i }> ~{ w VW n }~.
  
  Hypothesis HInt : forall ϵ w z i, P ϵ <{ w S z @ i }> ~{ w VS z }~.
  
  Hypothesis HVar : forall ϵ x τ i v,
      Env.find x ϵ = Some v ->
      P ϵ <{ Var x:τ @ i }> v.
  (**[]*)
  
  Hypothesis HSlice : forall ϵ e τ hi lo i v v',
      eval_slice hi lo v = Some v' ->
      ⟨ ϵ, e ⟩ ⇓ v ->
      P ϵ e v ->
      P ϵ <{ Slice e:τ [hi:lo] @ i }> v'.
  (**[]*)
  
  Hypothesis HCast : forall ϵ τ e i v v',
      eval_cast τ v = Some v' ->
      ⟨ ϵ, e ⟩ ⇓ v ->
      P ϵ e v ->
      P ϵ <{ Cast e:τ @ i }> v'.
  (**[]*)
  
  Hypothesis HError : forall ϵ err i, P ϵ <{ Error err @ i }> ~{ ERROR err }~.
  
  Hypothesis HMatchkind : forall ϵ mk i,
      P ϵ <{ Matchkind mk @ i }> ~{ MATCHKIND mk }~.
  (**[]*)
  
  Hypothesis HUop : forall ϵ op τ e i v v',
      eval_uop op v = Some v' ->
      ⟨ ϵ, e ⟩ ⇓ v ->
      P ϵ e v ->
      P ϵ <{ UOP op e:τ @ i }> v'.
  
  Hypothesis HBop : forall ϵ op τ1 τ2 e1 e2 i v v1 v2,
      eval_bop op v1 v2 = Some v ->
      ⟨ ϵ, e1 ⟩ ⇓ v1 ->
      P ϵ e1 v1 ->
      ⟨ ϵ, e2 ⟩ ⇓ v2 ->
      P ϵ e2 v2 ->
      P ϵ <{ BOP e1:τ1 op e2:τ2 @ i }> v.
  (**[]*)
  
  Hypothesis HMem : forall ϵ e x τ i v v',
      eval_member x v = Some v' ->
      ⟨ ϵ, e ⟩ ⇓ v ->
      P ϵ e v ->
      P ϵ <{ Mem e:τ dot x @ i }> v'.
  (**[]*)
  
  Hypothesis HTuple : forall ϵ es i vs,
      Forall2 (fun e v => ⟨ ϵ, e ⟩ ⇓ v) es vs ->
      Forall2 (P ϵ) es vs ->
      P ϵ <{ tup es @ i }> ~{ TUPLE vs }~.
  (**[]*)
  
  Hypothesis HStructLit : forall ϵ efs i vfs,
      F.relfs
        (fun te v =>
           let e := snd te in ⟨ ϵ, e ⟩ ⇓ v) efs vfs ->
      F.relfs (fun te v => let e := snd te in P ϵ e v) efs vfs ->
      P ϵ <{ struct { efs } @ i }> ~{ STRUCT { vfs } }~.
  (**[]*)
  
  Hypothesis HHdrLit : forall ϵ efs e i b vfs,
      F.relfs
        (fun te v =>
           let e := snd te in ⟨ ϵ, e ⟩ ⇓ v) efs vfs ->
      F.relfs (fun te v => let e := snd te in P ϵ e v) efs vfs ->
      ⟨ ϵ, e ⟩ ⇓ VBOOL b ->
      P ϵ e ~{ VBOOL b }~ ->
      P ϵ <{ hdr { efs } valid:=e @ i }> ~{ HDR { vfs } VALID:=b }~.
  (**[]*)
  
  Hypothesis HHdrStack : forall ϵ ts hs n ni i vss,
      Forall2
        (fun e bvs =>
           let b := fst bvs in
           let vs := snd bvs in
           ⟨ ϵ, e ⟩ ⇓ HDR { vs } VALID:=b)
        hs vss ->
      Forall2
        (fun e bvs =>
           let b := fst bvs in
           let vs := snd bvs in
           P ϵ e ~{ HDR { vs } VALID:=b}~ )
        hs vss ->
      P ϵ <{ Stack hs:ts[n] nextIndex:=ni @ i }> ~{ STACK vss:ts[n] NEXT:=ni }~.
  (**[]*)
  
  Hypothesis HAccess : forall ϵ e i n index ni ts vss b vs,
      nth_error vss (Z.to_nat index) = Some (b,vs) ->
      ⟨ ϵ, e ⟩ ⇓ STACK vss:ts[n] NEXT:=ni ->
                                       P ϵ e ~{ STACK vss:ts[n] NEXT:=ni }~ ->
                                       P ϵ <{ Access e[index] @ i }> ~{ HDR { vs } VALID:=b }~.
  (**[]*)
  
  (** Custom induction principle for
      the expression big-step relation.
      [Do induction ?H using custom_expr_big_step_ind]. *)
  Definition custom_expr_big_step_ind :
    forall (ϵ : epsilon) (e : E.e tags_t)
      (v : V.v) (Hy : ⟨ ϵ, e ⟩ ⇓ v), P ϵ e v :=
    fix ebsind ϵ e v Hy :=
      let fix lind
              {es : list (E.e tags_t)}
              {vs : list (V.v)}
              (HR : Forall2 (fun e v => ⟨ ϵ, e ⟩ ⇓ v) es vs)
          : Forall2 (P ϵ) es vs :=
          match HR with
          | Forall2_nil _ => Forall2_nil _
          | Forall2_cons _ _ Hh Ht
            => Forall2_cons _ _ (ebsind _ _ _ Hh) (lind Ht)
          end in
      let fix fsind
              {efs : F.fs string (E.t * E.e tags_t)}
              {vfs : F.fs string (V.v)}
              (HRs : F.relfs
                       (fun te v =>
                          let e := snd te in
                          ⟨ ϵ , e ⟩ ⇓ v) efs vfs)
          : F.relfs
              (fun te v => let e := snd te in P ϵ e v)
              efs vfs :=
          match HRs with
          | Forall2_nil _ => Forall2_nil _
          | Forall2_cons _ _ (conj Hx Hhd) Htl
            => Forall2_cons _ _ (conj Hx (ebsind _ _ _ Hhd)) (fsind Htl)
          end in
      let fix ffind
              {es : list (E.e tags_t)}
              {vss : list (bool * F.fs string (V.v))}
              (HRs : Forall2
                       (fun e bvs =>
                          let b := fst bvs in
                          let vs := snd bvs in
                          ⟨ ϵ, e ⟩ ⇓ HDR { vs } VALID:=b)
                       es vss)
          : Forall2
              (fun e bvs =>
                 let b := fst bvs in
                 let vs := snd bvs in
                 P ϵ e ~{ HDR { vs } VALID:=b}~ )
              es vss :=
          match HRs with
          | Forall2_nil _ => Forall2_nil _
          | Forall2_cons _ _ Hhead Htail
            => Forall2_cons _ _ (ebsind _ _ _ Hhead) (ffind Htail)
          end in
      match Hy with
      | ebs_bool _ b i => HBool ϵ b i
      | ebs_bit _ w n i => HBit ϵ w n i
      | ebs_int _ w z i => HInt ϵ w z i
      | ebs_var _ _ τ i _ Hx => HVar _ _ τ i _ Hx
      | ebs_slice _ _ _ _ _ i _ _ Hv He
        => HSlice _ _ _ _ _ i _ _ Hv He (ebsind _ _ _ He)
      | ebs_cast _ _ _ i _ _ Hv He
        => HCast _ _ _ i _ _ Hv He (ebsind _ _ _ He)
      | ebs_error _ err i => HError _ err i
      | ebs_matchkind _ mk i => HMatchkind _ mk i
      | ebs_uop _ _ _ _ i _ _ Hv He
        => HUop _ _ _ _ i _ _ Hv He (ebsind _ _ _ He)
      | ebs_bop _ _ _ _ _ _ i _ _ _ Hv He1 He2
        => HBop _ _ _ _ _ _ i _ _ _ Hv He1 (ebsind _ _ _ He1) He2 (ebsind _ _ _ He2)
      | ebs_mem _ _ _ _ i _ _ Heval He
        => HMem _ _ _ _ i _ _ Heval He (ebsind _ _ _ He)
      | ebs_tuple _ _ i _ HR => HTuple _ _ i _ HR (lind HR)
      | ebs_struct_lit _ _ i _ HR => HStructLit _ _ i _ HR (fsind HR)
      | ebs_hdr_lit _ _ _ i _ _ HR He
        => HHdrLit _ _ _ i _ _ HR (fsind HR) He (ebsind _ _ _ He)
      | ebs_hdr_stack _ _ _ n ni i _ HR
        => HHdrStack _ _ _ n ni i _ HR (ffind HR)
      | ebs_access _ _ i n index ni ts _ _ _ Hnth He
        => HAccess _ _ i n index ni ts _ _ _ Hnth He (ebsind _ _ _ He)
      end.
  (**[]*)
End ExprEvalInduction.

Section ParserExprInduction.
  Variable tags_t : Type.
  Variable P : epsilon -> PR.e tags_t -> PR.state -> Prop.
  
  Hypothesis HGoto : forall ϵ st i,
      P ϵ p{ goto st @ i }p st.
  
  Hypothesis HSelect : forall ϵ e def cases i v
                         st_def vcases,
      ⟨ ϵ, e ⟩ ⇓ v ->
      Forall2
        (fun pe ps =>
           let p := fst pe in
           let p' := fst ps in
           let e := snd pe in
           let s := snd ps in
           p = p' /\ ⦑ ϵ, e ⦒ ⇓ s)
        cases vcases ->
      Forall2 (fun pe ps =>
                 let e := snd pe in
                 let s := snd ps in
                 P ϵ e s) cases vcases ->
      ⦑ ϵ, def ⦒ ⇓ st_def ->
      P ϵ def st_def ->
      let st := match F.find_value (fun p => match_pattern p v) vcases with
                | None => st_def
                | Some st => st
                end in
      P ϵ p{ select e { cases } default:=def @ i }p st.
  
  Definition custom_parser_expr_big_step_ind :
    forall (ϵ : epsilon) (e : PR.e tags_t) (st : PR.state),
      ⦑ ϵ, e ⦒ ⇓ st -> P ϵ e st :=
    fix pebsind ϵ e st H :=
      let fix cases_ind
              {cases : F.fs PR.pat (PR.e tags_t)}
              {vcases : F.fs PR.pat PR.state}
              (Hcases :
                 Forall2
                   (fun pe ps =>
                      let p := fst pe in
                      let p' := fst ps in
                      let e := snd pe in
                      let s := snd ps in
                      p = p' /\ ⦑ ϵ, e ⦒ ⇓ s)
                   cases vcases)
          : Forall2
              (fun pe ps =>
                 let e := snd pe in
                 let s := snd ps in
                 P ϵ e s) cases vcases :=
          match Hcases with
          | Forall2_nil _ => Forall2_nil _
          | Forall2_cons _ _ (conj _ Hcase) Htail
            => Forall2_cons _ _ (pebsind _ _ _ Hcase) (cases_ind Htail)
          end in
      match H with
      | pebs_goto _ st i => HGoto _ st i
      | pebs_select _ _ _ _ i _ _ _ He Hcases Hdef
        => HSelect _ _ _ _ i _ _ _ He
                  Hcases (cases_ind Hcases)
                  Hdef (pebsind _ _ _ Hdef)
      end.
  (**[]*)
End ParserExprInduction.
