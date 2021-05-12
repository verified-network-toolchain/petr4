Require Import Poulet4.P4automata.P4automaton.
Require Import Coq.Lists.List.

Program Definition concat (l: p4automaton) (r: p4automaton) (r_start: states r) : p4automaton :=
  {|
    store := store l * store r ;
    states := states l + states r ;
    size := fun s =>
      match s with
      | inl ls => l.(size) ls
      | inr rs => r.(size) rs
      end ;
    update := fun st bs '(s_l, s_r) =>
      match st with
      | inl st' => (l.(update) st' bs s_l, s_r)
      | inr st' => (s_l, r.(update) st' bs s_r)
      end ;
    transitions := fun st '(s_l, s_r) =>
      match st with
      | inl st' =>
        match l.(transitions) st' s_l with
        | inl st'' => inl (inl st'')
        | inr true => inl (inr r_start)
        | inr false => inr false
        end
      | inr st' =>
        match r.(transitions) st' s_r with
        | inl st'' => inl (inr st'')
        | inr b => inr b
        end
      end ;
  |}.
Next Obligation.
  destruct s.
  - apply l.
  - apply r.
Qed.

Definition concat_config_l
  {l r: p4automaton} {r_start store_r}
  (c: configuration l) : configuration (concat l r r_start) :=
  let '(state, store_l, bs) := c in
  match state with
  | inl st => (inl (inl st), (store_l, store_r), bs)
  | inr b => (inr b, (store_l, store_r), bs)
  end.

Definition concat_config_r
  {l r: p4automaton} {r_start store_l}
  (c: configuration r) : configuration (concat l r r_start) :=
  let '(state, store_r, bs) := c in
  match state with
  | inl st => (inl (inr st), (store_l, store_r), bs)
  | inr b => (inr b, (store_l, store_r), bs)
  end.

Lemma accepted_concat:
  forall l r state_l store_l state_r store_r bs_pref bs_suff,
  accepted (a := l) (inl state_l, store_l, nil) bs_pref ->
  accepted (a := r) (inl state_r, store_r, nil) bs_suff ->
  accepted (a := concat l r state_r) (inl (inl state_l), (store_l, store_r), nil) (bs_pref ++ bs_suff).
Admitted.
