Require Import Poulet4.P4automata.P4automaton.

Definition concat (l: p4automaton) (r: p4automaton) (r_start: states r) : p4automaton :=
  {|
    store := store l + store r ;
    states := states l + states r ; 
    size := fun s =>
      match s with
      | inl ls => l.(size) ls
      | inr rs => r.(size) rs
      end ;
    update := fun st bs s => 
      match st, s with
      | inl st', inl s' => inl (l.(update) st' bs s')
      | inr st', inr s' => inr (r.(update) st' bs s')
      | _, _ => s
      end ;
    transitions := fun st s => 
      match st, s with 
      | inl st', inl s' => 
        match l.(transitions) st' s' with
        | inl st'' => inl (inl st'')
        | inr true => inl (inr r_start)
        | inr false => inr false
        end
      | inr st', inr s' =>
        match r.(transitions) st' s' with
        | inl st'' => inl (inr st'')
        | inr b => inr b
        end
      | _, _ => inr false
      end ;
  |}.

Definition concat_config_l 
  {l r: p4automaton} {r_start} 
  (c: configuration l) : configuration (concat l r r_start) := 
  let '(state, store, bs) := c in 
  match state with
  | inl st => (inl (inl st), inl store, bs)
  | inr b => (inr b, inl store, bs)
  end.

Definition concat_config_r 
  {l r: p4automaton} {r_start} 
  (c: configuration r) : configuration (concat l r r_start) := 
  let '(state, store, bs) := c in 
  match state with
  | inl st => (inl (inr st), inr store, bs)
  | inr b => (inr b, inr store, bs)
  end.
