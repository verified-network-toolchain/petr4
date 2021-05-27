Require Import String.
Require Import HAList.

Inductive hdr_ref: Type :=
| HRVar (var: string)
| HRField (hdr: hdr_ref) (field: string).

Inductive state_name: Type := 
| SNName (s: string)
| SNStart.

Definition state_ref: Type := state_name + bool.
    
Record sel_case: Type :=
  { sc_val: list bool;
    sc_st: state_ref }.
                        
Inductive transition: Type :=
| TGoto (state: state_ref)
| TSel (cond: hdr_ref) (cases: list sel_case) (default: string).

Record state: Type :=
  { st_hdr: hdr_ref;
    st_trans: transition }.

Definition automaton (states: list state_name) := 
  HAList.t (List.map (fun (s: state_name) => (s, state)) states).

Definition t: Type :=
  { states: list state_name & automaton states }.
