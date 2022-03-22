
Require Import Coq.Strings.String.

Open Scope string_scope.
Parameter string_of_nat : nat -> string.
Definition t : Type :=  nat.
Definition new_env : t := 
  0.
Definition new_var (env: t) : string * t :=
  ("_p_4_s_e_l_"++(string_of_nat env),  env+1).
