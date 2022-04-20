
Require Import Coq.Strings.String.
Require Import Poulet4.Utils.Util.StringUtil.
Open Scope string_scope.
Definition t : Type :=  nat.
Definition new_env : t := 
  0.
Definition new_var (env: t) : string * t :=
  ("_p_4_s_e_l_"++(string_of_nat env),  env+1).
