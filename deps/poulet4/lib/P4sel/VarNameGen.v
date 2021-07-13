Require Import Coq.Numbers.DecimalString.
Require Import Coq.Strings.String.
Require Import Coq.Init.Decimal.
Require Import Coq.Init.Nat.
Definition t : Type :=  nat.
Definition new_env : t := 
  0.
Definition new_var (env: t) : string * t :=
  (NilZero.string_of_uint (Nat.to_uint env),  env+1).