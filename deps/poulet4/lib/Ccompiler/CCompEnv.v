From compcert Require Import Clight Ctypes Integers Cop AST.
Require Import Poulet4.Ccompiler.IdentGen.
Require Import Poulet4.P4cub.Envn.
Require Import Coq.Strings.String.
Require Import Poulet4.P4cub.Utiliser.
(*map between string and ident*)
Record ClightEnv : Type := {
  identMap : Env.t string AST.ident;
  temps : (list (AST.ident * Ctypes.type));
  vars : (list (AST.ident * Ctypes.type));
  identGenerator : IdentGen.generator;
}.

Definition add_temp (env: ClightEnv) (temp: string) (t: Ctypes.type)
: ClightEnv := 
  let (gen', new_ident) := IdentGen.gen_next env.(identGenerator) in
  {|
  identMap := Env.bind temp new_ident env.(identMap);
  temps := (new_ident, t)::(env.(temps));
  vars := env.(vars);
  identGenerator := gen'
  |}.

Definition add_var (env: ClightEnv) (var: string) (t: Ctypes.type)
: ClightEnv := 
  let (gen', new_ident) := IdentGen.gen_next env.(identGenerator) in
  {|
  identMap := Env.bind var new_ident env.(identMap);
  temps := env.(vars);
  vars := (new_ident, t)::(env.(temps));
  identGenerator := gen'
  |}.

Definition find_ident (env: ClightEnv) (name: string)
: option AST.ident :=
  Env.find name env.(identMap). 

  