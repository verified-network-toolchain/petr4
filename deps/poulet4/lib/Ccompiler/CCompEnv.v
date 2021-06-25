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
  composites : (list Ctypes.composite_definition);
  identGenerator : IdentGen.generator;
}.

Definition add_temp (env: ClightEnv) (temp: string) (t: Ctypes.type)
: ClightEnv := 
  let (gen', new_ident) := IdentGen.gen_next env.(identGenerator) in
  {|
  identMap := Env.bind temp new_ident env.(identMap);
  temps := (new_ident, t)::(env.(temps));
  vars := env.(vars);
  composites := env.(composites);
  identGenerator := gen'
  |}.

Definition add_var (env: ClightEnv) (var: string) (t: Ctypes.type)
: ClightEnv := 
  let (gen', new_ident) := IdentGen.gen_next env.(identGenerator) in
  {|
  identMap := Env.bind var new_ident env.(identMap);
  temps := env.(vars);
  vars := (new_ident, t)::(env.(temps));
  composites := env.(composites);
  identGenerator := gen'
  |}.

Definition add_composite_typ 
  (env: ClightEnv)
  (su: struct_or_union)
  (m: members)
  (a: attr)
  : ClightEnv :=
  let (gen', new_ident) := IdentGen.gen_next env.(identGenerator) in
  {|
  identMap := env.(identMap);
  temps := env.(vars);
  vars := env.(temps);
  composites := (Composite new_ident su m a)::env.(composites);
  identGenerator := gen'
  |}.



Definition find_ident (env: ClightEnv) (name: string)
: option AST.ident :=
  Env.find name env.(identMap). 

(* 
Definition eq_su (su1 su2: struct_or_union) : bool :=
  match su1, su2 with
  | Struct, Struct
  | Union, Union => true
  | _, _ => false
  end. *)

(* 
Fixpoint eq_mem (m1 m2: members) : bool := 
  match m1, m2 with
  | nil, nil => true
  | h1::t1 , h2::t2 => 
    match h1, h2 with
    | (id1, t) *)
Definition eq_id (id1 id2: ident)
: bool.
  Admitted.
Definition eq_composite (comp1 comp2: Ctypes.composite_definition)
: bool.
  Admitted.
  
  
Fixpoint find_composite_from_list 
  (comp: Ctypes.composite_definition)
  (composites: list Ctypes.composite_definition)
  : option ident := 
  match composites with
  | nil => None
  | h::tl => if(eq_composite comp h) then Some (name_composite_def h) 
             else find_composite_from_list comp tl
  end.

Fixpoint composite_of_ident_from_list
  (id: ident)
  (composites: list Ctypes.composite_definition)
  : option Ctypes.composite_definition := 
  match composites with
  | nil => None
  | h::tl => if eq_id (name_composite_def h) id 
             then Some h
             else composite_of_ident_from_list id tl 
  end.

Definition ident_of_composite 
  (comp: Ctypes.composite_definition)
  (env: ClightEnv)
  : option ident :=
  find_composite_from_list comp env.(composites).

Definition composite_of_ident
  (id: ident)
  (env: ClightEnv)
  : option Ctypes.composite_definition := 
  composite_of_ident_from_list id env.(composites).
