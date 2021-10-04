Set Warnings "-custom-entry-overridden".
From compcert Require Import Clight Ctypes Integers Cop AST Clightdefs.
Require  Poulet4.P4cub.Syntax.Syntax.
Require Import Poulet4.Ccomp.IdentGen.
Require Import Poulet4.P4cub.Envn.
Require Import Coq.Strings.String.
Require Import Poulet4.P4cub.Util.Utiliser.
Require Import Poulet4.P4sel.P4sel.
Require Import Coq.ZArith.BinIntDef.
Import Clightdefs.ClightNotations.

Local Open Scope clight_scope.
Local Open Scope string_scope.
Module P := AST.P4cub.
Module E := P.Expr.
Section CEnv.
  Variable (tags_t: Type).
  Record ClightEnv : Type := {
    identMap : Env.t string AST.ident; (*contains name and their original references*)
    temps : (list (AST.ident * Ctypes.type));
    vars : (list (AST.ident * Ctypes.type));
    composites : (list (E.t * Ctypes.composite_definition));
    identGenerator : IdentGen.generator;
    fenv: Env.t string Clight.function;
    tempOfArg : Env.t string (AST.ident* AST.ident); (*contains arguments and their temps used for copy in copy out*)
    instantiationCarg : P4sel.Expr.constructor_args tags_t;
    maininit: Clight.statement;
    globvars: (list (AST.ident * globvar Ctypes.type))
  }.

  Definition newClightEnv : ClightEnv :=
    {|
    identMap := Env.empty string AST.ident;
    temps := [];
    vars := [];
    composites := [];
    identGenerator := IdentGen.gen_init;
    fenv := Env.empty string Clight.function;
    tempOfArg := Env.empty string (AST.ident* AST.ident);
    instantiationCarg := [];
    maininit := Clight.Sskip;
    globvars := [];
    |}.

  Definition bind (env: ClightEnv) (name: string) (id: ident) : ClightEnv 
  := 
    {|
    identMap := Env.bind name id env.(identMap);
    temps := (env.(temps));
    vars := env.(vars);
    composites := env.(composites);
    identGenerator := env.(identGenerator);
    fenv := env.(fenv);
    tempOfArg := env.(tempOfArg);
    instantiationCarg := env.(instantiationCarg);
    maininit := env.(maininit);
    globvars := env.(globvars);
    |}.



  Definition add_temp (env: ClightEnv) (temp: string) (t: Ctypes.type)
  : ClightEnv := 
    let (gen', new_ident) := IdentGen.gen_next env.(identGenerator) in
    {|
    identMap := Env.bind temp new_ident env.(identMap);
    temps := (new_ident, t)::(env.(temps));
    vars := env.(vars);
    composites := env.(composites);
    identGenerator := gen';
    fenv := env.(fenv);
    tempOfArg := env.(tempOfArg);
    instantiationCarg := env.(instantiationCarg);
    maininit := env.(maininit);
    globvars := env.(globvars);
    |}.

  Definition add_temp_arg (env: ClightEnv) (temp: string) (t: Ctypes.type) (oldid : AST.ident)
  : ClightEnv := 
    let (gen', new_ident) := IdentGen.gen_next env.(identGenerator) in
    {|
    identMap := env.(identMap);
    temps := (env.(temps));
    vars := (new_ident, t)::env.(vars);
    composites := env.(composites);
    identGenerator := gen';
    fenv := env.(fenv);
    tempOfArg := Env.bind temp (oldid,new_ident) env.(tempOfArg);
    instantiationCarg := env.(instantiationCarg);
    maininit := env.(maininit);
    globvars := env.(globvars);
    |}.



  Definition add_temp_nameless (env: ClightEnv) (t: Ctypes.type)
  : ClightEnv * ident := 
    let (gen', new_ident) := IdentGen.gen_next env.(identGenerator) in
    ({|
    identMap := env.(identMap);
    temps := (new_ident, t)::(env.(temps));
    vars := env.(vars);
    composites := env.(composites);
    identGenerator := gen';
    fenv := env.(fenv);
    tempOfArg := env.(tempOfArg);
    instantiationCarg := env.(instantiationCarg);
    maininit := env.(maininit);
    globvars := env.(globvars);
    |}, new_ident).



  Definition add_var (env: ClightEnv) (var: string) (t: Ctypes.type)
  : ClightEnv := 
    let (gen', new_ident) := IdentGen.gen_next env.(identGenerator) in
    {|
    identMap := Env.bind var new_ident env.(identMap);
    temps := env.(temps);
    vars := (new_ident, t)::(env.(vars));
    composites := env.(composites);
    identGenerator := gen';
    fenv := env.(fenv);
    tempOfArg := env.(tempOfArg);
    instantiationCarg := env.(instantiationCarg);
    maininit := env.(maininit);
    globvars := env.(globvars);
    |}.

  Definition add_composite_typ 
    (env: ClightEnv)
    (p4t : E.t)
    (composite_def : Ctypes.composite_definition): ClightEnv := 
    {|
    identMap := env.(identMap);
    temps := env.(temps);
    vars := env.(vars);
    composites := (p4t, composite_def) :: env.(composites);
    identGenerator := env.(identGenerator);
    fenv := env.(fenv);
    tempOfArg := env.(tempOfArg);
    instantiationCarg := env.(instantiationCarg);
    maininit := env.(maininit);
    globvars := env.(globvars);
    |}
    .

  Definition add_function 
  (env: ClightEnv) 
  (name: string) 
  (f: Clight.function): ClightEnv
  := 
  let new_ident := $name in
  {|
  identMap := Env.bind name new_ident env.(identMap);
  temps := env.(temps);
  vars := env.(vars);
  composites := env.(composites);
  identGenerator := env.(identGenerator);
  fenv := Env.bind name f env.(fenv);
  tempOfArg := env.(tempOfArg);
  instantiationCarg := env.(instantiationCarg);
  maininit := env.(maininit);
  globvars := env.(globvars);
  |}.

  Definition update_function
  (env: ClightEnv)
  (name: string)
  (f: Clight.function) : ClightEnv
  := 
  {|
  identMap := env.(identMap);
  temps := env.(temps);
  vars := env.(vars);
  composites := env.(composites);
  identGenerator := env.(identGenerator);
  fenv := Env.bind name f env.(fenv);
  tempOfArg := env.(tempOfArg);
  instantiationCarg := env.(instantiationCarg);
  maininit := env.(maininit);
  globvars := env.(globvars);
  |}.

  Definition new_ident
  (env: ClightEnv) : ClightEnv * ident := 
  let (gen', new_ident) := IdentGen.gen_next env.(identGenerator) in
  ({|
  identMap := env.(identMap);
  temps := env.(temps);
  vars := env.(vars);
  composites := env.(composites);
  identGenerator := gen';
  fenv := env.(fenv);
  tempOfArg := env.(tempOfArg);
  instantiationCarg := env.(instantiationCarg);
  maininit := env.(maininit);
  globvars := env.(globvars);
  |}, new_ident ).

  Definition clear_temp_vars (env: ClightEnv) : ClightEnv :=
  {|
    identMap := env.(identMap);
    temps := [];
    vars := [];
    composites := env.(composites);
    identGenerator := env.(identGenerator);
    fenv := env.(fenv);
    tempOfArg := [];
    instantiationCarg := env.(instantiationCarg);
    maininit := env.(maininit);
    globvars := env.(globvars);
  |}.

  Definition set_temp_vars (from: ClightEnv) (to: ClightEnv) : ClightEnv :=
  {|
    identMap := to.(identMap);
    temps := from.(temps);
    vars := from.(vars);
    composites := to.(composites);
    identGenerator := to.(identGenerator);
    fenv := to.(fenv);
    tempOfArg := from.(tempOfArg);
    instantiationCarg := to.(instantiationCarg);
    maininit := to.(maininit);
    globvars := to.(globvars);
  |}.  

  Definition add_bitvec_string (env: ClightEnv) (val : list init_data) : ClightEnv * ident := 
    let globvar := {|
      gvar_info := (tarray tschar (Z.of_nat (List.length val)));
      gvar_init := val;
      gvar_readonly := true;
      gvar_volatile := false
    |} in 
    let (gen', new_ident) := IdentGen.gen_next env.(identGenerator) in
    ({|
    identMap := env.(identMap);
    temps := env.(temps);
    vars := env.(vars);
    composites := env.(composites);
    identGenerator := gen';
    fenv := env.(fenv);
    tempOfArg := env.(tempOfArg);
    instantiationCarg := env.(instantiationCarg);
    maininit := env.(maininit);
    globvars := (new_ident, globvar)::env.(globvars);
    |}, new_ident )
    .
  

  Definition set_instantiate_cargs (env: ClightEnv) (cargs: P4sel.Expr.constructor_args tags_t) : ClightEnv :=
  {|
    identMap := env.(identMap);
    temps := env.(temps);
    vars := env.(vars);
    composites := env.(composites);
    identGenerator := env.(identGenerator);
    fenv := env.(fenv);
    tempOfArg := env.(tempOfArg);
    instantiationCarg := cargs;
    maininit := env.(maininit);
    globvars := env.(globvars);
  |}.  

  Definition get_instantiate_cargs (env: ClightEnv) : P4sel.Expr.constructor_args tags_t := 
    env.(instantiationCarg).
  Definition set_main_init (env: ClightEnv) (init: Clight.statement) : ClightEnv :=
  {|
    identMap := env.(identMap);
    temps := env.(temps);
    vars := env.(vars);
    composites := env.(composites);
    identGenerator := env.(identGenerator);
    fenv := env.(fenv);
    tempOfArg := env.(tempOfArg);
    instantiationCarg := env.(instantiationCarg);
    maininit := init;
    globvars := env.(globvars);
  |}.  

  Definition get_main_init (env: ClightEnv) : Clight.statement := 
    env.(maininit).

  Definition find_ident (env: ClightEnv) (name: string)
  : option AST.ident :=
    Env.find name env.(identMap). 
  Definition find_ident_temp_arg (env: ClightEnv) (name: string)
    : option (AST.ident*AST.ident) :=
      Env.find name env.(tempOfArg). 
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
  (* Definition eq_id (id1 id2: ident)
  : bool.
    Admitted. *)
  (* Definition eq_composite (comp1 comp2: Ctypes.composite_definition)
  : bool.
    Admitted.
    *)
  Fixpoint  lookup_composite_rec (composites : list (E.t * composite_definition)) (p4t: E.t): option composite_definition :=
    match composites with
    | nil => None
    | (head, comp) :: tl => if (head == p4t) 
                            then Some comp 
                            else lookup_composite_rec tl p4t
    end.

  Definition lookup_composite (env: ClightEnv) (p4t: E.t) : option composite_definition :=
    lookup_composite_rec env.(composites) p4t.

  Fixpoint  lookup_composite_id_rec (composites : list (E.t * composite_definition)) (id: ident): option composite_definition :=
    match composites with
    | nil => None
    | (head, comp) :: tl => if (name_composite_def comp == id)
                            then Some comp 
                            else lookup_composite_id_rec tl id
    end.

  Definition lookup_composite_id (env: ClightEnv) (id: ident) : option composite_definition :=
    lookup_composite_id_rec env.(composites) id.

  (* Fixpoint find_composite_from_list 
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
    composite_of_ident_from_list id env.(composites). *)

  Definition lookup_function (env: ClightEnv) (name: string) : option (Clight.function*ident) := 
    match Env.find name env.(fenv), Env.find name env.(identMap) with
    | Some (f), Some (id)=> Some (f,id)
    | _ , _ => None
    end.


  Fixpoint lookup_type_rec (temps : list (AST.ident * Ctypes.type)) (id: ident): option Ctypes.type :=
    match temps with
    | [] => None
    | (i, t) :: tl => if (i == id)
                            then Some t 
                            else lookup_type_rec tl id
    end.

  Definition lookup_temp_type (env: ClightEnv) (id : AST.ident) : option (Ctypes.type) :=
    lookup_type_rec env.(temps) id.

  Definition lookup_var_type (env: ClightEnv) (id : AST.ident) : option (Ctypes.type) :=
    lookup_type_rec env.(vars) id.

  Definition get_vars (env: ClightEnv) : list (AST.ident * Ctypes.type)
    := env.(vars).
  Definition get_temps (env: ClightEnv) : list (AST.ident * Ctypes.type)
    := env.(temps).

  Definition get_functions (env: ClightEnv) : option (list (AST.ident * Clight.function))
  := 
  let keys := Env.keys env.(fenv) in 
  List.fold_right 
  (fun (key : string) (accumulator: option (list (AST.ident * Clight.function))) 
    => match accumulator, lookup_function env key with
      | Some l, Some (f, id) => Some ((id,f)::l) 
      | _ , _ => None
      end) (Some []) keys.

  Definition get_composites (env: ClightEnv) : list (Ctypes.composite_definition):= 
    List.map snd env.(composites).

End CEnv.