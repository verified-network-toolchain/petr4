Set Warnings "-custom-entry-overridden".
From compcert Require Import Clight Ctypes Integers Cop AST Clightdefs.
Require Import Poulet4.P4cub.Syntax.Syntax.
Require Import Poulet4.Ccomp.IdentGen.
Require Import Poulet4.Ccomp.Petr4Runtime.
Require Import Poulet4.Utils.Envn.
Require Import Poulet4.Monads.Monad.
Require Import Poulet4.Monads.Error.
Require Import Coq.Strings.String.
Require Import Poulet4.Utils.Util.Utiliser.
Require Import Coq.ZArith.BinIntDef.
Require Import Coq.Init.Decimal.
Require Import Field.
Import Clightdefs.ClightNotations.
Local Open Scope clight_scope.
Open Scope string_scope.
Local Open Scope Z_scope.

Section CEnv.
  Variable (tags_t: Type).
  Inductive ClightEnv : Type := {
    identMap : Env.t string AST.ident; (*contains name and their original references*)
    temps : (list (AST.ident * Ctypes.type));
    vars : (list (AST.ident * Ctypes.type));
    composites : (list (Expr.t * Ctypes.composite_definition));
    identGenerator : IdentGen.generator;
    fenv: Env.t string Clight.function;
    tempOfArg : Env.t string (AST.ident* AST.ident); (*contains arguments and their temps used for copy in copy out*)
    instantiationCarg : Expr.constructor_args tags_t;
    maininit: Clight.statement;
    globvars: (list (AST.ident * globvar Ctypes.type));
    numStrMap : Env.t Z AST.ident;
    topdecltypes : Env.t string (TopDecl.d tags_t);(*maps the name to their corresponding top declarations like parser or control*)
    tables : Env.t string ((list (AST.Expr.e tags_t * AST.Expr.matchkind))*(list string));
    top_args : (list Clight.expr);
    extern_instances: Env.t string string; (*maps the name of extern obects to the name of their extern type*)
  }.

  Definition newClightEnv : ClightEnv :=
    {|
    identMap := Env.empty _ _;
    temps := [];
    vars := [];
    composites := [];
    identGenerator := IdentGen.gen_init;
    fenv := Env.empty _ _;
    tempOfArg := Env.empty _ _;
    instantiationCarg := [];
    maininit := Clight.Sskip;
    globvars := [];
    numStrMap :=  Env.empty _ _;
    topdecltypes := Env.empty _ _;
    tables := Env.empty _ _;
    top_args := [];
    extern_instances := Env.empty _ _;
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
    numStrMap := env.(numStrMap);
    topdecltypes := env.(topdecltypes);
    tables := env.(tables);
    top_args := env.(top_args);
    extern_instances := env.(extern_instances);
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
    numStrMap := env.(numStrMap);
    topdecltypes := env.(topdecltypes);
    tables := env.(tables);
    top_args := env.(top_args);
    extern_instances := env.(extern_instances);
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
    numStrMap := env.(numStrMap);
    topdecltypes := env.(topdecltypes);
    tables := env.(tables);
    top_args := env.(top_args);
    extern_instances := env.(extern_instances);
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
    numStrMap := env.(numStrMap);
    topdecltypes := env.(topdecltypes);
    tables := env.(tables);
    top_args := env.(top_args);
    extern_instances := env.(extern_instances);
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
    numStrMap := env.(numStrMap);
    topdecltypes := env.(topdecltypes);
    tables := env.(tables);
    top_args := env.(top_args);
    extern_instances := env.(extern_instances);
    |}.

  Definition add_composite_typ 
    (env: ClightEnv)
    (p4t : Expr.t)
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
    numStrMap := env.(numStrMap);
    topdecltypes := env.(topdecltypes);
    tables := env.(tables);
    top_args := env.(top_args);
    extern_instances := env.(extern_instances);
    |}
    .

  Definition add_tpdecl 
    (env: ClightEnv) 
    (name: string)
    (decl: TopDecl.d tags_t): ClightEnv
    := 
    let (gen', new_ident) := IdentGen.gen_next env.(identGenerator) in
    {|
    identMap := Env.bind name new_ident env.(identMap);
    temps := env.(temps);
    vars := env.(vars);
    composites := env.(composites);
    identGenerator := gen';
    fenv := env.(fenv);
    tempOfArg := env.(tempOfArg);
    instantiationCarg := env.(instantiationCarg);
    maininit := env.(maininit);
    globvars := env.(globvars);
    numStrMap := env.(numStrMap);
    topdecltypes := Env.bind name decl env.(topdecltypes);
    tables := env.(tables);
    top_args := env.(top_args);
    extern_instances := env.(extern_instances);
    |}.

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
  numStrMap := env.(numStrMap);
  topdecltypes := env.(topdecltypes);
  tables := env.(tables);
  top_args := env.(top_args);
  extern_instances := env.(extern_instances);
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
  numStrMap := env.(numStrMap);
  topdecltypes := env.(topdecltypes);
  tables := env.(tables);
  top_args := env.(top_args);
  extern_instances := env.(extern_instances);
  |}.

  Definition add_extern_instance 
  (env: ClightEnv)
  (name: string)
  (type: string) : ClightEnv
  :=
  {|
  identMap := env.(identMap);
  temps := env.(temps);
  vars := env.(vars);
  composites := env.(composites);
  identGenerator := env.(identGenerator);
  fenv := env.(fenv);
  tempOfArg := env.(tempOfArg);
  instantiationCarg := env.(instantiationCarg);
  maininit := env.(maininit);
  globvars := env.(globvars);
  numStrMap := env.(numStrMap);
  topdecltypes := env.(topdecltypes);
  tables := env.(tables);
  top_args := env.(top_args);
  extern_instances := Env.bind name type env.(extern_instances);
  |}.

  Fixpoint to_C_dec_str_unsigned (dec: uint): list init_data * Z :=
    match dec with
    | Nil => (Init_int8(Int.repr 0)::[], 1)
    | D0 d => 
        let (l,count) := to_C_dec_str_unsigned d in
        let digit := Init_int8 (Int.repr 48) in
        (digit::l, Z.succ count)
    | D1 d =>
        let (l,count) := to_C_dec_str_unsigned d in
        let digit := Init_int8 (Int.repr 49) in
        (digit::l, Z.succ count)
    | D2 d => 
        let (l,count) := to_C_dec_str_unsigned d in
        let digit := Init_int8 (Int.repr 50) in
        (digit::l, Z.succ count)
    | D3 d => 
        let (l,count) := to_C_dec_str_unsigned d in
        let digit := Init_int8 (Int.repr 51) in
        (digit::l, Z.succ count)
    | D4 d => 
        let (l,count) := to_C_dec_str_unsigned d in
        let digit := Init_int8 (Int.repr 52) in
        (digit::l, Z.succ count)
    | D5 d => 
        let (l,count) := to_C_dec_str_unsigned d in
        let digit := Init_int8 (Int.repr 53) in
        (digit::l, Z.succ count)
    | D6 d => 
        let (l,count) := to_C_dec_str_unsigned d in
        let digit := Init_int8 (Int.repr 54) in
        (digit::l, Z.succ count)
    | D7 d => 
        let (l,count) := to_C_dec_str_unsigned d in
        let digit := Init_int8 (Int.repr 55) in
        (digit::l, Z.succ count)
    | D8 d => 
        let (l,count) := to_C_dec_str_unsigned d in
        let digit := Init_int8 (Int.repr 56) in
        (digit::l, Z.succ count)
    | D9 d => 
        let (l,count) := to_C_dec_str_unsigned d in
        let digit := Init_int8 (Int.repr 57) in
        (digit::l, Z.succ count)
    end.

  Definition to_C_dec_str (dec: int): list init_data * Z :=
    match dec with 
    | Pos d => to_C_dec_str_unsigned d 
    | Neg d => let (l, count) := to_C_dec_str_unsigned d in
              let digit := Init_int8 (Int.repr 45) in
              (digit::l, Z.succ count)
    end.

  Definition add_Table
    (env : ClightEnv)
    (name : string)
    (key : list (AST.Expr.e tags_t * AST.Expr.matchkind))
    (actions : list string) 
    : ClightEnv :=
    let (gen', new_id) := IdentGen.gen_next env.(identGenerator) in
    let gvar :=  {|
    gvar_info := (Tstruct _Table noattr);
    gvar_init := [];
    gvar_readonly := false;
    gvar_volatile := false
    |} in 
    let env' := 
    {|
    identMap := Env.bind name new_id env.(identMap);
    temps := env.(temps);
    vars := env.(vars);
    composites := env.(composites);
    identGenerator := gen';
    fenv := env.(fenv);
    tempOfArg := env.(tempOfArg);
    instantiationCarg := env.(instantiationCarg);
    maininit := env.(maininit);
    globvars := (new_id, gvar) :: env.(globvars);
    numStrMap := env.(numStrMap);
    topdecltypes := env.(topdecltypes);
    tables := Env.bind name (key, actions) env.(tables);
    top_args := env.(top_args);
    extern_instances := env.(extern_instances);
    |} in 
    env'
    .



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
  numStrMap := env.(numStrMap);
  topdecltypes := env.(topdecltypes);
  tables := env.(tables);
  top_args := env.(top_args);
  extern_instances := env.(extern_instances);
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
    numStrMap := env.(numStrMap);
    topdecltypes := env.(topdecltypes);
    tables := env.(tables);
    top_args := env.(top_args);
    extern_instances := env.(extern_instances);
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
    numStrMap := to.(numStrMap);
    topdecltypes := to.(topdecltypes);
    tables := to.(tables);
    top_args := to.(top_args);
    extern_instances := to.(extern_instances);
  |}.  

  Definition set_instantiate_cargs (env: ClightEnv) (cargs: Expr.constructor_args tags_t) : ClightEnv :=
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
    numStrMap := env.(numStrMap);
    topdecltypes := env.(topdecltypes);
    tables := env.(tables);
    top_args := env.(top_args);
    extern_instances := env.(extern_instances);
  |}.  

 
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
    numStrMap := env.(numStrMap);
    topdecltypes := env.(topdecltypes);
    tables := env.(tables);
    top_args := env.(top_args);
    extern_instances := env.(extern_instances);
  |}.  


  Definition set_top_args (env: ClightEnv) (args: list Clight.expr) : ClightEnv := 
  {|
    identMap := env.(identMap);
    temps := env.(temps);
    vars := env.(vars);
    composites := env.(composites);
    identGenerator := env.(identGenerator);
    fenv := env.(fenv);
    tempOfArg := env.(tempOfArg);
    instantiationCarg := env.(instantiationCarg);
    maininit := env.(maininit);
    globvars := env.(globvars);
    numStrMap := env.(numStrMap);
    topdecltypes := env.(topdecltypes);
    tables := env.(tables);
    top_args := args;
    extern_instances := env.(extern_instances);
  |}.  

  (* Definition get_main_init (env: ClightEnv) : Clight.statement := 
    env.(maininit). *)

  Definition find_ident (env: ClightEnv) (name: string)
  : @error_monad string AST.ident :=
    match Env.find name env.(identMap) with 
    | None => err "name does not exist in env"
    | Some id => error_ret id
    end. 
  Definition find_ident_temp_arg (env: ClightEnv) (name: string)
    : @error_monad string (AST.ident*AST.ident) :=
    match Env.find name env.(tempOfArg) with
    | None => err "argument name does not exist in env"
    | Some (id1,id2) => error_ret (id1,id2)
    end. 
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
  Fixpoint  lookup_composite_rec (composites : list (Expr.t * composite_definition)) (p4t: Expr.t): @error_monad string composite_definition :=
    match composites with
    | nil => err "can't find the composite"
    | (head, comp) :: tl => if (head == p4t) 
                            then error_ret comp 
                            else lookup_composite_rec tl p4t
    end.

  Definition lookup_composite (env: ClightEnv) (p4t: Expr.t) : @error_monad string composite_definition :=
    lookup_composite_rec env.(composites) p4t.

  Fixpoint  lookup_composite_id_rec (composites : list (Expr.t * composite_definition)) (id: ident): @error_monad string composite_definition :=
    match composites with
    | nil => err "can't find the composite by id"
    | (head, comp) :: tl => if (name_composite_def comp == id)
                            then error_ret comp 
                            else lookup_composite_id_rec tl id
    end.

  Definition lookup_composite_id (env: ClightEnv) (id: ident) : @error_monad string composite_definition :=
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

  

  Definition lookup_function (env: ClightEnv) (name: string) : @error_monad string (Clight.function*ident) := 
    match Env.find name env.(fenv) , Env.find name env.(identMap) with
    | Some f, Some fid => error_ret (f,fid)
    | _, _ => err "failed to lookup the function"
    end.

  Definition lookup_topdecl (env: ClightEnv) (name: string) : @error_monad string (TopDecl.d tags_t) := 
    match Env.find name env.(topdecltypes) with
    | None => err "failed to lookup the top declaration"
    | Some decl => error_ret decl
    end.
  

  Fixpoint lookup_type_rec (temps : list (AST.ident * Ctypes.type)) (id: ident): @error_monad string Ctypes.type :=
    match temps with
    | [] => err "failed to lookup the type"
    | (i, t) :: tl => if (i == id)
                            then error_ret t 
                            else lookup_type_rec tl id
    end.

  Definition lookup_temp_type (env: ClightEnv) (id : AST.ident) : @error_monad string Ctypes.type :=
    lookup_type_rec env.(temps) id.

  Definition lookup_var_type (env: ClightEnv) (id : AST.ident) : @error_monad string Ctypes.type :=
    lookup_type_rec env.(vars) id.


  
    Definition find_BitVec_String 
    (env: ClightEnv)
    (val: Z)
    : ClightEnv * ident :=
    match Env.find val env.(numStrMap) with 
    | Some id => (env, id)
    | None =>
    let (gen', new_id) := IdentGen.gen_next env.(identGenerator) in
    let dec := Z.to_int val in
    let (inits, length) := to_C_dec_str dec in
    let gvar :=  {|
      gvar_info := (tarray tschar length);
      gvar_init := inits;
      gvar_readonly := false;
      gvar_volatile := false
    |} in
    let env' :=
      {|
      identMap := env.(identMap);
      temps := env.(temps);
      vars := env.(vars);
      composites := env.(composites);
      identGenerator := gen';
      fenv := env.(fenv);
      tempOfArg := env.(tempOfArg);
      instantiationCarg := env.(instantiationCarg);
      maininit := env.(maininit);
      globvars := (new_id, gvar) :: env.(globvars);
      numStrMap := Env.bind val new_id env.(numStrMap);
      topdecltypes := env.(topdecltypes);
      tables := env.(tables);
      top_args := env.(top_args);
      extern_instances := env.(extern_instances);
      |} in 
      (env', new_id)
    end.

  
  Definition find_table (env: ClightEnv) (name: string) 
    : @error_monad
        string
        (AST.ident * (list (AST.Expr.e tags_t * AST.Expr.matchkind))*(list string)) 
    := 
    match Env.find name env.(identMap), Env.find name env.(tables) with
    | Some id, Some (keys, actions) => error_ret (id, keys, actions)
    | _, _ => err "can't find table"
    end .

  Definition find_extern_type (env: ClightEnv) (name: string)
  : @error_monad string string
  := match Env.find name env.(extern_instances) with
    | Some type => error_ret type
    | _ => err "can't find extern name"
  end.

  Definition get_instantiate_cargs (env: ClightEnv) : Expr.constructor_args tags_t := 
    env.(instantiationCarg).

  Definition get_top_args (env: ClightEnv) : list (Clight.expr) :=
    env.(top_args).
  
  Definition get_vars (env: ClightEnv) : list (AST.ident * Ctypes.type)
    := env.(vars).
  Definition get_temps (env: ClightEnv) : list (AST.ident * Ctypes.type)
    := env.(temps).

  Definition get_functions (env: ClightEnv) : @error_monad string (list (AST.ident * Clight.function))
  := 
  let keys := Env.keys env.(fenv) in 
  List.fold_right 
  (fun (key : string) (accumulator: @error_monad string (list (AST.ident * Clight.function))) 
    => 
    let* l := accumulator in
    let* '(f,fid) := lookup_function env key in
    error_ret ((fid,f)::l))
  (error_ret []) keys.

  Definition get_composites (env: ClightEnv) : list (Ctypes.composite_definition):= 
    List.map snd env.(composites).

  Definition get_globvars (env: ClightEnv) : list (AST.ident * globvar Ctypes.type)
  := env.(globvars).


End CEnv.
