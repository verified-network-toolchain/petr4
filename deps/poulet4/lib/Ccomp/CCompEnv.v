From compcert Require Import Clight Ctypes Integers Cop AST Clightdefs.
From RecordUpdate Require Import RecordSet.
Require Import Poulet4.P4cub.Syntax.Syntax.
Require Import Poulet4.Ccomp.IdentGen.
Require Import Poulet4.Ccomp.Petr4Runtime.
Require Import Poulet4.Utils.Envn.
Require Import Poulet4.Monads.Result Poulet4.Monads.State.
Require Import Coq.Strings.String.
Require Import Poulet4.Utils.Util.Utiliser.
Require Import Coq.PArith.BinPosDef Coq.PArith.BinPos
        Coq.ZArith.BinIntDef Coq.ZArith.BinInt
        Coq.Classes.EquivDec Coq.Program.Program.
Require Import Coq.Init.Decimal.
Require Import Field.
Import Clightdefs.ClightNotations.
Local Open Scope clight_scope.
Open Scope N_scope.
Open Scope string_scope.
Local Open Scope Z_scope.
Open Scope positive_scope.

Import RecordSetNotations.

Notation "'{{' x 'with' y ':=' z '}}'" := (x <| y := z |>).

Fail Notation "'{{' x 'with' y ':=' z ; .. ; v ':=' w '}}'"
  := (.. (x <| y := z |>) .. <| v := w |>).
  
Notation "'{{' x 'with' y ':=' z ; v ':=' w '}}'"
  := (x <| y := z |> <| v := w |>).

Notation "'{{' x 'with' y ':=' z ; v ':=' w ; t ':=' u '}}'"
  := (x <| y := z |> <| v := w |> <| t := u |>).

Section CEnv.
  Definition standard_metadata_t :=
    Composite
      $"standard_metadata_t" Struct
      [ Member_plain $"ingress_port" (tptr (Tstruct _BitVec noattr)) ;
        Member_plain $"egress_spec" (tptr (Tstruct _BitVec noattr)) ;
        Member_plain $"egress_port" (tptr (Tstruct _BitVec noattr)) ;
        Member_plain $"instance_type" (tptr (Tstruct _BitVec noattr)) ;
        Member_plain $"packet_length" (tptr (Tstruct _BitVec noattr)) ;
        Member_plain $"enq_timestamp" (tptr (Tstruct _BitVec noattr)) ;
        Member_plain $"enq_qdepth" (tptr (Tstruct _BitVec noattr)) ;
        Member_plain $"deq_timedelta" (tptr (Tstruct _BitVec noattr)) ;
        Member_plain $"deq_qdepth" (tptr (Tstruct _BitVec noattr)) ;
        Member_plain $"ingress_global_timestamp" (tptr (Tstruct _BitVec noattr)) ;
        Member_plain $"egress_global_timestamp" (tptr (Tstruct _BitVec noattr)) ;
        Member_plain $"mcast_grp" (tptr (Tstruct _BitVec noattr)) ;
        Member_plain $"egress_rid" (tptr (Tstruct _BitVec noattr)) ;
        Member_plain $"checksum_error" (tptr (Tstruct _BitVec noattr)) ;
        Member_plain $"parser_error" tuint ;
        Member_plain $"priority" (tptr (Tstruct _BitVec noattr))] noattr.
  
  Definition standard_metadata_cub_fields := [
      (*ingress_port:*) Expr.TBit (Npos 9) ;
      (*egress_spec:*) Expr.TBit (Npos 9) ;
      (*egress_port:*) Expr.TBit (Npos 9) ;
      (*instance_type:*) Expr.TBit (Npos 32) ;
      (*packet_length:*) Expr.TBit (Npos 32) ;
      (*enq_timestamp*) Expr.TBit (Npos 32) ;
      (*enq_qdepth*) Expr.TBit (Npos 19) ;
      (*deq_timedelta*) Expr.TBit (Npos 32) ;
      (*deq_qdepth*) Expr.TBit (Npos 19) ;
      (*ingress_global_timestamp*) Expr.TBit (Npos 48) ;
      (*egress_global_timestamp*) Expr.TBit (Npos 48) ;
      (*mcast_grp*) Expr.TBit (Npos 16) ;
      (*egress_rid*) Expr.TBit (Npos 16) ;
      (*checksum_error*) Expr.TBit (Npos 1) ;
      (*parser_error*) Expr.TError ;
      (*priority*) Expr.TBit (Npos 3) ].

  Definition standard_metadata_cub := 
    Expr.TStruct standard_metadata_cub_fields false.
  
  Arguments gvar_info {_}.
  Arguments gvar_init {_}.
  Arguments gvar_readonly {_}.
  Arguments gvar_volatile {_}.
  Global Instance eta_globvar (V : Type) : Settable (globvar V) :=
    settable! (@mkglobvar V)
    < gvar_info ; gvar_init ; gvar_readonly ; gvar_volatile >.

  (* TODO: how to address De Bruijn indices? *)

  (* TODO: need to make instance (De Bruijn) names
     to Clight idents. *)

  (** In P4cub there are several different namespaces:
      - (expression) types.
      - expressions.
      - functions.
      - actions.
      - tables.
      - parser states.
      - top-level declarations of parsers, controls, & externs.
      - parser instances.
      - control instances.
      - extern instances.
      In clight all of these become members
      of the same namespace. Many p4cub constructs
      such as instances and actions get compiled
      to functions. In clight, expressions and functions
      share the same namespace. *)
  Record ClightEnv : Type :=
    mkClightEnv
      { (** P4cub term identifiers to clight identifiers. *)
        varMap : list AST.ident

      ; (** P4cub function names to clight idents. *)
        funMap : Env.t string AST.ident

      ; (** P4cub action names to clight idents. *)
        actMap : Env.t string AST.ident

      ; (** P4cub table names to clight idents. *)
        tblMap : Env.t string AST.ident

      ; (** P4cub parser state names to clight ident. *)
      (* TODO: need to be cleared after each parser is compiled *)
        parser_stateMap : list AST.ident
                       
      ; (** P4cub string identifiers to clight identifiers. *)
        topMap : Env.t string AST.ident
                       
      ; (** P4cub control instance names to clight identifiers. *)
        control_instanceMap : list AST.ident

      ; (** P4cub parser instance names to clight identifiers. *)
        parser_instanceMap : list AST.ident

      ; (** P4cub extern instance names to clight identifiers. *)
        extern_instanceMap : list AST.ident
                                 
      ; (** Available temps and their types. *)
        temps : (list (AST.ident * Ctypes.type))
                  
      ; (** Available variables and their types. *)    
        vars : (list (AST.ident * Ctypes.type))
                 
      ; (** P4cub types associated with clight type defs (headers, structs) *)
        composites : (list (Expr.t * Ctypes.composite_definition))
                       
      ; (** Name generator counter. *) (* TODO maybe use state monad instead? *)
        identGenerator : IdentGen.generator
                           
      ; (** Clight idents to clight functions. *)
        fenv : Env.t AST.ident Clight.function
                     
      ; (** Contains arguments and their temps used for copy in copy out. *)
        tempOfArg :
        list
          (AST.ident (** Clight param. *)
           * AST.ident (** Temp variable assigned to first ident *))
          
      ; (* TODO: maybe remove, not needed, unused? *)
        instantiationCarg : TopDecl.constructor_args
                              
      ; (** Used for main instantiation,
            now main function explicitly written,
            may still be used,
            a dummy function clight needs. *)
        maininit: Clight.statement
                    
      ; (** Global variables and their types. *)
        globvars: (list (AST.ident * globvar Ctypes.type))

      ; (** Maps literal ints in p4cub to global variable name of string in clight. *)
        numStrMap : Env.t Z AST.ident
                          
      ; (** Maps the name to their corresponding top declarations like parser or control. *)
        topdecltypes : Env.t string TopDecl.d

      ; (** Table names to tables. *)
        tables :
        Env.t
          string
          ((list (Expr.t * string)) * (list string) (** actions *))

      ; (** Parser states are functions.
            These are parser's args.
            Each state function takes these args. *)
        top_args : (list Clight.expr)

      ; (** Maps the name of extern obects to the name of their extern type. *)
        extern_instance_types : list string

      ; (** For v1 model, expected name to be printed in C.
            V1 model needs to know type of header. *)
        v1model_H : ident

      ; (** V1 model needs to know type of meta data *)
        v1model_M : ident }.

  (** Record-update boiler-plate. *)
  Global Instance etaClightEnv : Settable _ :=
    settable! mkClightEnv
    < varMap ; funMap ; actMap ; tblMap
  ; parser_stateMap ; topMap ; control_instanceMap
  ; parser_instanceMap ; extern_instanceMap
  ; temps ; vars ; composites
  ; identGenerator ; fenv ; tempOfArg
  ; instantiationCarg ; maininit ; globvars
  ; numStrMap ; topdecltypes ; tables ; top_args
  ; extern_instance_types ; v1model_H ; v1model_M >.

  Definition newClightEnv : ClightEnv :=
    {| varMap := []
    ; funMap := Env.empty _ _
    ; actMap := Env.empty _ _
    ; tblMap := Env.empty _ _
    ; parser_stateMap := []
    ; topMap := Env.empty _ _
    ; control_instanceMap := []
    ; parser_instanceMap := []
    ; extern_instanceMap := []
    ; temps := []
    ; vars := []
    ; composites := [(standard_metadata_cub,standard_metadata_t)]
    ; identGenerator := IdentGen.gen_init
    ; fenv := Env.empty _ _
    ; tempOfArg := Env.empty _ _
    ; instantiationCarg := []
    ; maininit := Clight.Sskip
    ; globvars := []
    ; numStrMap :=  Env.empty _ _
    ; topdecltypes := Env.empty _ _
    ; tables := Env.empty _ _
    ; top_args := []
    ; extern_instance_types := []
    ; v1model_H := xH
    ; v1model_M := xH |}.

  Definition top_bind (env: ClightEnv) (name: string) (id: ident) : ClightEnv 
    := {{ env with topMap := Env.bind name id env.(topMap) }}.
  
  Definition var_bind (env: ClightEnv) (id: ident) : ClightEnv 
    := {{ env with varMap := id :: env.(varMap) }}.

  Definition add_temp (env: ClightEnv) (t: Ctypes.type) : ClightEnv :=
    let (gen', new_ident) := IdentGen.gen_next env.(identGenerator) in
    {{ env with varMap := new_ident :: env.(varMap)
     ; temps := (new_ident, t) :: env.(temps)
     ; identGenerator := gen' }}.

  (** TODO: maybe incorrect :(. *)
  Definition
    add_temp_arg
    (env: ClightEnv)
    (t: Ctypes.type) (oldid : AST.ident) : ClightEnv := 
    let (gen', new_ident) := IdentGen.gen_next env.(identGenerator) in
    {{ env with vars := (new_ident, t)::env.(vars)
     ; tempOfArg := (oldid,new_ident) :: env.(tempOfArg)
     ; identGenerator := gen' }}.

  Definition add_temp_nameless (t: Ctypes.type) : State ClightEnv ident :=
    let* env := get_state in
    let (gen', new_ident) := IdentGen.gen_next env.(identGenerator) in
    put_state {{ env with temps := (new_ident, t)::(env.(temps))
               ; identGenerator := gen' }};;
    mret new_ident.

  Definition add_var (env: ClightEnv) (t: Ctypes.type) : ClightEnv := 
    let (gen', new_ident) := IdentGen.gen_next env.(identGenerator) in
    {{ env with varMap := new_ident :: env.(varMap)
     ; identGenerator := gen' }}.
  
  Definition add_composite_typ 
    (env: ClightEnv)
    (p4t : Expr.t)
    (composite_def : Ctypes.composite_definition): ClightEnv := 
    env <| composites := (p4t, composite_def) :: env.(composites) |>.

  Definition add_tpdecl 
    (env: ClightEnv) 
    (name: string)
    (decl: TopDecl.d) : ClightEnv := 
    let (gen', new_ident) := IdentGen.gen_next env.(identGenerator) in
    {{ env with topMap := Env.bind name new_ident env.(topMap)
     ; identGenerator := gen' }}.

  Definition
    add_function 
    (env: ClightEnv) 
    (name: string) 
    (f: Clight.function): ClightEnv :=
    (* TODO: why isn't ident generator used here. *)
  let new_ident := $name in
  {{ env with funMap := Env.bind name new_ident env.(funMap)
   ; fenv := Env.bind new_ident f env.(fenv) }}.

  Definition
    update_function
    (env: ClightEnv)
    (name: string)
    (f: Clight.function) : ClightEnv :=
    match Env.find name env.(funMap) with
    | None => env
    | Some idt => env <| fenv := Env.bind idt f env.(fenv) |>
    end.                     
  
  Definition
    add_extern_instance_type
    (env: ClightEnv)
    (type: string) : ClightEnv :=
    env <| extern_instance_types := type :: env.(extern_instance_types) |>.
  
  Definition clear_extern_instance_types (env: ClightEnv) : ClightEnv :=
    env <| extern_instance_types := [] |>.

  Fixpoint to_C_dec_str_unsigned (dec: uint): list init_data * Z :=
    match dec with
    | Nil => (Init_int8(Int.repr 0)::[], 1%Z)
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
    (key : list (Expr.t * string))
    (actions : list string) : ClightEnv :=
    let (gen', new_id) := IdentGen.gen_next env.(identGenerator) in
    let gvar :=
      {| gvar_info := (Tstruct _Table noattr)
      ; gvar_init := []
      ; gvar_readonly := false
      ; gvar_volatile := false |} in
    {{ env with tblMap := Env.bind name new_id env.(tblMap)
     ; identGenerator := gen' ; globvars := (new_id, gvar) :: env.(globvars) }}.

  (* FIXME!
  Definition
    add_control_instance
    (env: ClightEnv) (instance: string) : ClightEnv :=
    env <| expected_instances := instance :: env.(expected_instances) |>. *)
  
  Definition new_ident : State ClightEnv ident :=
    let* env := get_state in
    let (gen', new_ident) := IdentGen.gen_next env.(identGenerator) in
    put_state (env <| identGenerator := gen' |>) ;; mret new_ident.

  Definition clear_temp_vars (env: ClightEnv) : ClightEnv :=
    {{ env with temps := []; vars := [] }}.
  
  Definition set_temp_vars (from: ClightEnv) (to: ClightEnv) : ClightEnv :=
    {{ to with temps := from.(temps) ; vars := from.(vars)
     ; tempOfArg := from.(tempOfArg) }}.

  Definition
    set_instantiate_cargs
    (env: ClightEnv) (cargs: TopDecl.constructor_args) : ClightEnv :=
    env <| instantiationCarg := cargs |>.
 
  Definition set_main_init (env: ClightEnv) (init: Clight.statement) : ClightEnv :=
    env <| maininit := init |>.

  Definition
    set_top_args (env: ClightEnv) (args: list Clight.expr) : ClightEnv := 
    env <| top_args := args |>.

  Definition find_var (env: ClightEnv) (x : nat) : Result.result AST.ident :=
    match nth_error env.(varMap) x with
    | Some x => Result.ok x
    | None   => Result.error "unbound p4cub variable"
    end.

  (* FIXME!
  Definition find_ident (env: ClightEnv) (name: string)
    : Result.result AST.ident :=
    match Env.find name env.(identMap) with 
    | None => Result.error "name does not exist in env"
    | Some id => Result.ok id
    end. *)
  
  Definition find_ident_temp_arg (env: ClightEnv) (name: nat)
    : Result.result (AST.ident*AST.ident) :=
    match nth_error env.(tempOfArg) name with
    | None => Result.error "argument name does not exist in env"
    | Some (id1,id2) => Result.ok (id1,id2)
    end.

  Fixpoint
    lookup_composite_rec
    (composites : list (Expr.t * composite_definition))
    (p4t: Expr.t) : Result.result composite_definition :=
    match composites with
    | nil => Result.error "can't find the composite"
    | (head, comp) :: tl => if (head == p4t) 
                          then Result.ok comp 
                          else lookup_composite_rec tl p4t
    end.

  Definition
    lookup_composite
    (env: ClightEnv)
    (p4t: Expr.t) : Result.result composite_definition :=
    lookup_composite_rec env.(composites) p4t.

  Fixpoint
    lookup_composite_id_rec
    (composites : list (Expr.t * composite_definition))
    (id: ident): Result.result composite_definition :=
    match composites with
    | nil => Result.error "can't find the composite by id"
    | (head, comp) :: tl => if Pos.eqb (name_composite_def comp) id
                          then Result.ok comp 
                          else lookup_composite_id_rec tl id
    end.
  
  Definition
    lookup_composite_id
    (env: ClightEnv) (id: ident) : Result.result composite_definition :=
    lookup_composite_id_rec env.(composites) id.

  Fixpoint
    set_H_rec
    (composites :  list (Expr.t * composite_definition))
    (p4t: Expr.t) : Result.result ident := 
  match composites with
  | nil => Result.error "can't find the composite in Set_H"
  | (head, comp) :: tl => if (head == p4t)  then 
                          match comp with 
                          | Composite id su m a => 
                              Result.ok id
                          end
                        else   
                          set_H_rec tl p4t
  end.

  Definition set_H (env: ClightEnv) (p4t: Expr.t) : Result.result ClightEnv :=
    let^ H_id := set_H_rec env.(composites) p4t in
    env <| v1model_H := H_id |>.

  Definition get_H (env: ClightEnv) := env.(v1model_H).

  Fixpoint
    set_M_rec
    (composites :  list (Expr.t * composite_definition))
    (p4t: Expr.t) : Result.result ident := 
    match composites with
    | nil => Result.error "can't find the composite in Set_M"
    | (head, comp) :: tl => if (head == p4t) then
                            match comp with 
                            | Composite id su m a => 
                                Result.ok id
                            end
                          else  
                            (set_M_rec tl p4t)
    end.
  
  Definition set_M (env: ClightEnv) (p4t: Expr.t) : Result.result ClightEnv :=
    let^ M_id := set_M_rec env.(composites) p4t in
    env <| v1model_M := M_id |>.

  Definition get_M (env: ClightEnv) := env.(v1model_M).

  Definition lookup_function (env: ClightEnv) (name: string)
    : Result.result (ident * Clight.function) :=
    let* fid :=
      Result.from_opt
        (Env.find name env.(funMap))
        "failed to lookup the function id" in
    let^ f :=
      Result.from_opt
        (Env.find fid env.(fenv))
        "failed to lookup the function" in (fid, f).

  Definition lookup_action_function (env: ClightEnv) (name: string)
    : Result.result (ident * Clight.function) :=
    let* fid :=
      Result.from_opt
        (Env.find name env.(actMap))
        "failed to lookup the function id" in
    let^ f :=
      Result.from_opt
        (Env.find fid env.(fenv))
        "failed to lookup the function" in (fid, f).
  
  Definition lookup_parser_instance_function (env : ClightEnv) (name: nat)
    : Result.result (ident * Clight.function) :=
    let* pid :=
      Result.from_opt
        (nth_error env.(parser_instanceMap) name)
        "failed to lookup the parser instance id" in
    let^ f :=
      Result.from_opt
        (Env.find pid env.(fenv))
        "failed to lookup the function" in (pid, f).

  Definition lookup_control_instance_function (env : ClightEnv) (name: nat)
    : Result.result (ident * Clight.function) :=
    let* cid :=
      Result.from_opt
        (nth_error env.(control_instanceMap) name)
        "failed to lookup the parser instance id" in
    let^ f :=
      Result.from_opt
        (Env.find cid env.(fenv))
        "failed to lookup the function" in (cid, f).

  Definition lookup_topdecl (env: ClightEnv) (name: string) : Result.result TopDecl.d := 
    Result.from_opt
      (Env.find name env.(topdecltypes))
      "failed to lookup the top declaration".

  Fixpoint lookup_type_rec (temps : list (AST.ident * Ctypes.type)) (id: ident)
    : Result.result Ctypes.type :=
    match temps with
    | [] => Result.error "failed to lookup the type"
    | (i, t) :: tl => if (i == id)
                    then Result.ok t 
                    else lookup_type_rec tl id
    end.

  Definition lookup_temp_type (env: ClightEnv) (id : AST.ident)
    : Result.result Ctypes.type := lookup_type_rec env.(temps) id.

  Definition lookup_var_type (env: ClightEnv) (id : AST.ident)
    : Result.result Ctypes.type := lookup_type_rec env.(vars) id.

  (* FIXME!
  Definition lookup_expected_instance_types (env: ClightEnv) (name: nat)
    : option string := nth_error env.(expected_instance_types) 0. *)
  
  Definition
    find_BitVec_String
    (val: Z) : State ClightEnv ident :=
    let* env := get_state in
    match Env.find val env.(numStrMap) with 
    | Some id => mret id
    | None =>
        let (gen', new_id) := IdentGen.gen_next env.(identGenerator) in
        let dec := Z.to_int val in
        let (inits, length) := to_C_dec_str dec in
        let gvar :=
          {| gvar_info := (tarray tschar length);
            gvar_init := inits;
            gvar_readonly := false;
            gvar_volatile := false |} in
        put_state {{ env with globvars := (new_id, gvar) :: env.(globvars)
                   ; numStrMap := Env.bind val new_id env.(numStrMap) }} ;;
        mret new_id
    end.
  
  Definition find_table (env: ClightEnv) (name: string) 
    : Result.result
        (ident * list (Expr.t * string) * list string) := 
    match Env.find name env.(tblMap), Env.find name env.(tables) with
    | Some id, Some (keys, actions) => Result.ok (id, keys, actions)
    | _, _ => Result.error "can't find table"
    end .

  Definition find_extern_type (env: ClightEnv) (name: nat)
    : Result.result string :=
      Result.from_opt
        (nth_error env.(extern_instance_types) name)
        "can't find extern name".

  Definition get_instantiate_cargs (env: ClightEnv) : TopDecl.constructor_args := 
    env.(instantiationCarg).

  Definition get_top_args (env: ClightEnv) : list (Clight.expr) := env.(top_args).
  
  Definition get_vars (env: ClightEnv) : list (AST.ident * Ctypes.type) := env.(vars).
  
  Definition get_temps (env: ClightEnv) : list (AST.ident * Ctypes.type) := env.(temps).

  (* TODO: correct? *)
  Definition get_functions (env: ClightEnv)
    : Result.result (list (AST.ident * Clight.function)) := 
    sequence
      (List.map (lookup_function env) (Env.keys env.(funMap))).
  
  Definition get_composites (env: ClightEnv) : list (Ctypes.composite_definition):= 
    List.map snd env.(composites).

  Definition get_globvars (env: ClightEnv) : list (AST.ident * globvar Ctypes.type)
  := env.(globvars).

  Definition composite_nth (comp: composite_definition) (n : nat)
    : Result.result ident :=
    match comp with
    | (Composite _ _ m _) =>
        match List.nth_error m n with
        | Some member => Result.ok (name_member (member))
        | None => Result.error "composite field can't be found" 
        end
    end.
End CEnv.
