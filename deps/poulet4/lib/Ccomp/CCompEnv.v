From compcert Require Import Clight Ctypes Integers Cop AST Clightdefs.
From RecordUpdate Require Import RecordSet.
Require Import Poulet4.P4cub.Syntax.Syntax.
Require Import Poulet4.Ccomp.IdentGen.
Require Import Poulet4.Ccomp.Petr4Runtime.
Require Import Poulet4.Utils.Envn.
Require Import Poulet4.Monads.Monad.
Require Import Poulet4.Monads.Error.
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
  Instance eta_globvar (V : Type) : Settable (globvar V) :=
    settable! (@mkglobvar V)
    < gvar_info ; gvar_init ; gvar_readonly ; gvar_volatile >.

  (* TODO: Hence forth controls parsers & externs are in the same
     namespace, and their instances share a namespace.
     Need to go over p4cub static and dynamic semantics. *)
  
  (* TODO: how to address De Bruijn indices. *)
  Record ClightEnv : Type :=
    mkClightEnv
      { (** P4cub string identifiers to clight identifiers. *)
        identMap : Env.t string AST.ident

      ; (** P4cub term identifiers to clight identifiers. *)
        varMap : list AST.ident
                        
      ; (** Available temps and their types. *)
        temps : (list (AST.ident * Ctypes.type))
                  
      ; (** Available variables and their types. *)    
        vars : (list (AST.ident * Ctypes.type))
                 
      ; (** P4cub types associated with clight type defs (headers, structs) *)
        composites : (list (Expr.t * Ctypes.composite_definition))
                       
      ; (** Name generator counter. *) (* TODO maybe use state monad instead? *)
        identGenerator : IdentGen.generator
                           
      ; (** P4cub function names to clight functions. *)
        fenv : Env.t string Clight.function
                     
      ; (** Clight instance names to clight functions. *)
        ienv : Env.t string Clight.function
                     
      ; (** Contains arguments and their temps used for copy in copy out. *)
        tempOfArg :
        Env.t
          string (** Param name in p4cub. *)
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
          ((list (Expr.e (* TODO: will be types *) * string)) * (list string) (** actions *))

      ; (** Parser states are functions.
            These are parser's args.
            Each state function takes these args. *)
        top_args : (list Clight.expr)

      ; (** Maps the name of extern obects to the name of their extern type. *)
        extern_instances: list string

      ; (** Instance name in p4cub/clight to
            Instance name in architecture file written in C. *)
        expected_instances : list string

      ; (** For v1 model, expected name to be printed in C.
            V1 model needs to know type of header. *)
        v1model_H : ident

      ; (** V1 model needs to know type of meta data *)
        v1model_M : ident }.

  (** Record-update boiler-plate. *)
  Instance etaClightEnv : Settable _ :=
    settable! mkClightEnv
    < identMap ; varMap ; temps ; vars ; composites
  ; identGenerator ; fenv ; ienv ; tempOfArg
  ; instantiationCarg ; maininit ; globvars
  ; numStrMap ; topdecltypes ; tables ; top_args
  ; extern_instances ; expected_instances
  ; v1model_H ; v1model_M >.

  Definition newClightEnv : ClightEnv :=
    {| identMap := Env.empty _ _
    ; varMap := []
    ; temps := []
    ; vars := []
    ; composites := [(standard_metadata_cub,standard_metadata_t)]
    ; identGenerator := IdentGen.gen_init
    ; fenv := Env.empty _ _
    ; ienv := Env.empty _ _
    ; tempOfArg := Env.empty _ _
    ; instantiationCarg := []
    ; maininit := Clight.Sskip
    ; globvars := []
    ; numStrMap :=  Env.empty _ _
    ; topdecltypes := Env.empty _ _
    ; tables := Env.empty _ _
    ; top_args := []
    ; extern_instances := []
    ; expected_instances := []
    ; v1model_H := xH
    ; v1model_M := xH |}.

  Import RecordSetNotations.

  Notation "'{{' x 'with' y ':=' z '}}'" := (x <| y := z |>).

  Fail Notation "'{{' x 'with' y ':=' z ; .. ; v ':=' w '}}'"
    := (.. (x <| y := z |>) .. <| v := w |>).
  
  Notation "'{{' x 'with' y ':=' z ; v ':=' w '}}'"
    := (x <| y := z |> <| v := w |>).

  Notation "'{{' x 'with' y ':=' z ; v ':=' w ; t ':=' u '}}'"
    := (x <| y := z |> <| v := w |> <| t := u |>).

  Definition ident_bind (env: ClightEnv) (name: string) (id: ident) : ClightEnv 
    := {{ env with identMap := Env.bind name id env.(identMap) }}.
  
  Definition var_bind (env: ClightEnv) (id: ident) : ClightEnv 
    := {{ env with varMap := id :: env.(varMap) }}.

  Definition add_temp (env: ClightEnv) (t: Ctypes.type) : ClightEnv :=
    let (gen', new_ident) := IdentGen.gen_next env.(identGenerator) in
    {{ env with varMap := new_ident :: env.(varMap)
     ; temps := (new_ident, t) :: env.(temps)
     ; identGenerator := gen' }}.
  
  Definition
    add_temp_arg
    (env: ClightEnv) (temp: string)
    (t: Ctypes.type) (oldid : AST.ident) : ClightEnv := 
    let (gen', new_ident) := IdentGen.gen_next env.(identGenerator) in
    {{ env with vars := (new_ident, t)::env.(vars)
     ; tempOfArg := Env.bind temp (oldid,new_ident) env.(tempOfArg)
     ; identGenerator := gen' }}.

  Definition add_temp_nameless (env: ClightEnv) (t: Ctypes.type) : ident * ClightEnv := 
    let (gen', new_ident) := IdentGen.gen_next env.(identGenerator) in
    (new_ident,
      {{ env with temps := (new_ident, t)::(env.(temps))
       ; identGenerator := gen' }}).

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
    {{ env with identMap := Env.bind name new_ident env.(identMap)
     ; identGenerator := gen' }}.

  Definition
    add_function 
    (env: ClightEnv) 
    (name: string) 
    (f: Clight.function): ClightEnv :=
  let new_ident := $name in
  {{ env with identMap := Env.bind name new_ident env.(identMap)
   ; fenv := Env.bind name f env.(fenv) }}.

  Definition
    update_function
    (env: ClightEnv)
    (name: string)
    (f: Clight.function) : ClightEnv :=
    env <| fenv := Env.bind name f env.(fenv) |>.
  
  Definition
    add_extern_instance 
    (env: ClightEnv)
    (type: string) : ClightEnv :=
    env <| extern_instances := type :: env.(extern_instances) |>.
  
  Definition clear_extern_instance (env: ClightEnv) : ClightEnv :=
    env <| extern_instances := [] |>.

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
    (key : list (Expr.e * string))
    (actions : list string) : ClightEnv :=
    let (gen', new_id) := IdentGen.gen_next env.(identGenerator) in
    let gvar :=
      {| gvar_info := (Tstruct _Table noattr)
      ; gvar_init := []
      ; gvar_readonly := false
      ; gvar_volatile := false |} in
    {{ env with identMap := Env.bind name new_id env.(identMap)
     ; identGenerator := gen' ; globvars := (new_id, gvar) :: env.(globvars) }}.
  
  Definition
    add_expected_control 
    (env: ClightEnv) (instance: string) : ClightEnv :=
    env <| expected_instances := instance :: env.(expected_instances) |>.
  
  Definition
    new_ident (env: ClightEnv) : ident * ClightEnv := 
  let (gen', new_ident) := IdentGen.gen_next env.(identGenerator) in
  (new_ident, env <| identGenerator := gen' |>).

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

  Fixpoint
    lookup_composite_rec
    (composites : list (Expr.t * composite_definition))
    (p4t: Expr.t) : @error_monad string composite_definition :=
    match composites with
    | nil => err "can't find the composite"
    | (head, comp) :: tl => if (head == p4t) 
                          then error_ret comp 
                          else lookup_composite_rec tl p4t
    end.

  Definition
    lookup_composite
    (env: ClightEnv)
    (p4t: Expr.t) : @error_monad string composite_definition :=
    lookup_composite_rec env.(composites) p4t.

  Fixpoint
    lookup_composite_id_rec
    (composites : list (Expr.t * composite_definition))
    (id: ident): @error_monad string composite_definition :=
    match composites with
    | nil => err "can't find the composite by id"
    | (head, comp) :: tl => if Pos.eqb (name_composite_def comp) id
                          then error_ret comp 
                          else lookup_composite_id_rec tl id
    end.
  
  Definition
    lookup_composite_id
    (env: ClightEnv) (id: ident) : @error_monad string composite_definition :=
    lookup_composite_id_rec env.(composites) id.

  Fixpoint
    set_H_rec
    (composites :  list (Expr.t * composite_definition))
    (p4t: Expr.t) : @error_monad string ident := 
  match composites with
  | nil => err "can't find the composite in Set_H"
  | (head, comp) :: tl => if (head == p4t)  then 
                          match comp with 
                          | Composite id su m a => 
                              error_ret id
                          end
                        else   
                          set_H_rec tl p4t
  end.

  Definition set_H (env: ClightEnv) (p4t: Expr.t) : @error_monad string ClightEnv :=
    let^ H_id := set_H_rec env.(composites) p4t in
    env <| v1model_H := H_id |>.

  Definition get_H (env: ClightEnv) := env.(v1model_H).

  Fixpoint
    set_M_rec
    (composites :  list (Expr.t * composite_definition))
    (p4t: Expr.t) : @error_monad string ident := 
    match composites with
    | nil => err "can't find the composite in Set_M"
    | (head, comp) :: tl => if (head == p4t) then
                            match comp with 
                            | Composite id su m a => 
                                error_ret id
                            end
                          else  
                            (set_M_rec tl p4t)
    end.
  
  Definition set_M (env: ClightEnv) (p4t: Expr.t) : @error_monad string ClightEnv :=
    let^ M_id := set_M_rec env.(composites) p4t in
    env <| v1model_M := M_id |>.

  Definition get_M (env: ClightEnv) := env.(v1model_M).  

  Definition lookup_function (env: ClightEnv) (name: string)
    : @error_monad string (Clight.function*ident) := 
    match Env.find name env.(fenv) , Env.find name env.(identMap) with
    | Some f, Some fid => error_ret (f,fid)
    | _, _ => err "failed to lookup the function"
    end.

  Definition lookup_topdecl (env: ClightEnv) (name: string) : @error_monad string TopDecl.d := 
    match Env.find name env.(topdecltypes) with
    | None => err "failed to lookup the top declaration"
    | Some decl => error_ret decl
    end.

  Fixpoint lookup_type_rec (temps : list (AST.ident * Ctypes.type)) (id: ident)
    : @error_monad string Ctypes.type :=
    match temps with
    | [] => err "failed to lookup the type"
    | (i, t) :: tl => if (i == id)
                    then error_ret t 
                    else lookup_type_rec tl id
    end.

  Definition lookup_temp_type (env: ClightEnv) (id : AST.ident)
    : @error_monad string Ctypes.type := lookup_type_rec env.(temps) id.

  Definition lookup_var_type (env: ClightEnv) (id : AST.ident)
    : @error_monad string Ctypes.type := lookup_type_rec env.(vars) id.

  Definition lookup_expected_instance (env: ClightEnv) (name: nat)
    : option string := nth_error env.(expected_instances) 0.
  
  Definition
    find_BitVec_String
    (env: ClightEnv) (val: Z) : ClightEnv * ident :=
    match Env.find val env.(numStrMap) with 
    | Some id => (env, id)
    | None =>
        let (gen', new_id) := IdentGen.gen_next env.(identGenerator) in
        let dec := Z.to_int val in
        let (inits, length) := to_C_dec_str dec in
        let gvar :=
          {| gvar_info := (tarray tschar length);
            gvar_init := inits;
            gvar_readonly := false;
            gvar_volatile := false |} in
        let env' :=
          {{ env with globvars := (new_id, gvar) :: env.(globvars)
           ; numStrMap := Env.bind val new_id env.(numStrMap) }} in
        (env', new_id)
    end.
  
  Definition find_table (env: ClightEnv) (name: string) 
    : @error_monad
        string
        (ident * (list (Expr.e * string))*(list string)) := 
    match Env.find name env.(identMap), Env.find name env.(tables) with
    | Some id, Some (keys, actions) => error_ret (id, keys, actions)
    | _, _ => err "can't find table"
    end .

  Definition find_extern_type (env: ClightEnv) (name: nat)
    : @error_monad string string :=
    match nth_error env.(extern_instances) 0 with
    | Some type => error_ret type
    | _ => err "can't find extern name"
    end.

  Definition get_instantiate_cargs (env: ClightEnv) : TopDecl.constructor_args := 
    env.(instantiationCarg).

  Definition get_top_args (env: ClightEnv) : list (Clight.expr) := env.(top_args).
  
  Definition get_vars (env: ClightEnv) : list (AST.ident * Ctypes.type) := env.(vars).
  
  Definition get_temps (env: ClightEnv) : list (AST.ident * Ctypes.type) := env.(temps).

  Definition get_functions (env: ClightEnv)
    : @error_monad string (list (AST.ident * Clight.function)) := 
    let keys := Env.keys env.(fenv) in 
    List.fold_right 
      (fun (key : string)
         (accumulator: @error_monad string (list (AST.ident * Clight.function))) => 
         let* l := accumulator in
         let^ '(f,fid) := lookup_function env key in ((fid,f)::l))
      (error_ret []) keys.
  
  Definition get_composites (env: ClightEnv) : list (Ctypes.composite_definition):= 
    List.map snd env.(composites).

  Definition get_globvars (env: ClightEnv) : list (AST.ident * globvar Ctypes.type)
  := env.(globvars).

  Definition composite_nth (comp: composite_definition) (n : nat)
    : @error_monad string ident :=
    match comp with
    | (Composite _ _ m _) =>
        match List.nth_error m n with
        | Some member => error_ret (name_member (member))
        | None => err "composite field can't be found" 
        end
    end.
End CEnv.
