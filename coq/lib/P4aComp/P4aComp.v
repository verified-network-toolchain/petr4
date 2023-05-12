From Leapfrog Require Import Syntax Ntuple.
From Poulet4.P4cub.Syntax Require Import Syntax P4Field.
From Poulet4.Monads Require Import Option.
From Poulet4.Utils Require Import FinType P4Arith Envn.
Require Import Coq.ZArith.ZArith
        Coq.micromega.Lia
        Coq.Bool.Bool.
Import String.
Open Scope string_scope.
Import ListNotations.
Module P4c := AST.
Module P4a := Leapfrog.Syntax.
(* Open Scope p4a. *)
Open Scope nat_scope.

Definition id := nat.

Module IdGen.
  Definition t := id.
  Definition init : t := 0.
  Definition fresh (k : t) : nat * t :=
    (k, S k).
End IdGen.

Module BoundedIdGen.
  Record t :=
    Mk_t { max: id;
           next: id }.
  Definition init (max: id) : t := {| max := max;
                                      next := 0; |}.
  Definition fresh (env : t) : option (nat * t) :=
    let '(Mk_t max next) := env in
    if Nat.leb next max
    then Some (next, {| max := max; next := next + 1 |})
    else None.
End BoundedIdGen.

Module IdxMap.
  (* Mapping from de Bruijn indices to generated names (nats) *)
  Inductive shape :=
  | Var (x: id)
  | Struct (fields : list id).
  Definition t := list shape.
  Definition init : t := [].
  Definition get_shape (m: t) (idx: nat) : option shape :=
    nth_error m idx.
  Definition add_shape (m: t) (x: shape) : t :=
    x :: m.
End IdxMap.

Definition sz_map :=
  Env.t id nat.

Module CompEnv.
  Record t :=
    { env_idx: IdxMap.t;
      env_sz: sz_map }.

  Definition init: t :=
    {| env_idx := IdxMap.init;
       env_sz := Env.empty _ _ |}.

End CompEnv.


Section P4AComp. 

(* Find size of P4cub Expr.t *)
Fixpoint type_size (e:Typ.t) : option nat:=
  match e with 
    | Typ.Bool => Some 1
    | Typ.VarBit max_width => None
    | Typ.Bit w => Some (N.to_nat w)
    | Typ.Int w => Some (Pos.to_nat w)
    | Typ.Struct isHeader fields => 
      match isHeader with 
      | false => None (* Struct case*)
      | true => 
        List.fold_left (fun accum f => 
          match accum, type_size f with 
            | (Some t1), Some field_size => Some (t1 + field_size)
            | _, _ => None
          end) fields (Some 0)
      end
    | Typ.Var var_name => None
    | Typ.Array _ _ => None
    | Typ.Error => None
  end.

(* Find size of P4Cub Expr.e *)
Fixpoint type_size_e (e:Exp.t) : option nat :=
  match e with 
    | Exp.Bool b => Some 1
    | Exp.VarBit max_width width val => Some (N.to_nat width)
    | Exp.Bit w val => Some (N.to_nat w)
    | Exp.Int w val => Some (Pos.to_nat w)
    | Exp.Var t name x => type_size t
    | Exp.Slice hi lo arg => 
      match type_size_e arg with 
      | Some n1 => Some (Init.Nat.min (1 + Pos.to_nat hi) n1 - Pos.to_nat lo)
      | None => None
      end
    | Exp.Cast t arg => type_size t
    | Exp.Uop t op arg => type_size t
    | Exp.Member result_type mem arg =>
        type_size result_type
    | _ => None
  end.

(* Get the headers from paramargs *)
Definition collect_hdrs_params (gen: IdGen.t) (p: Typ.params) : option (IdGen.t * CompEnv.t) :=
  let add_hdr acc (t:Typ.t) :=
    let* (gen, sz, hdrs) := acc in
    let (next, gen') := IdGen.fresh gen in
    let* size_t := type_size t in
    Some (gen', Env.bind next size_t sz, hdrs ++ [next])%list
  in
  match p with 
  | (_ , PAOut (Typ.Struct false fields)) :: t => 
    let init := Some (gen, Env.empty id nat, []) in
    let* '(gen', sz, shape) := List.fold_left add_hdr fields init in
    mret (gen', {| CompEnv.env_sz := sz;
                   CompEnv.env_idx := IdxMap.add_shape IdxMap.init (IdxMap.Struct shape) |})
  | _ => None
  end.

Definition collect_hdrs_parser (gen: IdGen.t) (p:Top.t) : option (IdGen.t * CompEnv.t) :=
  match p with 
  | Top.Parser _ _ _ _ params _ _ => collect_hdrs_params gen params
  | _ => None
  end.

Definition test_header_from_params := [("hdr",
                                         (PAOut
                                            (Typ.Struct false
                                                        [Typ.Struct true [Typ.Bit 48; Typ.Bit 48; Typ.Bit 16];
   Typ.Struct true [Typ.Bit 40; Typ.Bit 10]])))] : (Typ.params).
  
Compute collect_hdrs_params IdGen.init test_header_from_params.

(* Create Fin type headers, hdrs might not be needed as everything is *)
Definition mk_hdr_type (hdrs: Field.fs nat nat) : Type := Fin.t (List.length hdrs).

(* Create Fin type states *)
(* + 3 at the end for Start, Accept, Reject respectively *)
Definition mk_st_type (states: Field.fs nat Stm.t) : Type := Fin.t (List.length states).

(* Get Fin type headers from list of headers and header name*)
Definition inject_name (hdrs: list (nat * nat)) (hdr: nat) : option (mk_hdr_type hdrs).
Proof.
  destruct (findi (fun kv => Nat.eqb hdr (fst kv)) hdrs) eqn:?.
  - apply Some.
    destruct hdrs.
    + cbv in Heqo. 
      congruence.
    + unfold mk_hdr_type.
      apply @Fin.of_nat_lt with (p := n).
      eapply findi_bound.
      apply Heqo.
  - exact None.
Defined.

(* Get header name from Fin header and list of headers *)
Definition extract_name (hdrs: list (nat * nat)) (h: mk_hdr_type hdrs) : nat.
Proof.
  pose (Fin.to_nat h).
  destruct s as [i pf].
  destruct (List.nth_error hdrs i) eqn:?.
  - exact (fst p).
  - apply nth_error_None in Heqo.
    unfold Field.f in pf.
    lia.
Defined.

(* Get size of header *)
Definition hdr_map (hdrs: list (nat * nat)) (h:mk_hdr_type hdrs) : nat := 
  match Field.get (extract_name hdrs h) hdrs with 
    | Some n => n 
    | None => 0   (* This shouldn't be needed *)
  end.

(* Lemma test : forall {A: Type} (n:nat) h (l: list A), n < (Datatypes.length (h::l)) -> n < (Datatypes.length (h::l)) + 3.
Proof.
  intros. lia.
Qed. *)


(* Get Fin type headers from list of states and state name*)
Definition inject_name_st (states: list (nat * (Stm.t))) (st: nat) : option (mk_st_type states).
Proof.
  destruct (findi (fun kv => Nat.eqb st (fst kv)) states) eqn:?.
  - apply Some.
    destruct states.
    + cbv in Heqo. 
      congruence.
    + unfold mk_hdr_type.
      apply @Fin.of_nat_lt with (p := n).
      (* apply test. *)
      eapply findi_bound.
      apply Heqo.
  - exact None.
Defined.

(* Get state name from Fin state and list of states *)
Definition extract_name_st (states: list (nat * Stm.t)) (st:mk_st_type states) : nat.
Proof.
  pose (Fin.to_nat st).
  destruct s as [i pf].
  destruct (List.nth_error states i) eqn:?.
  - exact (fst p).
  - apply nth_error_None in Heqo.
    unfold Field.f in pf.
    lia.
Defined.  

(* Return size of an expression. Duplicate of type_size_e without returning the option *)
Fixpoint expr_size (env: CompEnv.t) (e:Exp.t) : nat := 
  match e with 
  | Exp.Bool b => 1
  | Exp.VarBit max_width width val => (N.to_nat width)
  | Exp.Bit w val => (N.to_nat w)
  | Exp.Int w val => (Pos.to_nat w)
  | Exp.Var t name idx =>
      match IdxMap.get_shape (CompEnv.env_idx env) idx with
      | Some (IdxMap.Var x) =>
          match Env.find x (CompEnv.env_sz env) with
          | Some sz => sz
          | None => 0
          end
      | Some (IdxMap.Struct _) => 0
      | None => 0
      end
  | Exp.Slice hi lo arg =>
      (Init.Nat.min (1 + Pos.to_nat hi) (expr_size hdrs arg) -
         Pos.to_nat lo)
  | Exp.Cast t arg => 
      match type_size t with 
      | Some size => size
      | None => 0
      end
  | Exp.Uop t op arg =>
      match type_size t with 
      | Some size => size
      | None => 0
      end
  (* result_type seems wrong in p4cub output file *)
  | Exp.Member result_type mem arg => 
      match size_struct_member mem arg with
      | Some field_size => field_size
      | _ => 0
      end
  | _ => 0
  end.

Definition args_sz (hdrs: Field.fs nat nat) (args:Exp.args) : nat := 
  let arg_sz (accum:nat) (arg: Exp.arg):= 
    match arg with 
    | PAIn a => expr_size hdrs a
    | PAOut b => expr_size hdrs b
    | PAInOut b => expr_size hdrs b
    end in 
    List.fold_left arg_sz args 0.

(* Find the size of a P4cub state_block *)
Fixpoint statement_sz (hdrs: Field.fs nat nat) (state: Stm.t) (accum:nat): nat := 
  match state with 
  (* Size of a extract call *)
  | Stm.App (Call.Method "packet_in" "extract" _ _) args => args_sz hdrs args
  | Stm.Seq head tail => statement_sz hdrs tail (statement_sz hdrs head accum)
  | _ => 0
  end.

(* Maps a P4cub state to its size using state_block_sz. (Might not need this definition) *)
Definition st_map (hdrs: Field.fs nat nat) (states: list (nat * Stm.t)) (st:mk_st_type states) : nat := 
  match Field.get (extract_name_st states st) states with 
  | Some st => statement_sz hdrs st 0
  | None => 0
  end.

Compute fun test (hdrs: Field.fs nat nat) => (ESlice _ _ 1 0).

(* Translate P4cub expression to P4a. 
[ctxt] holds mappings from debruijn to P4a Headers*)

(* Add one level to the context for debruijn *)
Definition ctxt_push (ctx: Field.fs nat Exp.t) (e:Exp.t) :=
  let helper elem := 
    match elem with 
    | (x, e') => (x+1, e')
    end in 
  (0,e)::(List.map helper ctx).

  (* The issue is in translating debruijn indices *)

  (* Check list (nat, (nat * nat)). *)
  Check list nat.
Definition ctxt_pop (ctx:Field.fs nat nat) :=
  let helper elem := 
    match elem with 
    | (x, e') => (x-1, e')
    end in
    List.tl (List.map helper ctx).

Fixpoint ctxt_pop_n (ctxt:Field.fs nat nat) (n:nat) :=
  match n with 
  | 0 => ctxt
  | S n' => ctxt_pop_n (ctxt_pop ctxt) n'
  end.

Check option (expr (hdr_map _) (expr_size _ _)).
Fixpoint translate_expr (ctxt: Field.fs nat Exp.t) (hdrs: Field.fs nat nat) (e:Exp.t) : option (expr (hdr_map hdrs) (expr_size hdrs e)) := 
  match e with 
  (* | Exp.Member result_t debruijn (Var ) =>  *)
  (* | Exp.Member result_t debruijn arg_t => 
    if debruijn + 1 == List.length ctxt then 

    else  *)
  | Exp.Slice hi lo arg => 
      match translate_expr ctxt hdrs arg with
        | Some e1 => Some (ESlice _ e1 (Pos.to_nat hi) (Pos.to_nat lo) )
        | None => None
      end
  | _ => None
  end.

Definition coerce_size {Hdr: Type} {H_sz: Hdr -> nat} {sz: nat} (e: Syntax.expr H_sz sz) (sz': nat) : option (Syntax.expr H_sz sz').
Proof.
  destruct (Nat.eq_dec sz sz').
  - rewrite <- e0. apply Some. apply e.
  - apply None.
Defined. 

Fixpoint extract_trans (s:Stm.t) : option (Stm.t * Trns.t) :=
  match s with 
  | Stm.Trans t => Some (Stm.Skip, t)
  | Stm.Seq head tail => 
    match extract_trans tail with 
    | Some (tail, t) => Some (Stm.Seq head tail, t)
    | None => None
    end
  | _ => None (* Parser states presumably must end with transitions*)
  end.

(* Translate transition statements *)
Definition translate_trans (hdrs: Field.fs nat nat) (states:Field.fs nat Stm.t) 
(trans:Trns.t) : option (transition (mk_st_type states) (hdr_map hdrs)) :=
  match trans with 
    | Trns.Direct st => 
      match (st:Lbl.t) with 
      | Lbl.Accept => Some (TGoto (hdr_map hdrs) (inr true))
      | Lbl.Reject => Some (TGoto (hdr_map hdrs) (inr false))
      | Lbl.Start => 
        match inject_name_st states 0 with
        | Some start_st => Some (TGoto (hdr_map hdrs) (inl start_st))
        | None => None 
        end
      | Lbl.Name st_name => 
        match inject_name_st states st_name with
        | Some start_st => Some (TGoto (hdr_map hdrs) (inl start_st))
        | None => None 
        end
      end
    | Trns.Select discriminee default cases => None
  end.


(* Fixpoint transform_st (ctxt: Field.fs nat Exp.t) (s:Stm.t) : prod (Field.fs nat Exp.t) Stm.t:=
  match s with 
  | Stm.Seq s1 s2 => 
    match transform_st ctxt s1 with 
    | ctxt', s' => 
  | _ => s, ctxt
  end. *)

(* Need function for finding header associated with an expression *)
Fixpoint translate_st (hdrs: Field.fs nat nat) (s:Stm.t): option (op (hdr_map hdrs)):= 
  match s with 
  | Stm.Skip => Some (OpNil _)
  (* | Stm.SVardecl x expr _ =>
    match inject_name hdrs x with 
    | Some hdr => 
      match expr with 
      | inl typ => Some (OpNil _) 
      | inr e => 
        match translate_expr hdrs e with 
        | Some e1 => 
          match coerce_size e1 (hdr_map hdrs hdr) with 
          | Some e2 => Some (OpAsgn hdr e2)
          | None => None
          end
        | None => None
        end
      end
    | None => None
    end *)
  (* | Stmt.SAssign lhs rhs _ => 
    match (translate_expr hdrs lhs), (translate_expr hdrs rhs) with 
      | Some (EHdr hdr), Some e1 => OpAsgn hdr e1
      |  
    end *)
  | Stm.Seq s1 s2 => 
    match (translate_st hdrs s1), (translate_st hdrs s2) with 
    | Some st1, Some st2 => Some (OpSeq st1 st2)
    | _, _ => None
    end
  (* | Stm.App (Call.Method "packet_in" "extract" _ _) args => 
    match inject_name hdrs 
  Some (OpExtract (hdr_map hdrs)) *)
    (* | Stmt.SExternMethodCall "packet_in" "extract" _ {|paramargs := params; rtrns := _|} _ => (* Packet extract calls *) 
      match params with 
      | (_, PAOut (Expr.EExprMember _ h _ _))::[] => (* extract only returns PAOut?*)
        match inject_name hdrs h with 
          | Some header => Some (OpExtract (hdr_map hdrs) header)
          | None => None
        end
      | _ => None
      end  *)
  (* Find header associated with lhs *)
  (* | Stmt.SAssign lhs rhs i => translate_expr hdrs  *)
  | _ => None
  end.

(* Get all parser declarations from the program *)
Fixpoint get_parsers (prog: list Top.t) (accum:list Top.t): list (Top.t) :=
match prog with 
  | nil => accum
  | (Top.Parser name cparam expr_cparams eparams params start states)::t => 
  get_parsers t ((Top.Parser name cparam expr_cparams eparams params start states)::accum)
  | _::t => get_parsers t accum
end.

(* Assumes only one parser *)
Definition find_main_parser (prog : list Top.t) : option Top.t :=
  let parsers := get_parsers prog [] in 
  match parsers with  
  | [h] => Some (h)
  | _ => None
  end.

Definition find_states (parser:Top.t) : Field.fs nat Stm.t :=
  match parser with 
  | Top.Parser name cparam expr_cparams eparams params start states => 
    let iterate accum state := (List.length accum, state)::accum in 
    List.fold_left iterate states []
  | _ => []
  end.

Definition find_hdrs (prog:Top.t) : Field.fs nat nat :=
   match collect_hdrs_parser prog with 
   | Some headers => headers
   | None => []
   end.

Definition fold_option {A} (l: list (option A)) :=
  let helper accum elem :=
    match elem, accum with 
    | Some val, Some accum' => Some (val::accum')%list
    | _, _=> None
    end in 
    List.fold_left helper l (Some []).
(* Definition translate_state (state_name:string)
    (hdrs: F.fs string nat) (states:F.fs string (Parser.state_block tags_t)) (st: Parser.state_block tags_t) : option (state (mk_st_type states) (hdr_map hdrs)) :=
    match st with 
    | {|Parser.stmt:=stmt; Parser.trans:=pe|} =>   
      match translate_st hdrs stmt, translate_trans hdrs states pe with 
        | Some t_stmt, Some transition => Some ({| st_op := t_stmt; st_trans := transition|})
        | _, _ => None
      end
    end. *)

Definition translate_state (hdrs:Field.fs nat nat) (states:Field.fs nat Stm.t) (st : Stm.t * Trns.t) : option (state (mk_st_type states) (hdr_map hdrs)):= 
  match st with 
  | (st', trans') => 
    match translate_st hdrs st', translate_trans hdrs states trans' with 
    | Some t_stmt, Some transition => Some ({| st_op := t_stmt; st_trans := transition|})
    | _, _ => None
    end
  end.

Definition translate_parser (parser:Top.t) : option (list (state (mk_st_type (find_states parser)) (hdr_map (find_hdrs parser)))) :=
  let hdrs := find_hdrs parser in 
  let all_states := find_states parser in 
  (* Get all Stm.t from current parser *)
  let all_states_temp : list Stm.t := List.map snd (all_states) in 
  (* Extract all transitions from  *)
  let all_states_temp' : option (list (Stm.t * Trns.t)) := fold_option (List.map extract_trans all_states_temp) in 
    match all_states_temp' with 
    | Some P4cub_states => fold_option (List.map (translate_state hdrs all_states) P4cub_states)
    | None => None
    end.
End P4AComp.

(* 
ctxt => maps debruijn to headers in P4A
hdrs => maps headers to their respective sizes

TODO: 

Look at 2nd arg of 4th arg of TParser
get TStruct => collect header + name => map to nat

Expr.param -> 
petr4 typecheck -exportp4 _.p4 
poulet4 compile

header field accesses => ESlice

convert Z => list of bools for cases selection
Z_to_binary
*)
