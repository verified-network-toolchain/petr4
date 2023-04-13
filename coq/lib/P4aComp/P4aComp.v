From Leapfrog Require Import Syntax Ntuple.
From Poulet4.P4cub.Syntax Require Import Syntax P4Field.
From Poulet4.Utils Require Import FinType P4Arith.
Require Import Coq.ZArith.ZArith
        Coq.micromega.Lia
        Coq.Bool.Bool.
Import String.
Open Scope string_scope.
Module P4c := AST.
Module P4a := Leapfrog.Syntax.
(* Open Scope p4a. *)
Open Scope nat_scope.

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

Print List.nth_error.

Definition size_struct_member (mem:nat) (arg:Exp.t) : option nat:=
  match arg with 
  | Exp.Var (Typ.Struct _ fields) _ _ => 
    match List.nth_error fields mem with 
    | Some field => type_size field
    | None => None
    end
  | _ => None
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
      | Some n1 => Some (Init.Nat.min (1 + Pos.to_nat hi) n1 -
    Pos.to_nat lo)
      | None => None
      end
    | Exp.Cast t arg => type_size t
    | Exp.Uop t op arg => type_size t
    (* result_type seems wrong in p4cub output file *)
    | Exp.Member result_type mem arg => 
      match size_struct_member mem arg with
        | Some field_size => Some field_size
        | _ => None
      end
    | _ => None
  end.

(* Definition collect_hdrs_str5uct *)


(* Get the headers from paramargs *)
Definition collect_hdrs_params (p:Typ.params) : option (Field.fs nat nat) :=
  let add_hdr hdrs (t:Typ.t) := 
    match hdrs with 
    | Some headers => 
      match type_size t with 
      | Some size_t => Some ((List.length headers, size_t)::headers)
      | None => None 
      end
    | None => None
    end in 
  match p with 
  | (_ , PAOut (Typ.Struct false fields))::t => 
    List.fold_left add_hdr fields (Some [])
  | _ => None
  end.

(* Note this works for V1model -> as it assumes all Out fields are headers *)
Definition collect_hdrs_parsers (p: list Top.t) : option (Field.fs nat nat) := 
  let collect_hdrs_parser accum parser:= 
    match accum, parser with 
    | Some accum_headers, Top.Parser _ _ _ _ params _ _ => 
      match collect_hdrs_params params with 
      | Some headers => Some (headers ++ accum_headers)%list
      | None => None
      end
    | _, _ => None
    end in 
  List.fold_left collect_hdrs_parser p (Some []).
  

Definition test_header_from_params := [("hdr",
(PAOut
  (Typ.Struct false
  [Typ.Struct true [Typ.Bit 48; Typ.Bit 48; Typ.Bit 16]])))] : (Typ.params).
  
  Compute collect_hdrs_params test_header_from_params.

(* Create Fin type headers, hdrs might not be needed as everything is *)
Definition mk_hdr_type (hdrs: Field.fs nat nat) : Type := Fin.t (List.length hdrs).

(* Create Fin type states *)
(* + 3 at the end for Start, Accept, Reject respectively *)
Definition mk_st_type (states: Field.fs nat Stm.t) : Type := Fin.t (List.length states).
  Print findi.
  Print fold_lefti.
  Search findi.
  Lemma findi_length_bound_inner :
    forall {A} (l: list A) (pred: A -> bool) (j k : nat) (r: option nat) (i : nat),
    fold_left
        (fun '(n, b) (a : A) =>
          (S n,
          match b with
        | Some _ => b
        | None => if pred a then Some n else None
        end)) l (j, r) = (k, Some i) ->
        (forall r', r = Some r' -> r' < j) ->
        i < Datatypes.length l + j.
    Proof.
      induction l; intros.
      - simpl in *.
        inversion H; subst.
        specialize (H0 i eq_refl).
        congruence.
      - cbn in *.
        destruct (pred a).
        + Admitted. 


Lemma findi_length_bound :
  forall {A: Type} pred (l: list A) i,
    findi pred l = Some i ->
    i < Datatypes.length l.
Proof.
  (* unfold findi.
  unfold fold_lefti.
  intros until 0.
  revert i.
  generalize (0, @None nat).
  Print findi.
  unfold findi.

   induction l. 
  - intros. cbv in *. congruence.
  - intros. unfold findi in H. unfold fold_lefti in H. cbn in H.
  destruct (pred a).
    + unfold findi in IHl. unfold fold_lefti in IHl. apply IHl in H. cbn in *.    *)
Admitted.

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
      eapply findi_length_bound.
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
      eapply findi_length_bound.
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
Fixpoint expr_size (hdrs: Field.fs nat nat) (e:Exp.t) : nat := 
  match e with 
    | Exp.Bool b => 1
    | Exp.VarBit max_width width val => (N.to_nat width)
    | Exp.Bit w val => (N.to_nat w)
    | Exp.Int w val => (Pos.to_nat w)
    | Exp.Var t name x => 
      (*  May need a type_size that is not wrapped in an option *)
      match type_size t with 
      | Some size => size
      | None => 0
      end
    | Exp.Slice hi lo arg => (Init.Nat.min (1 + Pos.to_nat hi) (expr_size hdrs arg) -
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
  (* | Stm.SExternMethodCall "packet_in" "extract" _ {|paramargs := params; rtrns := _|} _ => (* Packet extract calls *) 
    match params with 
    | (_, PAOut (Expr.EExprMember h _ _ _))::[] => (* extract only returns PAOut?*)
      match type_size [] h with 
      | Some n => n
      | None => 0
      end
    | _ => 0
    end  *)
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

Check option (expr (hdr_map _) (expr_size _ _)).
Check ESlice 2 _ _ _.
Print ESlice.
Fixpoint translate_expr (hdrs: Field.fs nat nat) (e:Exp.t): option (expr (hdr_map hdrs) (expr_size hdrs e)) := 
  match e with 
  | Exp.Slice hi lo arg => 
      match translate_expr hdrs arg with
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

(* Translate transition statements *)
Definition translate_trans (hdrs: Field.fs nat nat) (states:Field.fs nat Stm.t) 
(trans:Trns.t ) : option (transition (mk_st_type states) (hdr_map hdrs)) :=
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
Print P4a.state_ref.
Check inl true.
Check state_ref (mk_st_type _).
Check TGoto (hdr_map _) (inl true).

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

(* Assumes only one parser *)
Definition find_states (prog:list Top.t) : list (Stm.t) :=
  match get_parsers prog [] with 
  | [Top.Parser name cparam expr_cparams eparams params start states] => states
  | _ => []
  end.

(* Definition find_hdrs (prog:list Top.t) :  *)

(* Definition translate_parser (prog:Top.t) : option (list (state (mk_st_type (find_states prog)) (hdr_map (find_hdrs prog)))) :=
  let parsers := get_parsers prog in 
  let hdrs := find_hdrs prog in 
  let all_states := find_states prog in 
  match parsers with 
  | [main_parser] => 
    match collect_hdrs_parser parsers with 
    | Some headers 
    let translate_all := List.map (fun '(name, st) => translate_state name hdrs all_states st) in 
    let state_collect accum translated_state := 
      match accum, translated_state with 
      | Some acc, Some st' => Some (st'::acc)
      | _,_ => None
      end in
      List.fold_left state_collect (translate_all all_states) (Some []) 
  | _ => None
  end. *)

(* 
Definition translate_parser (prog:Top.t) : option (list (state (mk_st_type (find_states prog)) (hdr_map (find_hdrs prog)))) :=
  let main_parser := find_main_parser prog in 
  let hdrs := find_hdrs prog in 
  let all_states := find_states prog in 
  match main_parser with 
    | Some (TopDecl.TPParser p _ _ params start states i) => 
      let translate_all := List.map (fun '(name, st) => translate_state name hdrs all_states st) in 
      let state_collect accum translated_state := 
        match accum, translated_state with 
        | Some acc, Some st' => Some (st'::acc)
        | _,_ => None
        end in
        List.fold_left state_collect (translate_all all_states) (Some []) 
    | _ => None
    end.  *)
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
