From Leapfrog Require Import Syntax Ntuple.
From Poulet4.P4cub.Syntax Require Import Syntax P4Field.
From Poulet4.Utils Require Import FinType P4Arith.
Require Import Coq.ZArith.ZArith
        Coq.micromega.Lia
        Coq.Bool.Bool.
Import String.
Open Scope string_scope.
Module P4c := AST.
Module P4a := Poulet4.P4cub.Syntax.Syntax.
(* Open Scope p4a. *)

Section P4AComp. 
  (* State identifiers. *)
Variable (S: Type).
Context `{S_eq_dec: EquivDec.EqDec S eq}.
Context `{S_finite: @Finite S _ S_eq_dec}.

(* Header identifiers. *)
Variable (H: Type).
Context `{H_eq_dec: EquivDec.EqDec H eq}.
Context `{H_finite: @Finite H _ H_eq_dec}.
Variable (Hdr_sz: H -> nat).

Variable (tags_t : Type).

Fixpoint type_size (ctxt:F.fs string nat) (e:Expr.t) : option nat:=
  match e with 
    | Expr.TBool => Some 1
    | Expr.TBit w => Some (N.to_nat w)
    | Expr.TInt w => Some (Pos.to_nat w)
    | Expr.THeader fields => 
      List.fold_left (fun accum f => 
        match accum, f with 
          | (Some t1), (_, t2) => 
            match type_size ctxt t2 with 
              | Some field_size => Some (t1 + field_size)
              | _ => None
            end
          | _, _ => None
        end) fields (Some 0)
    | Expr.TTuple types => None  (* ? *)
    | Expr.TVar var_name => Field.find_value (String.eqb var_name) ctxt
    | _ => None
  end.

Fixpoint type_size_e (ctxt:F.fs string nat) (e:Expr.e tags_t) : option nat :=
  match e with 
    | Expr.EBool b i => Some 1
    | Expr.EBit w val i => Some (N.to_nat w)
    | Expr.EInt w val i => Some (Pos.to_nat w)
    | Expr.EVar t x i => type_size ctxt t
    | Expr.EHeader fields valid i => 
      List.fold_left (fun accum f => 
        match accum, f with 
          | (Some t1), (_, t2) => 
            match type_size_e ctxt t2 with 
              | Some field_size => Some (t1 + field_size)
              | _ => None
            end
          | _, _ => None
        end) fields (Some 0)
    | _ => None
  end.

Definition digit2string(d:nat) : string :=
  match d with
    | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3"
    | 4 => "4" | 5 => "5" | 6 => "6" | 7 => "7"
    | 8 => "8" | _ => "9"
  end %string.
  
Definition thdr_to_str (e:Expr.t) : option string :=
  let helper (accum:option string) (field:(string * Expr.t)) :=
    let (name, t) := field in  
    match accum, type_size [] t with 
    | Some acc, Some n => Some (acc ++ name ++ (digit2string n))
    | _, _ => None
    end in 
  match e with 
  | Expr.THeader fields => 
    List.fold_left helper fields (Some "")
  | _ => None
  end.
  Check (List.length []) == 1.
(* Definition collect_hdrs_expr (ctxt: F.fs string nat) (e:Expr.e tags_t) :  *)

Fixpoint collect_hdrs_stmt (ctxt:F.fs string nat) (st: P4c.Stmt.s tags_t) : option (F.fs string nat) :=
  match st with 
  | Stmt.SVardecl x expr _ => 
      match expr with 
      | inl typ =>
          match type_size ctxt typ with
          | Some sz => Some ((x, sz)::ctxt)
          | None => None
          end
      | inr e => 
          match type_size_e ctxt e with
          | Some sz => Some ((x, sz)::ctxt)
          | None => None
          end
      end
  | Stmt.SExternMethodCall "packet_in" "extract" _ {|paramargs := params; rtrns := _|} _ => (* Packet extract calls *) 
      match params with 
      | (_, PAOut (Expr.EExprMember header _ _ _))::[] => (* extract only returns PAOut?*)
            match thdr_to_str header, type_size ctxt header with
            | Some x, Some sz => Some ((x,sz)::ctxt)
            | _, _ => None 
            end
      | _ => None
      end 
  | Stmt.SSeq s1 s2 _ =>
      match (collect_hdrs_stmt ctxt s1) with
      | Some ctxt' => collect_hdrs_stmt ctxt' s2
      | None => None
      end
  | _ => Some ctxt
  end.

Definition collect_hdrs_state (ctxt:F.fs string nat) (state : Parser.state_block tags_t) : option (F.fs string nat) :=
  collect_hdrs_stmt ctxt state.(Parser.stmt).

Definition collect_hdrs_states (states : F.fs string (Parser.state_block tags_t)) : option (F.fs string nat) :=
  List.fold_left  (fun accum state =>  
    match accum, state with 
    | (Some ctxt'), (_, s1) => collect_hdrs_state ctxt' s1
    | None, (_, s2) => collect_hdrs_state [] s2
    end) states None.


    (* Collect all headers from a program *)
Fixpoint collect_hdrs (prog: P4c.TopDecl.d tags_t) : (F.fs string nat):=
  match prog with 
    | TopDecl.TPParser p _ eps params st states i => 
      match collect_hdrs_states states with
      | Some ctxt => ctxt
      | None => []
      end
    | TopDecl.TPSeq d1 d2 _ => List.app (collect_hdrs d1) (collect_hdrs d2)
    | _ => []
  end.

Definition mk_hdr_type (hdrs: F.fs string nat) : Type := Fin.t (List.length hdrs).

Definition mk_st_type (states: F.fs string (Parser.state_block tags_t)) : Type := Fin.t (List.length states).

Lemma findi_length_bound :
  forall {A: Type} pred (l: list A) i,
    findi pred l = Some i ->
    i < Datatypes.length l.
Proof.
Admitted.

Definition inject_name (hdrs: list (string * nat)) (hdr: string) : option (mk_hdr_type hdrs).
Proof.
  destruct (findi (fun kv => String.eqb hdr (fst kv)) hdrs) eqn:?.
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

Definition extract_name (hdrs: list (string * nat)) (h: mk_hdr_type hdrs) : string.
Proof.
  pose (Fin.to_nat h).
  destruct s as [i pf].
  destruct (List.nth_error hdrs i) eqn:?.
  - exact (fst p).
  - apply nth_error_None in Heqo.
    unfold F.f in pf.
    lia.
Defined.

Definition hdr_map (hdrs: list (string * nat)) (h:mk_hdr_type hdrs) : nat := 
  match F.get (extract_name hdrs h) hdrs with 
    | Some n => n 
    | None => 0   (* This shouldn't be needed *)
  end.

Definition inject_name_st (states: list (string * (Parser.state_block tags_t))) (st: string) : option (mk_st_type states).
Proof.
  destruct (findi (fun kv => String.eqb st (fst kv)) states) eqn:?.
  - apply Some.
    destruct states.
    + cbv in Heqo. 
      congruence.
    + unfold mk_hdr_type.
      apply @Fin.of_nat_lt with (p := n).
      eapply findi_length_bound.
      apply Heqo.
  - exact None.
Defined.

Definition extract_name_st (states: list (string * (Parser.state_block tags_t))) (st:mk_st_type states) : string.
Proof.
  pose (Fin.to_nat st).
  destruct s as [i pf].
  destruct (List.nth_error states i) eqn:?.
  - exact (fst p).
  - apply nth_error_None in Heqo.
    unfold F.f in pf.
    lia.
Defined.  

Fixpoint expr_size (hdrs: F.fs string nat) (e:Expr.e tags_t) : nat := 
  match e with 
  (* | Expr.EHeader fields valid i => Some (expr ) *)
  (* slice size not right *)
  | Expr.ESlice arg hi lo i => (Init.Nat.min (1 + Pos.to_nat hi) (expr_size hdrs arg) -
  Pos.to_nat lo)
  | _ => 0
  end.

Fixpoint translate_expr (hdrs: F.fs string nat) (e:Expr.e tags_t): option (expr (hdr_map hdrs) (expr_size hdrs e)) := 
  match e with 
  (* | Expr.EHeader fields valid i => Some (EHdr ) *)
  | Expr.ESlice arg hi lo i => 
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

Check OpAsgn.
Check OpExtract.
(* Need function for finding header associated with an expression *)
Fixpoint translate_st (hdrs: F.fs string nat) (s:Stmt.s tags_t): option (op (hdr_map hdrs)):= 
  match s with 
  | Stmt.SSkip i => Some (OpNil _)
  | Stmt.SVardecl x expr _ =>
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
    end
  (* | Stmt.SAssign lhs rhs _ => 
    match (translate_expr hdrs lhs), (translate_expr hdrs rhs) with 
      | Some (EHdr hdr), Some e1 => OpAsgn hdr e1
      |  
    end *)
  | Stmt.SSeq s1 s2 i => 
    match (translate_st hdrs s1), (translate_st hdrs s2) with 
    | Some st1, Some st2 => Some (OpSeq st1 st2)
    | _, _ => None
    end
    | Stmt.SExternMethodCall "packet_in" "extract" _ {|paramargs := params; rtrns := _|} _ => (* Packet extract calls *) 
    match params with 
    | (_, PAOut (Expr.EExprMember h _ _ _))::[] => (* extract only returns PAOut?*)
      match thdr_to_str h with 
      | Some hdr_name => 
        match inject_name hdrs hdr_name with 
        | Some header => Some (OpExtract (hdr_map hdrs) header)
        | None => None
        end
      | None => None
      end
    | _ => None
    end 
  (* Find header associated with lhs *)
  (* | Stmt.SAssign lhs rhs i => translate_expr hdrs  *)
  | Stmt.SBlock s => translate_st hdrs s
  | _ => None
  end.

  Print nat.
  Check Parser.PGoto.
  Print Parser.state. 
Definition state_holder (A:F.fs string nat): Type := string * (state (mk_hdr_type A) (hdr_map A)).
(* Need to make states finite as well *)
 Fixpoint translate_states (num_states: nat) (state_name:string)
 (hdrs: F.fs string nat) (states:F.fs string (Parser.state_block tags_t)) (st: Parser.state_block tags_t) : option (state (mk_hdr_type hdrs) (hdr_map hdrs)) :=
  match num_states with 
    | O => None 
    | Datatypes.S num_states =>
      match st with 
      | {|Parser.stmt:=stmt; Parser.trans:=pe|} =>   
        match translate_st hdrs stmt, translate_trans num_states hdrs pe with 
          | Some t_stmt, Some transition => Some ({| st_op := t_stmt; st_trans := transition|})
          | _, _ => None
        end
      end
    end

  with translate_trans  (num_states:nat) (hdrs: F.fs string nat) (e:Parser.e tags_t) : option (transition (mk_hdr_type hdrs) (hdr_map hdrs)) :=
    match e with 
      | Parser.PGoto st _ => 
        match (st:Parser.state) with 
        | Parser.STAccept => Some (TGoto (hdr_map hdrs) (inr true))
        | Parser.STReject => Some (TGoto (hdr_map hdrs) (inr false))
        (* What if parser loops to self? how to compile? *)
        | Parser.STStart => None
        | Parser.STName st_name => None
        end
          (* match translate_states num_states hdrs st with 
          | Some new_st =>Some (TGoto (hdr_map hdrs) new_st)
          | None => None
          end *)
      | Parser.PSelect discriminee default cases i => None
    end.
        
 (* bin/main, lib/common *)
(* header passed into parser via params (Expr.params in TPParser)  *)

(* Notes: F.fs is an association list *)
(* Does not handle subparsers, for now consider only one parser *)

(* Get all parser declarations from the program *)
Fixpoint get_parser (prog: P4c.TopDecl.d tags_t) : list(P4c.TopDecl.d tags_t) :=
match prog with 
  | TopDecl.TPParser p _ eps params st states i => [prog]
  | TopDecl.TPSeq d1 d2 _ => get_parser d1 ++ get_parser d2
  | _ => []
end.

Definition translate_parser {Hdr: Type} {H_sz: Hdr -> nat} {hdrs':F.fs string nat} (prog:P4c.TopDecl.d tags_t) : option (list (state (mk_hdr_type _) (hdr_map _))) :=
  let parsers := get_parser prog in   
  (* Assume only one parser for now *)
  let main_parser := List.hd prog parsers in 
  let hdrs := collect_hdrs main_parser in 
  match main_parser with 
    | TopDecl.TPParser p _ _ params start states i => 
    let states' := mk_st_type states in 
    let all_states := ("start", start)::states in 
    let start := translate_states (List.length all_states) "start" hdrs all_states start in
    let translate '(name, st) := (translate_states (List.length all_states) name hdrs all_states st) in
    let state_collect accum translated_state := 
      match accum, translated_state with 
      | Some acc, Some st' => Some (st'::acc)
      | _,_ => None
      end in 
    let temp := (List.map translate states) in 
    List.fold_left state_collect (List.map translate states) (Some []) 
  (* Some (List.map (fun x => let (name, st) = x in 
       (translate_states (List.length all_states) name hdrs all_states hdrs)) states) *)
    | _ => None
    end.

End P4AComp.
