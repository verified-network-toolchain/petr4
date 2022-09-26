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

Variable (tags_t : Type).

(* Find size of P4cub Expr.t *)
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

  (* Find size of P4Cub Expr.e *)
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
    | Expr.ESlice arg hi lo i => 
      match type_size_e ctxt arg with 
        | Some n1 => Some (Init.Nat.min (1 + Pos.to_nat hi) n1 -
        Pos.to_nat lo)
        | None => None
      end
    | Expr.EExprMember result_type mem arg i => 
      match type_size ctxt result_type with
        | Some field_size => Some field_size
        | _ => None
      end
    | _ => None
  end.

(* Get the headers from paramargs *)
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
      | (_, PAOut (Expr.EExprMember header mem _ _))::[] => (* extract only returns PAOut?*)
          match type_size ctxt header with 
            | Some sz => Some ((mem,sz)::ctxt)
            | None => None
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

(* Collect headers from a state *)
Definition collect_hdrs_state (ctxt:F.fs string nat) (state : Parser.state_block tags_t) : option (F.fs string nat) :=
  collect_hdrs_stmt ctxt state.(Parser.stmt).

(* Collect all headers from a list of states, mapping each header to its size *)
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

(* Create Fin type headers *)
Definition mk_hdr_type (hdrs: F.fs string nat) : Type := Fin.t (List.length hdrs).

(* Create Fin type states *)
Definition mk_st_type (states: F.fs string (Parser.state_block tags_t)) : Type := Fin.t (List.length states).

Lemma findi_length_bound :
  forall {A: Type} pred (l: list A) i,
    findi pred l = Some i ->
    i < Datatypes.length l.
Proof.
  unfold findi. unfold fold_lefti.
Admitted.

(* Get Fin type headers from list of headers and header name*)
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

(* Get header name from Fin header and list of headers *)
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

(* Get size of header *)
Definition hdr_map (hdrs: list (string * nat)) (h:mk_hdr_type hdrs) : nat := 
  match F.get (extract_name hdrs h) hdrs with 
    | Some n => n 
    | None => 0   (* This shouldn't be needed *)
  end.

(* Get Fin type headers from list of states and state name*)
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

(* Get state name from Fin state and list of states *)
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

(* Find the size of a P4cub state_block *)
Definition state_block_sz '({|Parser.stmt:=statements; Parser.trans:=_ |}: (Parser.state_block tags_t)) : nat := 
  match statements with 
  | Stmt.SExternMethodCall "packet_in" "extract" _ {|paramargs := params; rtrns := _|} _ => (* Packet extract calls *) 
    match params with 
    | (_, PAOut (Expr.EExprMember h _ _ _))::[] => (* extract only returns PAOut?*)
      match type_size [] h with 
      | Some n => n
      | None => 0
      end
    | _ => 0
    end 
  | _ => 0
  end.

(* Maps a P4cub state to its size using state_block_sz. (Might not need this definition) *)
Definition st_map (states: list (string * (Parser.state_block tags_t))) (st:mk_st_type states) : nat := 
  match F.get (extract_name_st states st) states with 
  | Some st => state_block_sz st
  | None => 0
  end.

  Check List.fold_left.
(* Return size of an expression. Duplicate of type_size_e without returning the option *)
Fixpoint expr_size (hdrs: F.fs string nat) (e:Expr.e tags_t) : nat := 
  match e with 
    | Expr.EBool b i => 1
    | Expr.EBit w val i => N.to_nat w
    | Expr.EInt w val i => Pos.to_nat w
    | Expr.EVar t x i => 
      match type_size hdrs t with 
      | Some size => size
      | None => 0
      end
    | Expr.EHeader fields valid i => 
      List.fold_left (fun accum f => 
        match f with 
          | (_, t2) => accum + (expr_size hdrs t2)
        end) fields 0
    | Expr.ESlice arg hi lo i => (Init.Nat.min (1 + Pos.to_nat hi) (expr_size hdrs arg) -
    Pos.to_nat lo)
    | Expr.EExprMember result_type mem arg i => 
      match type_size hdrs result_type with
        | Some field_size => field_size
        | None => 0
      end
    | _ => 0
    end.
  (* | Expr.EHeader fields valid i => Some (expr ) *)
  (* slice size not right *)
  (* | Expr.ESlice arg hi lo i => (Init.Nat.min (1 + Pos.to_nat hi) (expr_size hdrs arg) -
  Pos.to_nat lo)
  | _ => 0
  end. *)

(* Translate P4cub expression to P4a *)
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
      | (_, PAOut (Expr.EExprMember _ h _ _))::[] => (* extract only returns PAOut?*)
        match inject_name hdrs h with 
          | Some header => Some (OpExtract (hdr_map hdrs) header)
          | None => None
        end
      | _ => None
      end 
  (* Find header associated with lhs *)
  (* | Stmt.SAssign lhs rhs i => translate_expr hdrs  *)
  | Stmt.SBlock s => translate_st hdrs s
  | _ => None
  end.
Print P4a.state_ref.
Check inl true.
Check state_ref (mk_st_type _).
Check TGoto (hdr_map _) (inl true).

(* Translate transition statements *)
Definition translate_trans (hdrs: F.fs string nat) (states:F.fs string (Parser.state_block tags_t)) 
(e:Parser.e tags_t) : option (transition (mk_st_type states) (hdr_map hdrs)) :=
  match e with 
    | Parser.PGoto st _ => 
      match (st:Parser.state) with 
      | Parser.STAccept => Some (TGoto (hdr_map hdrs) (inr true))
      | Parser.STReject => Some (TGoto (hdr_map hdrs) (inr false))
      | Parser.STStart => 
        match inject_name_st states "start" with
        | Some start_st => Some (TGoto (hdr_map hdrs) (inl start_st))
        | None => None 
        end
      | Parser.STName st_name => 
        match inject_name_st states st_name with
        | Some start_st => Some (TGoto (hdr_map hdrs) (inl start_st))
        | None => None 
        end
      end
    | Parser.PSelect discriminee default cases i => None
  end.

(* Need to make states finite as well *)
Definition translate_state (state_name:string)
(hdrs: F.fs string nat) (states:F.fs string (Parser.state_block tags_t)) (st: Parser.state_block tags_t) : option (state (mk_st_type states) (hdr_map hdrs)) :=
match st with 
| {|Parser.stmt:=stmt; Parser.trans:=pe|} =>   
  match translate_st hdrs stmt, translate_trans hdrs states pe with 
    | Some t_stmt, Some transition => Some ({| st_op := t_stmt; st_trans := transition|})
    | _, _ => None
  end
end.

(* Get all parser declarations from the program *)
Fixpoint get_parser (prog: P4c.TopDecl.d tags_t) : list(P4c.TopDecl.d tags_t) :=
match prog with 
  | TopDecl.TPParser p _ eps params st states i => [prog]
  | TopDecl.TPSeq d1 d2 _ => get_parser d1 ++ get_parser d2
  | _ => []
end.

(* Assume one parser only *)
Fixpoint find_main_parser (prog: P4c.TopDecl.d tags_t) : option (P4c.TopDecl.d tags_t) := 
  match prog with 
  | TopDecl.TPParser p _ _ params start states i => Some prog
  | TopDecl.TPSeq d1 d2 _ => 
    match find_main_parser d1 with 
    | Some p => Some p 
    | None => 
      match find_main_parser d2 with 
      | Some p => Some p 
      | None => None
      end
    end
  | _ => None
  end.

Definition find_states (prog:P4c.TopDecl.d tags_t) : list (string * P4c.Parser.state_block tags_t) :=
  match find_main_parser prog with 
  | Some (TopDecl.TPParser p _ _ params start states i) => states
  | _ => []
  end.

Definition find_hdrs (prog:P4c.TopDecl.d tags_t) : F.fs string nat :=
  match find_main_parser prog with 
  | Some (parser) => collect_hdrs parser
  | _ => []
  end.


Definition translate_parser (prog:P4c.TopDecl.d tags_t) : option (list (state (mk_st_type (find_states prog)) (hdr_map (find_hdrs prog)))) :=
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
    end. 
End P4AComp.

(* TODO: 

Look at 2nd arg of 4th arg of TParser
get TStruct => collect header + name => map to nat

Expr.param -> 
petr4 typecheck -exportp4 _.p4 
poulet4 compile

header field accesses => ESlice

convert Z => list of bools for cases selection
Z_to_binary
*)
