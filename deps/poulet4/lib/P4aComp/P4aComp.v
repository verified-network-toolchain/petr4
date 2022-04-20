From Leapfrog Require Import Syntax Ntuple.
From Poulet4.P4cub.Syntax Require Import Syntax P4Field.
From Poulet4.Utils Require Import FinType P4Arith.
Require Import Coq.ZArith.ZArith
        Coq.micromega.Lia
        Coq.Bool.Bool.
Import String.
Module P4c := AST.
Module P4a := Syntax.
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

Fixpoint collect_hdrs_stmt (ctxt:F.fs string nat) (st: P4c.Stmt.s tags_t) : option (F.fs string nat) :=
  match st with 
  | Stmt.SVardecl x expr _ => 
      match expr with 
      | inl typ =>
          match type_size ctxt typ with
          | Some sz => Some [(x, sz)]
          | None => None
          end
      | inr e => 
          match type_size_e ctxt e with
          | Some sz => Some [(x, sz)]
          | None => None
          end
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
    | TopDecl.TPSeq d1 d2 _ => collect_hdrs d1 ++ collect_hdrs d2
    | _ => []
  end.

Definition mk_hdr_type (hdrs: F.fs string nat) : Type := Fin.t (List.length hdrs).


Lemma findi_length_bound :
  forall {A: Type} pred (l: list A) i,
    findi pred l = Some i ->
    i < Datatypes.length l.
Proof.
  induction l.
  - cbn.
    congruence.
  - intros.
    unfold findi, fold_lefti in H0.
    cbn in H0.
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
    try lia. Admitted.

Locate F.fs.
Check F.get.

Definition hdr_map (hdrs: list (string * nat)) (h:mk_hdr_type hdrs) : nat := 
  match F.get (extract_name hdrs h) hdrs with 
    | Some n => n 
    | None => 0   (* This shouldn't be needed *)
  end.

Print expr.

Fixpoint expr_size (hdrs: F.fs string nat) (e:Expr.e tags_t) : nat := 
  match e with 
  (* | Expr.EHeader fields valid i => Some (expr ) *)
  (* slice size not right *)
  | Expr.ESlice arg hi lo i => (Init.Nat.min (1 + Pos.to_nat hi) (expr_size hdrs arg) -
  Pos.to_nat lo)
  | _ => 0
  end.

Print ESlice.

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
Print OpAsgn.
Print hdr_map.

Definition coerce_size {Hdr: Type} {H_sz: Hdr -> nat} {sz: nat} (e: Syntax.expr H_sz sz) (sz': nat) : option (Syntax.expr H_sz sz').
Proof.
  destruct (Nat.eq_dec sz sz').
  - rewrite <- e0. apply Some. apply e.
  - apply None.
Defined. 
Print hdr_map.
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
  | Stmt.SSeq s1 s2 i => OpSeq (translate_st hdrs s1) (translate_st hdrs s2)
  (* Find header associated with lhs *)
  (* | Stmt.SAssign lhs rhs i => translate_expr hdrs  *)
  | Stmt.SBlock s => translate_st hdrs s
  | _ => OpNil _
  end.
(* header passed into parser via params (Expr.params in TPParser)  *)
Print Parser.

(* Notes: F.fs is an association list *)
(* Does not handle subparsers, for now consider only one parser *)

(* Inductive mk_hdr_type (parser: P4cubparser) : Type :=
| Hdr: forall id sz, List.In (id, sz) (collect_headers parser) -> mk_hdr_type parser.
Definition mk_hdr_sz (parser: P4cubparser) : mk_hdr_type parser -> nat.
Admitted. *)


(* Fixpoint translate_trans (e:Parser.e) : transition
  match e with 
    | PGoto st i => TGoto (translate_state st)
    | PSelet discriminee default cases i =?>
  end. *)

Fixpoint get_parser (prog: P4c.TopDecl.d tags_t) : list (Parser.state_block tags_t) :=
  match prog with 
    | TopDecl.TPParser p _ eps params st states i => [st] ++ []
    | TopDecl.TPSeq d1 d2 _ => get_parser d1 ++ get_parser d2
    | _ => []
  end.

End P4AComp.


(* Inductive mk_hdr_type (parser: P4cubparser) : Type :=
| Hdr: forall id sz, List.In (id, sz) (collect_headers parser) -> mk_hdr_type parser.
Definition mk_hdr_sz (parser: P4cubparser) : mk_hdr_type parser -> nat.
Admitted.
Definition mk_st (parser: P4cubparser) : Type.
Admitted.

Definition mk_states (parser: P4cubparser): mk_st parser -> state (mk_st parser) (mk_hdr_sz parser).
Admitted. *)
