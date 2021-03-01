Require Import Syntax.
Require Import BabyIP.
Require Import SimpleIPv4Monadic.
Require Import P4defs.
Require Import Step.
Require Import P4String.

Require Import Environment.
Require Import Petr4.Monads.Monad.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope nat_scope.
Open Scope monad_scope.



Compute foo.

Definition eval_parser' pkt parser :=
  match parser with
  | DeclParser _ _ _ params constructor_params locals states =>
    let env := {|
          env_fresh := 0;
          env_stack := MStr.empty loc :: nil;
          env_heap := MNat.empty (@Value Info);
        |} in
    let scope := MkEnv_EvalEnv nil nil (MkP4String "dummy") in
    let parser := ValObjParser scope params constructor_params locals states in
    let packet := ValObj (ValObjPacket pkt) in
    let stepper := step_trans _ NoInfo parser 2 (MkP4String "start") in
    Some ((env_insert Info "packet" packet ;;
           env_insert Info "hdr" (ValBase (ValBaseHeader ((MkP4String "ip", ValBaseHeader ((MkP4String "src", ValBaseBit 8 0) :: (MkP4String "dst", ValBaseBit 8 0) :: (MkP4String "proto", ValBaseBit 4 0) :: nil) false) :: (MkP4String "t_or_u", ValBaseUnion ((MkP4String "udp", ValBaseHeader ((MkP4String "sport", ValBaseBit 8 0) :: (MkP4String "dport", ValBaseBit 8 0) :: (MkP4String "flags", ValBaseBit 4 0) :: nil) false) :: (MkP4String "tcp", ValBaseHeader ((MkP4String "sport", ValBaseBit 8 0) :: (MkP4String "dport", ValBaseBit 8 0) :: (MkP4String "flags", ValBaseBit 4 0) :: (MkP4String "seq", ValBaseBit 8 0) :: nil) false) :: nil)) :: nil) false)) ;; stepper) env)
  | _ => None
  end
.

Definition eval_parser pkt parser : option (Value * list bool) :=
  match eval_parser' pkt parser with
  | Some (inl _, env) =>
    let get_pkt_and_hdr := 
        let* pkt_val := env_str_lookup Info (MkP4String "packet") in
        let* hdr_val := env_str_lookup Info (MkP4String "hdr") in
        mret (hdr_val, pkt_val)
    in
    match get_pkt_and_hdr env  with
    | (inl (hdr, (ValObj (ValObjPacket pkt))), env) =>
      Some (hdr, pkt)
    | _ => None
    end
  | Some (inr _, _)
  | None => None
  end.

Inductive header_repr: @Value Info -> Headers -> Prop :=
.

Theorem parser_grammar_sound :
  forall p p' hdr hdr_rec parser_state,
    eval_parser p MyParser = Some (hdr, p') ->
    State.run_with_state (init_state p) Headers_p = (inl hdr_rec, parser_state) ->
    header_repr hdr hdr_rec /\
    p' = parser_state.(pkt).
Proof.
  intros.
Admitted.
