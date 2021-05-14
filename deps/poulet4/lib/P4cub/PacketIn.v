(** * The P4 Core [packet_in] Extern *)

Require Poulet4.P4cub.Value.
Require Poulet4.P4cub.Paquet.
Module PKT := Poulet4.P4cub.Paquet.
Require Poulet4.P4cub.BigStep.
Require Poulet4.P4cub.SmallStep.
(* TODO: helpers need a different file from semantics. *)
Require Import Coq.ZArith.BinIntDef.
Require Import Poulet4.P4cub.Utiliser.

(** [packet_in.advance] *)
Definition advance (sizeInBits : Z) (pkt : PKT.t) : PKT.t :=
  PKT.consume_incoming (Z.to_nat sizeInBits) pkt.
(**[]*)

(** [packet_in.length] *)
Definition length : PKT.t -> Z := Z.of_nat ∘ PKT.in_length.

Section BigStepExtract.
  Import Poulet4.P4cub.Value.
  Import Poulet4.P4cub.BigStep.
  
  (** [packet_in.extract] *)
  Definition value_extract (τ : E.t) (lv : Val.lv) (ϵ : Step.epsilon)
    : PKT.paquet_monad Step.epsilon :=
    v <<| PKT.ValuePacket.read τ ;; Step.lv_update lv v ϵ.
  (**[]*)
End BigStepExtract.

Section SmallStepExtract.
  Import Poulet4.P4cub.SmallStep.

  (** TODO *)
  Definition emap {A B : Type} : (A -> B) -> Step.E.e A -> Step.E.e B.
  Admitted.
  
  Context {tags_t : Type}.
  
  (** [packet_in.extract] *)
  Definition expr_extract
             (i : tags_t) (τ : Step.E.t)
             (lv : Step.E.e tags_t) (ϵ : Step.eenv)
    : PKT.paquet_monad Step.eenv :=
    e <<| PKT.ExprPacket.read τ ;;
    Step.lv_update lv (emap (fun _ => i) e) ϵ.
End SmallStepExtract.
