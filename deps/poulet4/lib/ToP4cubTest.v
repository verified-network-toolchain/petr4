
Require Import Poulet4.P4defs.
Require Import Poulet4.Syntax.
Require Import Poulet4.SimpleNat.
Require Import Poulet4.P4cub.Util.Result.
Require Import Poulet4.ToP4cub.

Import Result SimpleNat Syntax List ListNotations.

Definition test := Syntax.Program [decl'1
                      ; packet_in
                      ; packet_out
                      ; verify'check'toSignal
                      ; NoAction
                      ; decl'2
                      ; decl'3
                      ; standard_metadata_t
                      ; CounterType
                      ; MeterType
                      ; counter
                      ; direct_counter
                      ; meter
                      ; direct_meter
                      ; register
                      ; action_profile
                      ; random'result'lo'hi
                      ; digest'receiver'data
                      ; HashAlgorithm
                      ; mark_to_drop
                      ; mark_to_drop'standard_metadata
                      ; hash'result'algo'base'data'max
                      ; action_selector
                      ; CloneType
                      ; Checksum16
                      ; verify_checksum'condition'data'checksum'algo
                      ; update_checksum'condition'data'checksum'algo
                      ; verify_checksum_with_payload'condition'data'checksum'algo
                      ; update_checksum_with_payload'condition'data'checksum'algo
                      ; resubmit'data
                      ; recirculate'data
                      ; clone'type'session
                      ; clone3'type'session'data
                      ; truncate'length
                      ; assert'check
                      ; assume'check
                      (* ; log_msg'msg *)
                      (* ; log_msg'msg'data *)
                      ; Parser
                      ; VerifyChecksum
                      ; Ingress
                      ; Egress
                      ; ComputeChecksum
                      ; Deparser
                      ; V1Switch
                      ; intrinsic_metadata_t
                      ; meta_t
                      ; cpu_header_t
                      ; ethernet_t
                      ; ipv4_t
                      ; tcp_t
                      ; metadata
                      ; headers
                      ; ParserImpl
                      ; egress
                      ; ingress
                      ; DeparserImpl
                      ; verifyChecksum
                      ; computeChecksum
                      ; main
                     ].
(* Compute test. *)

(* compute (translate_program Info NoInfo test). *)
Lemma simplenat_no_error: Result.is_ok (translate_program Info NoInfo test).
Proof.
  compute.
  trivial.
Qed.
