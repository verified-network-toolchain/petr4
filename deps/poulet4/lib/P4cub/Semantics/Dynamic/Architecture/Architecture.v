Set Warnings "-custom-entry-overridden".
From Poulet4.P4cub Require Import
     Syntax.AST Semantics.Climate Semantics.Dynamic.Architecture.Paquet.
        
Import String.

(** P4cub's analogue to p4light's [Target.v].
    May be replace entirely with [Target.v]
    if it is parameterized by a value data-type. *)

Module Arch (Pkt : P4Packet).
  Import Pkt.

  (** p4 [extern] instance signature. *)
  Record P4Extern := {
    closure : Clmt.t string E;
    dispatch_method :
      string ->                                 (* method name *)
      arrow string E LV LV -> (* arguments *)
      Clmt.t string E ->                         (* current environment *)
      paquet_monad (Clmt.t string E)            (* input/output packet &
                                                  resulting environment. *)
      (** TODO: useful lemmas. **) }.
  (**[]*)

  Definition extern_env : Type := Clmt.t string P4Extern.

  (** TODO: notion of pipeline. *)
End Arch.
