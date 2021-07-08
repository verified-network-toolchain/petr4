Set Warnings "-custom-entry-overridden".
Require Import Poulet4.P4cub.Syntax.AST
        Poulet4.P4cub.Architecture.Paquet
        Poulet4.P4cub.Envn.
Module P := P4cub.

(** P4cub's analogue to p4light's [Target.v].
    May be replace entirely with [Target.v]
    if it is parameterized by a value data-type. *)

Module Arch (Pkt : P4Packet).
  Import Pkt.

  (** p4 [extern] instance signature. *)
  Record P4Extern := {
    closure : Env.t string E;
    dispatch_method :
      string ->                                 (* method name *)
      P.arrow string (T * E) (T * LV) (T * LV) -> (* arguments *)
      Env.t string E ->                         (* current environment *)
      paquet_monad (Env.t string E)            (* input/output packet &
                                                  resulting environment. *)
      (** TODO: useful lemmas. **) }.
  (**[]*)

  Definition extern_env : Type := Env.t string P4Extern.

  (** TODO: notion of pipeline. *)
End Arch.
