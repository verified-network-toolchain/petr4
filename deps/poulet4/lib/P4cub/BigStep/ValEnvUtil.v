Set Warnings "-custom-entry-overridden".
Require Import Poulet4.P4cub.BigStep.Value.Value
        Coq.ZArith.BinInt Poulet4.P4cub.Envn.
Module V := Val.
Import V.ValueNotations V.LValueNotations Env.EnvNotations.

(** Variable to Value mappings. *)
Definition epsilon : Type := Env.t string V.v.

(** Lookup an lvalue. *)
Fixpoint lv_lookup (ϵ : epsilon) (lv : V.lv) : option V.v :=
  match lv with
  | l{ VAR x }l => Env.find x ϵ
  | l{ lv DOT x }l =>
    (* TODO: use monadic bind. *)
    match lv_lookup ϵ lv with
    | None => None
    | Some ~{ STRUCT { fs } }~
    | Some ~{ HDR { fs } VALID:=_ }~ => F.get x fs
    | Some _ => None
    end
  | l{ lv[n] }l =>
    match lv_lookup ϵ lv with
    | None => None
    | Some ~{ STACK vss:_[_] NEXT:=_ }~ =>
      match nth_error vss (Z.to_nat n) with
      | None => None
      | Some (b,vs) => Some ~{ HDR { vs } VALID:=b }~
      end
    | Some _ => None
    end
  end.
(**[]*)

(** Updating an lvalue in an environment. *)
Fixpoint lv_update (lv : V.lv) (v : V.v) (ϵ : epsilon) : epsilon :=
  match lv with
  | l{ VAR x }l    => !{ x ↦ v ;; ϵ }!
  | l{ lv DOT x }l =>
    match lv_lookup ϵ lv with
    | Some ~{ STRUCT { vs } }~ => lv_update lv (V.VStruct (F.update x v vs)) ϵ
    | Some ~{ HDR { vs } VALID:=b }~ =>
      lv_update lv (V.VHeader (F.update x v vs) b) ϵ
    | Some _ | None => ϵ
    end
  | l{ lv[n] }l =>
    match v, lv_lookup ϵ lv with
    | ~{ HDR { vs } VALID:=b }~ ,
      Some ~{ STACK vss:ts[size] NEXT:=ni }~ =>
      let vss := nth_update (Z.to_nat n) (b,vs) vss in
      lv_update lv ~{ STACK vss:ts[size] NEXT:=ni }~ ϵ
    | _, Some _ | _, None => ϵ
    end
  end.
(**[]*)

(** Create a new environment
    from a closure environment where
    values of [In] args are substituted
    into the function parameters. *)
Definition copy_in
           (argsv : V.argsv)
           (ϵcall : epsilon) : epsilon -> epsilon :=
  F.fold (fun x arg ϵ =>
            match arg with
            | P.PAIn v     => !{ x ↦ v ;; ϵ }!
            | P.PAInOut lv => match lv_lookup ϵcall lv with
                             | None   => ϵ
                             | Some v => !{ x ↦ v ;; ϵ }!
                             end
            | P.PAOut _    => ϵ
            end) argsv.
(**[]*)

(** Update call-site environment with
    out variables from function call evaluation. *)
Definition copy_out
           (argsv : V.argsv)
           (ϵf : epsilon) : epsilon -> epsilon :=
  F.fold (fun x arg ϵ =>
            match arg with
            | P.PAIn _ => ϵ
            | P.PAOut lv
            | P.PAInOut lv =>
              match Env.find x ϵf with
              | None   => ϵ
              | Some v => lv_update lv v ϵ
              end
            end) argsv.
(**[]*)
