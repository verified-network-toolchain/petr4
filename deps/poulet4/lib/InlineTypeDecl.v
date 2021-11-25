Require Import Poulet4.Typed Poulet4.Syntax Poulet4.Maps.
Require Poulet4.P4String.

(* TODO: inline type-declarations in p4light programs. *)
Section Inline.
  Context {tags_t : Type}.
  Notation typ := (@P4Type tags_t).
  Notation expr := (@Expression tags_t).
  Notation parameter := (@P4Parameter tags_t).

  (* TODO: how do [name]s in type names work
     with bare or qualifieds? *)
  Notation typ_decl_map := (IdentMap.t typ).

  Variable σ : typ_decl_map.

  Fixpoint inline_typs_typ (τ : typ) : typ :=
    match τ with
    | TypBool
    | TypString
    | TypInteger
    | TypInt _
    | TypBit _
    | TypVarBit _
    | TypError
    | TypMatchKind
    | TypVoid
    | TypTable _   => τ
    | TypArray τ n => TypArray (inline_typs_typ τ) n
    | TypTuple τs  => TypTuple (List.map inline_typs_typ τs)
    | TypList τs   => TypList  (List.map inline_typs_typ τs)
    | TypRecord τs => TypRecord (AList.map_values inline_typs_typ τs)
    | TypStruct τs => TypStruct (AList.map_values inline_typs_typ τs)
    | TypSet τ     => TypSet (inline_typs_typ τ)
    | TypHeader τs => TypHeader (AList.map_values inline_typs_typ τs)
    | TypHeaderUnion τs => TypHeaderUnion (AList.map_values inline_typs_typ τs)
    | TypEnum x τ mems => TypEnum x (option_map inline_typs_typ τ) mems
    | TypTypeName (BareName T| QualifiedName _ T) (* TODO: correct? *)
      => match IdentMap.get (P4String.str T) σ with
        | Some τ => τ
        | None   => τ
        end
    | TypNewType x τ => TypNewType x (inline_typs_typ τ)
    | TypControl ct => TypControl (inline_typs_controltype ct)
    | TypParser  ct => TypParser  (inline_typs_controltype ct)
    | TypExtern T
      => match IdentMap.get (P4String.str T) σ with
        | Some τ => τ
        | None   => τ
        end
    | TypFunction ft => TypFunction (inline_typs_functype ft)
    | TypAction cps ps => TypAction
                           (List.map inline_typs_param cps)
                           (List.map inline_typs_param ps)
    | TypPackage Xs ws params
      (* TODO: need to remove conflicting names. *)
      => TypPackage Xs ws (List.map inline_typs_param params)
    | TypSpecializedType τ τs
      => TypSpecializedType
          (inline_typs_typ τ)
          (List.map inline_typs_typ τs)
    | TypConstructor Xs ws ps τ
      (* TODO: need to remove conflicting names. *)
      => TypConstructor
          Xs ws (List.map inline_typs_param ps)
          (inline_typs_typ τ)
    end
  (* TODO: need to remove conflicting names. *)
  with inline_typs_controltype (ctrltype : ControlType) : ControlType :=
         match ctrltype with
         | MkControlType Xs params
           => MkControlType Xs (List.map inline_typs_param params)
         end
  (* TODO: need to remove conflicting names. *)
  with inline_typs_functype (functype : FunctionType) : FunctionType :=
         match functype with
         | MkFunctionType Xs params kind ret
           => MkFunctionType
               Xs (List.map inline_typs_param params)
               kind (inline_typs_typ ret)
         end
  with inline_typs_param (param : parameter) : parameter :=
         match param with
         | MkParameter b d τ def x
           => MkParameter b d (inline_typs_typ τ) def x
         end.
End Inline.
