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
  
  Fixpoint inline_typs_typ (σ : typ_decl_map) (τ : typ) : typ :=
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
    | TypArray τ n => TypArray (inline_typs_typ σ τ) n
    | TypTuple τs  => TypTuple (List.map (inline_typs_typ σ) τs)
    | TypList τs   => TypList  (List.map (inline_typs_typ σ) τs)
    | TypRecord τs => TypRecord (AList.map_values (inline_typs_typ σ) τs)
    | TypStruct τs => TypStruct (AList.map_values (inline_typs_typ σ) τs)
    | TypSet τ     => TypSet (inline_typs_typ σ τ)
    | TypHeader τs => TypHeader (AList.map_values (inline_typs_typ σ) τs)
    | TypHeaderUnion τs
      => TypHeaderUnion (AList.map_values (inline_typs_typ σ) τs)
    | TypEnum x τ mems
      => TypEnum x (option_map (inline_typs_typ σ) τ) mems
    | TypTypeName (BareName T| QualifiedName _ T) (* TODO: correct? *)
      => match IdentMap.get (P4String.str T) σ with
        | Some τ => τ
        | None   => τ
        end
    | TypNewType x τ => TypNewType x (inline_typs_typ σ τ)
    | TypControl ct => TypControl (inline_typs_controltype σ ct)
    | TypParser  ct => TypParser  (inline_typs_controltype σ ct)
    | TypExtern T
      => match IdentMap.get (P4String.str T) σ with
        | Some τ => τ
        | None   => τ
        end
    | TypFunction ft => TypFunction (inline_typs_functype σ ft)
    | TypAction cps ps => TypAction
                           (List.map (inline_typs_param σ) cps)
                           (List.map (inline_typs_param σ) ps)
    | TypPackage Xs ws params
      => TypPackage
          Xs ws
          (List.map
             (inline_typs_param
                (IdentMap.removes (List.map P4String.str Xs) σ))
             params)
    | TypSpecializedType τ τs
      => TypSpecializedType
          (inline_typs_typ σ τ)
          (List.map (inline_typs_typ σ) τs)
    | TypConstructor Xs ws ps τ
      => TypConstructor
          Xs ws
          (List.map
             (inline_typs_param
                (IdentMap.removes
                   (List.map P4String.str Xs) σ))
             ps)
          (inline_typs_typ
             (IdentMap.removes
                (List.map P4String.str Xs) σ) τ)
    end
  with inline_typs_controltype
         (σ : typ_decl_map) (ctrltype : ControlType) : ControlType :=
         match ctrltype with
         | MkControlType Xs params
           => MkControlType
               Xs
               (List.map
                  (inline_typs_param
                     (IdentMap.removes
                        (List.map P4String.str Xs) σ))
                  params)
         end
  with inline_typs_functype
         (σ : typ_decl_map) (functype : FunctionType) : FunctionType :=
         match functype with
         | MkFunctionType Xs params kind ret
           => MkFunctionType
               Xs (List.map
                     (inline_typs_param
                        (IdentMap.removes
                           (List.map P4String.str Xs) σ))
                     params) kind
               (inline_typs_typ
                  (IdentMap.removes (List.map P4String.str Xs) σ) ret)
         end
  with inline_typs_param
         (σ : typ_decl_map) (param : parameter) : parameter :=
         match param with
         | MkParameter b d τ def x
           => MkParameter b d (inline_typs_typ σ τ) def x
         end.
End Inline.
