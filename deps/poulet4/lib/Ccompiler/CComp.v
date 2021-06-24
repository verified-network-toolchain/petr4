From compcert Require Import Clight Ctypes Integers Cop.
Require Import Poulet4.P4cub.Syntax.AST.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.PArith.BinPos.
Require Import Poulet4.P4cub.Envn.
Require Import Poulet4.Monads.Monad.
Require Import Poulet4.Monads.Option.
Require Import List.
Module P := P4cub.
Module F := P.F.
Module E := P.Expr.
Module ST := P.Stmt.
Parameter print_Clight: Clight.program -> unit.
(** P4Cub -> Clight **)

Section CComp.

  Import P4cub.P4cubNotations.
  Context (tags_t: Type).
  Notation tpdecl := (P4cub.TopDecl.d tags_t).
  (*currently all integers (bit strings) are represented by long*)
    (*TODO: implement integers with width larger than 64
      and optimize integers with width smaller than 32 *)
  Notation long_unsigned := (Tlong Unsigned noattr).
  Notation long_signed := (Tlong Signed noattr).
  Notation int_unsigned := (Tint I32 Unsigned noattr).
  Notation int_signed := (Tint I32 Signed noattr).
  Definition identMap : Type := Env.t string AST.ident.
  Definition CTranslateType (p4t : E.t) : Ctypes.type.
    Admitted.
  Definition CubTypeOf (e : E.e tags_t) : E.t.
    Admitted.
  Definition CTranslateSlice (x: Clight.expr) (hi lo: positive) (type: E.t) : option ( (list Clight.statement) * Clight.expr) := 
    (* x[hi : lo] = [x >> lo] & (1<<(hi-lo+1) - 1)*)
    let hi' := Econst_int (Integers.Int.repr (Zpos hi)) (int_unsigned) in
    let lo' := Econst_int (Integers.Int.repr (Zpos lo)) (int_unsigned) in
    let one' := Econst_long (Integers.Int64.one) (long_unsigned) in
    Some ([], Ebinop Oand (Ebinop Oshr x lo' long_unsigned) 
          (Ebinop Osub (Ebinop Oshl one' (Ebinop Oadd one' 
          (Ebinop Osub hi' lo' long_unsigned) long_unsigned) long_unsigned) 
            (one') long_unsigned) long_unsigned).
  Definition CTranslateCast (e: Clight.expr) (typefrom typeto: E.t) : option ( (list Clight.statement) * Clight.expr).
  Admitted.

  Definition CTranslateUop (op: E.uop) (x) :  option ( (list Clight.statement) * Clight.expr).
  Admitted.

  Definition CTranslateBop (op: E.bop) : Cop.binary_operation.
  Admitted. 
  (* TODO: figure out what cast rules does clight support and then implement this*)
  (* See https://opennetworking.org/wp-content/uploads/2020/10/P416-Language-Specification-wd.html#sec-casts *)
  Fixpoint CTranslateExpr (e: E.e tags_t) (idents: identMap): option ( (list Clight.statement) * Clight.expr) :=
    let prepend (addon: list Clight.statement) (source: option ( (list Clight.statement) * Clight.expr)): option ( (list Clight.statement) * Clight.expr) := 
      match source with
      | Some (src_list, e) => Some (addon++src_list, e)
      | None => None
      end
    in
    let postpend (addon: list Clight.statement) (source: option ( (list Clight.statement) * Clight.expr)): option ( (list Clight.statement) * Clight.expr) := 
      match source with
      | Some (src_list, e) => Some (src_list++addon, e)
      | None => None
      end
    in
    match e with
    | <{TRUE @ i}> =>   Some ([], Econst_int (Integers.Int.one) (type_bool))
    | <{FALSE @ i}> =>  Some ([], Econst_int (Integers.Int.zero) (type_bool))
    
    | <{w W n @ i}> =>  if (Pos.leb w (Pos.of_nat 64))
                        then Some ([], Econst_long (Integers.Int64.repr n) (long_unsigned))
                        else None 
    | <{w S n @ i}> =>  if (Pos.leb w (Pos.of_nat 64))
                        then Some([], Econst_long (Integers.Int64.repr n) (long_signed))
                        else None
    | <{Var x : ty @ i}> => (*assuming p4cub separates initialization and declaration*)
                        match Env.find x idents with
                        | Some id => Some ([], Evar id (CTranslateType ty))
                        | _ => None
                        end 
    | <{Slice n : τ [ hi : lo ] @ i}> => 
                        match CTranslateExpr n idents with
                        | Some (stmts, n') => prepend stmts (CTranslateSlice n' hi lo τ)
                        | _ => None
                        end
    | <{Cast e : τ @ i}> => 
                        match CTranslateExpr e idents with
                        | Some e' => let typefrom := (CubTypeOf e) in 
                                      CTranslateCast (snd e') typefrom τ
                        | _ => None
                        end
    | <{UOP op x : ty @ i}> => 
    (* | BOP x : tx op y : ty @ i => *)
    (* | tup es @ i => *)
    (* | rec { fields } @ i =>  *)
    (* | hdr { fields } valid := b @ i => *)
    (* | Mem x : ty dot y @ i =>  *)
    (* | Error x @ i => *)
    (* | Matchkind mk @ i => *)
    (* | Stack hdrs : ts [ n ] nextIndex := ni @ i => *)
    (* | Access e1 [ e2 ] @ i =>  *)
    | _ =>  None
    end.
    

  
  (* currently just an empty program *)
  Definition Compile (prog: tpdecl) : Errors.res (Clight.program) := 
    let main_decl : AST.globdef (fundef function) type :=
      AST.Gfun (Ctypes.Internal (Clight.mkfunction 
        Ctypes.Tvoid 
        (AST.mkcallconv None true true)
        []
        []
        []
        Sskip
      ))
    in
    let res_prog : Errors.res (program function) := make_program 
      [] [(xH, main_decl)] [] xH
    in
    res_prog.

  Definition Compile_print (prog: tpdecl): unit := 
    match Compile prog with
    | Errors.Error e => tt
    | Errors.OK prog => print_Clight prog
    end.
  
End CComp.


