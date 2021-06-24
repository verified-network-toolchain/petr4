From compcert Require Import Clight Ctypes Integers Cop.
From compcert Require AST.
Require Import Poulet4.P4cub.Syntax.AST.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.PArith.BinPos.
Require Import Poulet4.P4cub.Envn.
Require Import Poulet4.Monads.Monad.
Require Import Poulet4.Monads.Option.
(* Require Import Poulet4.Ccompiler.IdentGen. *)
Require Import List.
Require Import Coq.ZArith.BinIntDef.
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
  (*map between string and ident*)
  Definition identMap : Type := Env.t string AST.ident.
  (*currently all integers (bit strings) are represented by long*)
    (*TODO: implement integers with width larger than 64
      and optimize integers with width smaller than 32 *)
  Notation long_unsigned := (Tlong Unsigned noattr).
  Notation long_signed := (Tlong Signed noattr).
  Notation int_unsigned := (Tint I32 Unsigned noattr).
  Notation int_signed := (Tint I32 Signed noattr).
  
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
  (* TODO: figure out what cast rules does clight support and then implement this*)
  (* See https://opennetworking.org/wp-content/uploads/2020/10/P416-Language-Specification-wd.html#sec-casts *)
  
  (* input is an expression with tags_t and an idents map,
     output would be statement list , expression, needed variables/temps (in ident) and their corresponding types*)
  Fixpoint CTranslateExpr (e: E.e tags_t) (idents: identMap)
    : option ( (list Clight.statement) * Clight.expr) :=
    let prepend_stmts 
      (addon: list Clight.statement) 
      (source: option ( (list Clight.statement) * Clight.expr))
      : option ( (list Clight.statement) * Clight.expr) := 
      match source with
      | Some (src_stmts, e) => Some (addon++src_stmts, e)
      | None => None
      end
    in
    let postpend_stmts 
      (addon: list Clight.statement) 
      (source: option ( (list Clight.statement) * Clight.expr))
      : option ( (list Clight.statement) * Clight.expr) := 
      match source with
      | Some (src_stmts, e) => Some (src_stmts++addon, e)
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
    | <{Var x : ty @ i}> => (*first find if x has been declared. If not, declare it by putting it into vars*)
                        match Env.find x idents with
                        | Some id => Some ([], Evar id (CTranslateType ty))
                        | _ => None
                        end 
    | <{Slice n : τ [ hi : lo ] @ i}> => 
                        match CTranslateExpr n idents with
                        | Some (stmts, n') => prepend_stmts stmts (CTranslateSlice n' hi lo τ)
                        | _ => None
                        end
    | <{Cast e : τ @ i}> => 
                        match CTranslateExpr e idents with
                        | Some (stmts, e') => let typefrom := (CubTypeOf e) in 
                                      prepend_stmts stmts (CTranslateCast e' typefrom τ)
                        | _ => None
                        end
    | <{UOP op x : ty @ i}> => 
                        match CTranslateExpr x idents with
                        | None => None
                        | Some (stmts, x') => 
                          match op with
                          | _{!}_ => Some (stmts, Eunop Onotbool x' (CTranslateType ty))
                          | _{~}_ => Some (stmts, Eunop Onotint x' (CTranslateType ty))
                          | _{-}_ => Some (stmts, Eunop Oneg x' (CTranslateType ty))
                          | _{isValid}_ => None (*TODO: *)
                          | _{setValid}_ => None (*TODO: *)
                          | _{setInValid}_ => None (*TODO: *)
                          | _{Next}_ => None (*TODO: *)
                          | _{Size}_ => None (*TODO: *)
                          | _{Push n}_ => None (*TODO: *)
                          | _{Pop n}_ => None (*TODO: *)
                          end
                        end
    | <{BOP x : tx op y : ty @ i}> =>
                        match CTranslateExpr x idents, CTranslateExpr y idents with
                        | Some (stmts_x, x'), Some (stmts_y, y') => 
                          match op with
                          | +{+}+ =>  Some (stmts_x ++ stmts_y, Ebinop Oadd x' y' (CTranslateType tx))
                          | +{-}+ =>  Some (stmts_x ++ stmts_y, Ebinop Osub x' y' (CTranslateType tx))
                          | +{|+|}+ =>None
                          | +{|-|}+ =>None
                          | E.Times =>  Some (stmts_x ++ stmts_y, Ebinop Omul x' y' (CTranslateType tx))
                          | +{<<}+ => Some (stmts_x ++ stmts_y, Ebinop Oshl x' y' (CTranslateType tx))
                          | +{>>}+ => Some (stmts_x ++ stmts_y, Ebinop Oshr x' y' (CTranslateType tx))
                          | +{<=}+ => Some (stmts_x ++ stmts_y, Ebinop Ole x' y' type_bool)                         
                          | +{>=}+ => Some (stmts_x ++ stmts_y, Ebinop Oge x' y' type_bool)
                          | +{<}+ =>  Some (stmts_x ++ stmts_y, Ebinop Olt x' y' type_bool)
                          | +{>}+ =>  Some (stmts_x ++ stmts_y, Ebinop Ogt x' y' type_bool)
                          | +{==}+ => Some (stmts_x ++ stmts_y, Ebinop Oeq x' y' type_bool)
                          | +{!=}+ => Some (stmts_x ++ stmts_y, Ebinop One x' y' type_bool)
                          | +{&&}+
                          | +{&}+ =>  Some (stmts_x ++ stmts_y, Ebinop Oand x' y' (CTranslateType tx))
                          | +{^}+ =>  Some (stmts_x ++ stmts_y, Ebinop Oxor x' y' (CTranslateType tx))
                          | +{||}+
                          | +{|}+ =>  Some (stmts_x ++ stmts_y, Ebinop Oor x' y' (CTranslateType tx))
                          | +{++}+ => (*x ++ y = x<< widthof(y) + y*)
                                      let shift_amount := Econst_long (Integers.Int64.repr (Z.of_nat (E.width_of_typ ty))) long_unsigned in 
                                      Some (stmts_x ++ stmts_y, Ebinop Oadd (Ebinop Oshl x' shift_amount (CTranslateType tx)) y' (CTranslateType tx))
                          
                          end
                        | _, _ => None
                        end
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


