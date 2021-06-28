From compcert Require Import Clight Ctypes Integers Cop.
From compcert Require AST.
Require Import Poulet4.P4cub.Syntax.AST.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.PArith.BinPos.
Require Import Poulet4.P4cub.Envn.
Require Import Poulet4.Monads.Monad.
Require Import Poulet4.Monads.Option.
Require Import Poulet4.Ccompiler.CCompEnv.
Require Import List.
Require Import Coq.ZArith.BinIntDef.
Module P := P4cub.
Module F := P.F.
Module E := P.Expr.
Module ST := P.Stmt.
Parameter print_Clight: Clight.program -> unit.
(** P4Cub -> Clight **)
Section CComp.
  
  Context (tags_t: Type).
  Notation tpdecl := (P4cub.TopDecl.d tags_t).
  (*map between string and ident*)
  Definition identMap : Type := Env.t string AST.ident.
    (*TODO: implement integers with width larger than 64
      and optimize integers with width smaller than 32 *)
  Notation long_unsigned := (Tlong Unsigned noattr).
  Notation long_signed := (Tlong Signed noattr).
  Notation int_unsigned := (Tint I32 Unsigned noattr).
  Notation int_signed := (Tint I32 Signed noattr).


  (*helper functions that are not translations*)
  (* Definition prepend_stmts 
      (addon: list Clight.statement) 
      (source: option ( (list Clight.statement) * Clight.expr * ClightEnv))
      : option ( (list Clight.statement) * Clight.expr * ClightEnv) := 
      match source with
      | Some (src_stmts, e, env) => Some (addon++src_stmts, e, env)
      | None => None
      end
    .
  Definition postpend_stmts 
      (addon: list Clight.statement) 
      (source: option ( (list Clight.statement) * Clight.expr * ClightEnv))
      : option ( (list Clight.statement) * Clight.expr * ClightEnv) := 
      match source with
      | Some (src_stmts, e, env) => Some (src_stmts++addon, e, env)
      | None => None
      end
    . *)
  
  Definition CTranslateType (p4t : E.t) : Ctypes.type.
    Admitted.
  Definition CubTypeOf (e : E.e tags_t) : E.t.
    Admitted.
  
  Definition CTranslateSlice (x: Clight.expr) (hi lo: positive) (type: E.t) (env: ClightEnv)
  : option (Clight.expr * ClightEnv) := 
    (* x[hi : lo] = [x >> lo] & (1<<(hi-lo+1) - 1)*)
    let hi' := Econst_int (Integers.Int.repr (Zpos hi)) (int_unsigned) in
    let lo' := Econst_int (Integers.Int.repr (Zpos lo)) (int_unsigned) in
    let one' := Econst_long (Integers.Int64.one) (long_unsigned) in
    Some (Ebinop Oand (Ebinop Oshr x lo' long_unsigned) 
          (Ebinop Osub (Ebinop Oshl one' (Ebinop Oadd one' 
          (Ebinop Osub hi' lo' long_unsigned) long_unsigned) long_unsigned) 
            (one') long_unsigned) long_unsigned, env).
  Definition CTranslateCast (e: Clight.expr) (typefrom typeto: E.t) (env: ClightEnv) 
  : option (Clight.expr * ClightEnv).
    Admitted.
  (* TODO: figure out what cast rules does clight support and then implement this*)
  (* See https://opennetworking.org/wp-content/uploads/2020/10/P416-Language-Specification-wd.html#sec-casts *)
  

  Import P4cub.P4cubNotations.
  (* input is an expression with tags_t and an idents map,
     output would be statement list , expression, needed variables/temps (in ident) and their corresponding types*)
  Fixpoint CTranslateExpr (e: E.e tags_t) (env: ClightEnv)
    : option (Clight.expr * ClightEnv) :=
    
    match e with
    | <{TRUE @ i}> =>   Some (Econst_int (Integers.Int.one) (type_bool), env)
    | <{FALSE @ i}> =>  Some (Econst_int (Integers.Int.zero) (type_bool), env)
    (*currently all integers (bit strings) are represented by long*)
    | <{w W n @ i}> =>  if (Pos.leb w (Pos.of_nat 64))
                        then Some (Econst_long (Integers.Int64.repr n) (long_unsigned), env)
                        else None 
    | <{w S n @ i}> =>  if (Pos.leb w (Pos.of_nat 64))
                        then Some(Econst_long (Integers.Int64.repr n) (long_signed), env)
                        else None
    | <{Var x : ty @ i}> => (*first find if x has been declared. If not, declare it by putting it into vars*)
                        let cty := CTranslateType ty in
                        match find_ident env x with
                        | Some id => Some (Evar id cty, env)
                        | None => let env' := add_var env x cty in
                                  match find_ident env' x with
                                  | Some id' => Some (Evar id' cty, env')
                                  | None => None
                                  end
                        end 
    | <{Slice n : τ [ hi : lo ] @ i}> => 
                        match CTranslateExpr n env with
                        | Some (n', env') => (CTranslateSlice n' hi lo τ env')
                        | _ => None
                        end
    | <{Cast e : τ @ i}> => 
                        match CTranslateExpr e env with
                        | Some (e', env') => let typefrom := (CubTypeOf e) in 
                                      (CTranslateCast e' typefrom τ env')
                        | _ => None
                        end
    | <{UOP op x : ty @ i}> => 
                        match CTranslateExpr x env with
                        | None => None
                        | Some (x', env') => 
                          match op with
                          | _{!}_ => Some (Eunop Onotbool x' (CTranslateType ty), env')
                          | _{~}_ => Some (Eunop Onotint x' (CTranslateType ty), env')
                          | _{-}_ => Some (Eunop Oneg x' (CTranslateType ty), env')
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
                        match CTranslateExpr x env with
                        | None => None
                        | Some (x', env') =>  
                          match CTranslateExpr y env' with
                          | None => None
                          | Some (y', env'') => 
                            match op with
                            | +{+}+ =>  Some (Ebinop Oadd x' y' (CTranslateType tx), env'')
                            | +{-}+ =>  Some (Ebinop Osub x' y' (CTranslateType tx), env'')
                            | +{|+|}+ =>None
                            | +{|-|}+ =>None
                            | E.Times =>  Some (Ebinop Omul x' y' (CTranslateType tx), env'')
                            | +{<<}+ => Some (Ebinop Oshl x' y' (CTranslateType tx), env'')
                            | +{>>}+ => Some (Ebinop Oshr x' y' (CTranslateType tx), env'')
                            | +{<=}+ => Some (Ebinop Ole x' y' type_bool, env'')                         
                            | +{>=}+ => Some (Ebinop Oge x' y' type_bool, env'')
                            | +{<}+ =>  Some (Ebinop Olt x' y' type_bool, env'')
                            | +{>}+ =>  Some (Ebinop Ogt x' y' type_bool, env'')
                            | +{==}+ => Some (Ebinop Oeq x' y' type_bool, env'')
                            | +{!=}+ => Some (Ebinop One x' y' type_bool, env'')
                            | +{&&}+
                            | +{&}+ =>  Some (Ebinop Oand x' y' (CTranslateType tx), env'')
                            | +{^}+ =>  Some (Ebinop Oxor x' y' (CTranslateType tx), env'')
                            | +{||}+
                            | +{|}+ =>  Some (Ebinop Oor x' y' (CTranslateType tx), env'')
                            | +{++}+ => (*x ++ y = x<< widthof(y) + y*)
                                        let shift_amount := Econst_long (Integers.Int64.repr (Z.of_nat (E.width_of_typ ty))) long_unsigned in 
                                        Some (Ebinop Oadd (Ebinop Oshl x' shift_amount (CTranslateType tx)) y' (CTranslateType tx), env'')
                            end
                          end
                        end
    | <{tup es @ i}> => None (*first create a temp of this tuple. then assign all the values to it. then return this temp *) 
    | <{rec { fields } @ i}> => None (*first create a temp of this record. then assign all the values to it. then return this temp *)
                        
    | <{hdr { fields } valid := b @ i}> => None (*first create a temp of this header. then assign all the values to it. then return this temp*)
    | <{Mem x : ty dot y @ i}> => 
                        match CTranslateExpr x env with
                        | None => None
                        | Some (x', env') =>
                          match ty with
                          | E.TRecord(f)
                          | E.THeader(f) => 
                            match F.get_index y f with
                            | Some n => Some ((Clight.Efield x' (Pos.of_nat n) (CTranslateType ty)), env')
                            | None => None
                            end
                          | _ => None
                          end
                        end

    (* | Error x @ i => *)
    (* | Matchkind mk @ i => *)
    (* | Stack hdrs : ts [ n ] nextIndex := ni @ i => *)
    (* | Access e1 [ e2 ] @ i =>  *)
    | _ =>  None
    end.

  Definition CTranslateExprList (el : list (E.e tags_t)) (env: ClightEnv): option ((list Clight.expr) * ClightEnv) :=
    let Cumulator: Type := option ((list Clight.expr * ClightEnv)) in 
    let transformation (A: Cumulator) (B: E.e tags_t) : Cumulator := 
      match A with
      |None => None
      |Some (el', env') => 
      match CTranslateExpr B env' with
      |None => None
      |Some (B', env'') => Some(el' ++ [B'], env'')
      end end in
    List.fold_left  (transformation) el (Some ([],env)).
  Fixpoint CTranslateStatement (s: ST.s tags_t) (env: ClightEnv) : option (Clight.statement * ClightEnv) :=
    match s with
    | -{skip @ i}- => Some (Sskip, env)
    | -{s1;s2 @ i}- => match CTranslateStatement s1 env with
                       |None => None
                       |Some(s1', env1) => 
                       match CTranslateStatement s2 env1 with
                       |None => None
                       |Some(s2', env2) =>
                       Some (Ssequence s1' s2', env2)
                       end end
    | -{b{s}b}- => CTranslateStatement s env
    | -{var x : t @ i}- => Some (Sskip, CCompEnv.add_var env x (CTranslateType t))
    | -{asgn e1 := e2 : t @ i}- => match CTranslateExpr e1 env with
                                   |None => None
                                   |Some(e1', env1) => 
                                   match CTranslateExpr e2 env1 with
                                   |None => None
                                   |Some(e2', env2) =>
                                   Some (Sassign e1' e2', env2)
                                   end end
    | -{if e : t then s1 else s2 @ i}- => match CTranslateExpr e env with
                                          |None => None
                                          |Some(e', env1) =>
                                          match CTranslateStatement s1 env1 with
                                          |None => None
                                          |Some(s1', env2) =>
                                          match CTranslateStatement s2 env2 with
                                          |None => None
                                          |Some(s2', env3) =>
                                          Some(Sifthenelse e' s1' s2', env3)
                                          end end end
    | -{call f with args @ i}- => match CCompEnv.lookup_function env f with
                                  |None => None
                                  |Some(f', id) =>
                                    let args' : list (E.e tags_t) := 
                                      let map_f (f:string * (P.paramarg (E.t*(E.e tags_t)) (E.t*(E.e tags_t)))) : (E.e tags_t):=
                                      match f with
                                      | (_, P.PAIn (t,e))
                                      | (_, P.PAOut (t,e))
                                      | (_, P.PAInOut (t,e)) => e
                                      end in
                                      List.map (map_f) args in
                                    match CTranslateExprList args' env with
                                    | None => None
                                    | Some (elist, env') => 
                                    Some(Scall None (Evar id (Clight.type_of_function f')) elist, env')
                                    end 
                                  end 
    (* | -{let e : t := call f with args @ i}- *)
    (* | -{funcall f with args into o @ i}- *)
    (* | -{calling a with args @ i}- *)
    (* | -{extern e calls f with args gives x @ i}- *)
    | -{return e : t @ i}- => match CTranslateExpr e env with
                              | None => None
                              | Some (e', env') => Some ((Sreturn (Some e')), env')
                              end
    | -{returns @ i}- => Some (Sreturn None, env)
    (* | -{exit @ i}- *)
    (* | -{apply x with args @ i}- *)
    (* | -{invoke tbl @ i}- => None *)
    | _ => None
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


