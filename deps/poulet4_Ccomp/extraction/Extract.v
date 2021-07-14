
(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)
From compcert Require Coqlib.
From compcert Require Wfsimpl.
From compcert Require Decidableplus.
Require DecidableClass.
From compcert Require AST.
From compcert Require Iteration.
From compcert Require Floats.
From compcert Require SelectLong.
From compcert Require Selection.
From compcert Require RTLgen.
From compcert Require Inlining.
From compcert Require ValueDomain.
From compcert Require Tailcall.
From compcert Require Allocation.
From compcert Require Bounds.
From compcert Require Ctypes.
From compcert Require Csyntax.
From compcert Require Ctyping.
From compcert Require Clight.
From compcert Require Compiler.
From compcert Require Parser.
From compcert Require Initializers.
Require Coq.extraction.Extraction.
Require Import ExtrOcamlBasic.
Require BinPosDef.
Require Import ExtrOcamlString.
Require Poulet4.SimplExpr.
Require Poulet4.GenLoc.
Require Poulet4_Ccomp.CComp.

Extract Inlined Constant Coqlib.proj_sumbool => "(fun x -> x)".

Extract Inlined Constant Datatypes.fst => "fst".
Extract Inlined Constant Datatypes.snd => "snd".

(* Decidable *)

Extraction Inline DecidableClass.Decidable_witness DecidableClass.decide
   Decidableplus.Decidable_and Decidableplus.Decidable_or
   Decidableplus.Decidable_not Decidableplus.Decidable_implies.

   (* Wfsimpl *)
Extraction Inline Wfsimpl.Fix Wfsimpl.Fixm.

(* Memory - work around an extraction bug. *)
Extraction NoInline Memory.Mem.valid_pointer.

(* Errors *)
Extraction Inline Errors.bind Errors.bind2.

(* Iteration *)

Extract Constant Iteration.GenIter.iterate =>
  "let rec iter f a =
     match f a with Coq_inl b -> Some b | Coq_inr a' -> iter f a'
   in iter".

(* Selection *)
(* 
Extract Constant Selection.compile_switch => "Switchaux.compile_switch".
Extract Constant Selection.if_conversion_heuristic => "Selectionaux.if_conversion_heuristic".

(* RTLgen *)
Extract Constant RTLgen.more_likely => "RTLgenaux.more_likely".
Extraction Inline RTLgen.ret RTLgen.error RTLgen.bind RTLgen.bind2.

(* Inlining *)
Extract Inlined Constant Inlining.should_inline => "Inliningaux.should_inline".
Extract Inlined Constant Inlining.inlining_info => "Inliningaux.inlining_info".
Extract Inlined Constant Inlining.inlining_analysis => "Inliningaux.inlining_analysis". *)
Extraction Inline Inlining.ret Inlining.bind.

(* Allocation *)
(* Extract Constant Allocation.regalloc => "Regalloc.regalloc".

(* Linearize *)
Extract Constant Linearize.enumerate_aux => "Linearizeaux.enumerate_aux". *)

(* SimplExpr *)
Extract Constant SimplExpr.first_unused_ident => "Camlcoq.first_unused_ident".
Extraction Inline SimplExpr.ret SimplExpr.error SimplExpr.bind SimplExpr.bind2.

(* Compopts *)
(* Extract Constant Compopts.optim_for_size =>
  "fun _ -> !Clflags.option_Osize".
Extract Constant Compopts.va_strict =>
  "fun _ -> false".
Extract Constant Compopts.propagate_float_constants =>
  "fun _ -> !Clflags.option_ffloatconstprop >= 1".
Extract Constant Compopts.generate_float_constants =>
  "fun _ -> !Clflags.option_ffloatconstprop >= 2".
Extract Constant Compopts.optim_tailcalls =>
  "fun _ -> !Clflags.option_ftailcalls".
Extract Constant Compopts.optim_constprop =>
  "fun _ -> !Clflags.option_fconstprop".
Extract Constant Compopts.optim_CSE =>
  "fun _ -> !Clflags.option_fcse".
Extract Constant Compopts.optim_redundancy =>
  "fun _ -> !Clflags.option_fredundancy".
Extract Constant Compopts.thumb =>
  "fun _ -> !Clflags.option_mthumb".
Extract Constant Compopts.debug =>
  "fun _ -> !Clflags.option_g". *)

Extract Constant CComp.print_Clight => "PrintClight.print_if".

(* Extract Inductive positive => "Bigint.t"
  [ "(fun p -> Bigint.of_zarith_bigint (Big_int_Z.succ_big_int (Big_int_Z.mult_big_int (Big_int_Z.big_int_of_int 2) (Bigint.to_zarith_bigint p))))"
      "(fun p -> Bigint.of_zarith_bigint (Big_int_Z.mult_big_int (Big_int_Z.big_int_of_int 2) (Bigint.to_zarith_bigint p)))" "(Bigint.of_zarith_bigint Big_int_Z.unit_big_int)" ]
  "(fun f2p1 f2p f1 p -> if Big_int_Z.le_big_int (Bigint.to_zarith_bigint p) Big_int_Z.unit_big_int then f1 () else let (q,r) = Big_int_Z.quomod_big_int (Bigint.to_zarith_bigint p) (Big_int_Z.big_int_of_int 2) in if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p (Bigint.of_zarith_bigint q) else f2p1 (Bigint.of_zarith_bigint q))".

Extract Inductive Z => "Bigint.t" [ "(Bigint.of_zarith_bigint Big_int_Z.zero_big_int)" "" "(fun z -> Bigint.of_zarith_bigint (Big_int_Z.minus_big_int (Bigint.to_zarith_bigint z)))" ]
  "(fun fO fp fn z -> let nz = (Bigint.to_zarith_bigint z) in let s = Big_int_Z.sign_big_int nz in if s = 0 then fO () else if s > 0 then fp z else fn (Bigint.of_zarith_bigint (Big_int_Z.minus_big_int nz)))".

Extract Inductive N => "Bigint.t" [ "(Bigint.of_zarith_bigint Big_int_Z.zero_big_int)" "" ]
  "(fun fO fp n -> if Big_int_Z.sign_big_int (Bigint.to_zarith_bigint n) <= 0 then fO () else fp n)". *)

(* Extract Constant SyntaxUtil.dummy_ident => "(fun () -> failwith ""unrealized dummy_ident reached"")".
Extract Constant SimplExpr.to_digit => "(fun x -> Char.chr 20)".
Extract Constant SimplExpr.N_to_string_aux => "(fun x y z -> z)". (* Don't remove: this line informs Coq to not actually extract this function. *)
Extract Constant SimplExpr.N_to_string => "(fun x -> Big_int_Z.string_of_big_int (Bigint.to_zarith_bigint x))".
Extract Constant SimplExpr.add1 => "(fun x -> Bigint.of_zarith_bigint (Big_int_Z.succ_big_int (Bigint.to_zarith_bigint x)))".
Extract Inlined Constant SimplExpr.Nzero => "(Bigint.of_zarith_bigint Big_int_Z.zero_big_int)".
Extract Inlined Constant BinNat.N.eqb => "Bigint.(=)".
Extract Inlined Constant BinNat.N.add => "Bigint.(+)".
Extract Inlined Constant Nat.add => "(+)". *)
(* TODO: figure out what is the correct reference of PrintClight *)

Extraction Blacklist List String Int.

Cd "extraction/lib/".
Separate Extraction Poulet4_Ccomp.CComp BinPos BinInt BinNat Integers Floats Values Csyntax String compcert.common.AST .
Cd "../../".
