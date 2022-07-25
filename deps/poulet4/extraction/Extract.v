Set Warnings "-extraction-reserved-identifier".
Require Coq.extraction.Extraction.
Require Import Coq.extraction.ExtrOcamlBasic.
Require Import Coq.extraction.ExtrOcamlNativeString.

Require Import Coq.Numbers.BinNums.

Extract Inductive nat =>
int [ "0" "Stdlib.Int.succ" ]
    "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Extract Constant pred => "fun n -> Stdlib.max 0 (n-1)".
Extract Constant minus => "fun n m -> Stdlib.max 0 (n-m)".

Extract Inlined Constant max => "Stdlib.max".
Extract Inlined Constant min => "Stdlib.min".

Extract Inductive positive => "Bigint.t"
  [ "(fun p -> Bigint.of_zarith_bigint (Zarith.Z.succ (Zarith.Z.mul (Zarith.Z.of_int 2) (Bigint.to_zarith_bigint p))))"
      "(fun p -> Bigint.of_zarith_bigint (Zarith.Z.mul (Zarith.Z.of_int 2) (Bigint.to_zarith_bigint p)))" "(Bigint.of_zarith_bigint Zarith.Z.one)" ]
  "(fun f2p1 f2p f1 p -> if Zarith.Z.leq (Bigint.to_zarith_bigint p) Zarith.Z.one then f1 () else let (q,r) = Zarith.Z.div_rem (Bigint.to_zarith_bigint p) (Zarith.Z.of_int 2) in if Zarith.Z.equal r Zarith.Z.zero then f2p (Bigint.of_zarith_bigint q) else f2p1 (Bigint.of_zarith_bigint q))".

Extract Inductive Z => "Bigint.t" [ "(Bigint.of_zarith_bigint Zarith.Z.zero)" "" "(fun z -> Bigint.of_zarith_bigint (Zarith.Z.neg (Bigint.to_zarith_bigint z)))" ]
  "(fun fO fp fn z -> let nz = (Bigint.to_zarith_bigint z) in let s = Zarith.Z.sign nz in if s = 0 then fO () else if s > 0 then fp z else fn (Bigint.of_zarith_bigint (Zarith.Z.neg nz)))".

Extract Inductive N => "Bigint.t" [ "(Bigint.of_zarith_bigint Zarith.Z.zero)" "" ]
  "(fun fO fp n -> if Zarith.Z.sign (Bigint.to_zarith_bigint n) <= 0 then fO () else fp n)".

Require Poulet4.P4light.Transformations.SimplExpr.
Require Poulet4.P4light.Transformations.GenLoc.

Extract Constant SyntaxUtil.dummy_ident => "(fun () -> failwith ""unrealized dummy_ident reached"")".
Extract Constant SimplExpr.to_digit => "(fun x -> Char.chr 20)".
Extract Constant SimplExpr.N_to_string_aux => "(fun x y z -> z)". (* Don't remove: this line informs Coq to not actually extract this function. *)
Extract Constant SimplExpr.N_to_string => "(fun x -> Zarith.Z.to_string (Bigint.to_zarith_bigint x))".
Extract Constant SimplExpr.add1 => "(fun x -> Bigint.of_zarith_bigint (Zarith.Z.succ (Bigint.to_zarith_bigint x)))".
Extract Inlined Constant SimplExpr.Nzero => "(Bigint.of_zarith_bigint (Zarith.Z.of_int 0))".
Extract Inlined Constant BinNat.N.eqb => "Bigint.(=)".
Extract Inlined Constant BinNat.N.add => "Bigint.(+)".
Extract Inlined Constant Nat.add => "(+)".

Require Poulet4.P4light.Semantics.Interpreter.
Require Poulet4.P4light.Syntax.Syntax.
Require Poulet4.P4light.Syntax.Typed.
Require Poulet4.P4light.Syntax.ConstValue.
Require Poulet4.GCL.GCL.
Require Poulet4.Compile.ToP4cub.
Require Poulet4.GCL.ToGCL.
Require Poulet4.GCL.TableInstr.
Require Poulet4.GCL.V1model.
Require Poulet4.P4cub.ExportAll.

(* The Set Extraction Flag 716 command below turns on the following
extraction optimizations.

See the refman for details: https://coq.inria.fr/refman/addendum/extraction.html#coq:flag.Extraction-Optimize

716 = 0b01011001100
         | ||  |+---Simplify case with iota-redux
         | ||  +----Factor case branches as functions
         | |+-------Simplify case by swapping case and lambda
         | +--------Some case optimization
         +----------Use linear let reduction

It is necessary in order to compile interp_isValid as it is currently written,
because it includes a nested fixpoint which OCaml normally rejects.

    File "extraction/Interpreter.ml", lines 724-748, characters 6-61:
    724 | ......let x0 = x fix_0 in
    725 |       (fun sv ->
    726 |       match sv with
    727 |       | ValBaseNull -> Coq_interp_isValid_graph_equation_1
    728 |       | ValBaseBool o -> Coq_interp_isValid_graph_equation_2 o
    ...
    745 |       | ValBaseEnumField (typ_name, enum_name) ->
    746 |         Coq_interp_isValid_graph_equation_15 (typ_name, enum_name)
    747 |       | ValBaseSenumField (typ_name, sv0) ->
    748 |         Coq_interp_isValid_graph_equation_16 (typ_name, sv0))
    Error: This kind of expression is not allowed as right-hand side of `let rec'

The optimizations somehow optimize away the nested fixpoint and avoid this error message.
 *)

Set Extraction Flag 716.
Extraction Inline Interpreter.interp_isValid.
Extraction NoInline Interpreter.interp_isValid_fields.

(* Extract Constant VarNameGen.string_of_nat => "Int.to_string". *)
Separate Extraction
         Poulet4.P4light.Syntax.Syntax
         Poulet4.P4light.Syntax.Typed
         Poulet4.P4light.Semantics.Interpreter
         Poulet4.P4light.Transformations.SimplExpr
         Poulet4.P4light.Transformations.GenLoc
         Poulet4.P4light.Syntax.ConstValue
         Poulet4.Compile.ToP4cub
         Poulet4.GCL.GCL
         Poulet4.GCL.ToGCL
         Poulet4.GCL.TableInstr
         Poulet4.GCL.V1model
         Poulet4.P4cub.Transformations.Lifting.Statementize.
