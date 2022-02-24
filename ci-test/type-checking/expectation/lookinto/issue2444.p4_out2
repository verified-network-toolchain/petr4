/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2444.p4
\n
const int a =  1;
const bool b = (bool)a;

const int z = (int)2w1;
const bool w = (bool)z;

const int z1 = 2w1;
const bool w1 = (bool)z1;

const int z2 = 2w3;
const int z3 = 2s3;
************************\n******** petr4 type checking result: ********\n************************\n
Uncaught exception:
  
  ("illegal explicit cast" (old_type Integer) (new_type Bool))

Raised at Base__Error.raise in file "src/error.ml" (inlined), line 8, characters 14-30
Called from Base__Error.raise_s in file "src/error.ml", line 9, characters 19-40
Called from Petr4__Checker.type_expression in file "lib/checker.ml", line 866, characters 7-33
Called from Petr4__Checker.cast_expression in file "lib/checker.ml", line 923, characters 21-60
Called from Petr4__Checker.type_constant in file "lib/checker.ml", line 2905, characters 19-65
Called from Petr4__Checker.type_declarations.f in file "lib/checker.ml", line 4118, characters 26-55
Called from Stdlib__list.fold_left in file "list.ml", line 121, characters 24-34
Called from Base__List0.fold in file "src/list0.ml" (inlined), line 21, characters 22-52
Called from Petr4__Checker.type_declarations in file "lib/checker.ml", line 4121, characters 19-58
Called from Petr4__Checker.check_program in file "lib/checker.ml", line 4128, characters 18-78
Called from Petr4__Common.Make_parse.check_file' in file "lib/common.ml", line 95, characters 17-51
Called from Petr4__Common.Make_parse.check_file in file "lib/common.ml", line 108, characters 10-50
Called from Main.check_command.(fun) in file "bin/main.ml", line 70, characters 14-65
Called from Core_kernel__Command.For_unix.run.(fun) in file "src/command.ml", line 2453, characters 8-238
Called from Base__Exn.handle_uncaught_aux in file "src/exn.ml", line 111, characters 6-10
************************\n******** p4c type checking result: ********\n************************\n
/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2444.p4(11): [--Wwarn=overflow] warning: 2s3: signed value does not fit in 2 bits
const int z3 = 2s3
               ^^^
[--Wwarn=missing] warning: Program does not contain a `main' module
