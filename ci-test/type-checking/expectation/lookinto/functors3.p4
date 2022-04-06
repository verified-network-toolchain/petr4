/petr4/ci-test/type-checking/testdata/p4_16_samples/functors3.p4
\n
/*
Copyright 2013-present Barefoot Networks, Inc.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/

#include <core.p4>

parser p1(out bit z1)(bit b1) {
    state start {
        z1 = b1;
        transition accept;
    }
}

parser p(out bit z)(bit b, bit c) {
   p1(b) p1i;

   state start {
        p1i.apply(z);
        z = z & b & c;
        transition accept;
   }
}

const bit bv = 1w0;

parser simple(out bit z);
package m(simple n);

m(p(bv, 1w1)) main;
************************\n******** petr4 type checking result: ********\n************************\n
Uncaught exception:
  
  ("constructor argument is not compile-time known"
   (arg
    ((I
      (filename
       /petr4/ci-test/type-checking/testdata/p4_16_samples/functors3.p4)
      (line_start 27) (line_end ()) (col_start 6) (col_end 7))
     ((expr
       (Name
        (BareName
         ((I
           (filename
            /petr4/ci-test/type-checking/testdata/p4_16_samples/functors3.p4)
           (line_start 27) (line_end ()) (col_start 6) (col_end 7))
          b))))
      (typ (Bit ((width 1)))) (dir Directionless)))))

Raised at Base__Error.raise in file "src/error.ml" (inlined), line 8, characters 14-30
Called from Base__Error.raise_s in file "src/error.ml", line 9, characters 19-40
Called from Base__List.rev_filter_map.loop in file "src/list.ml", line 812, characters 13-17
Called from Base__List.filter_map in file "src/list.ml" (inlined), line 819, characters 26-47
Called from Petr4__Checker.type_constructor_invocation in file "lib/checker.ml", line 2560, characters 4-50
Called from Petr4__Checker.type_nameless_instantiation in file "lib/checker.ml", line 2573, characters 32-97
Called from Petr4__Checker.type_instantiation in file "lib/checker.ml", line 2928, characters 23-77
Called from Petr4__Checker.type_declarations.f in file "lib/checker.ml", line 4118, characters 26-55
Called from Stdlib__list.fold_left in file "list.ml", line 121, characters 24-34
Called from Base__List0.fold in file "src/list0.ml" (inlined), line 21, characters 22-52
Called from Petr4__Checker.type_declarations in file "lib/checker.ml", line 4121, characters 19-58
Called from Petr4__Checker.open_parser_scope in file "lib/checker.ml", line 3045, characters 26-73
Called from Petr4__Checker.type_parser in file "lib/checker.ml", line 3057, characters 4-72
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