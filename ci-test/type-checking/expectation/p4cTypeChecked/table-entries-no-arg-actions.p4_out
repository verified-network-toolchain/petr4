/petr4/ci-test/type-checking/testdata/p4_16_samples/table-entries-no-arg-actions.p4
\n
/*
* Copyright 2019, Cornell University
*
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

control C(inout bit<2> x);
package S(C c);

control MyC(inout bit<2> x) {
    action a() { }
    action b() { }
    table t {
        key = { x : exact; }
        actions = {a; b;}
        const entries = {
            { 0 } : a;
            { 1 } : b;
            { 2 } : a();
            { 3 } : b();
        }
    }
    apply {
        t.apply();
    }
}

S(MyC()) main;
************************\n******** petr4 type checking result: ********\n************************\n
Uncaught exception:
  
  ("cannot cast"
   (expr
    ((I
      (filename
       /petr4/ci-test/type-checking/testdata/p4_16_samples/table-entries-no-arg-actions.p4)
      (line_start 29) (line_end ()) (col_start 12) (col_end 17))
     ((expr
       (List
        (values
         (((I
            (filename
             /petr4/ci-test/type-checking/testdata/p4_16_samples/table-entries-no-arg-actions.p4)
            (line_start 29) (line_end ()) (col_start 14) (col_end 15))
           ((expr
             (Cast (typ (Bit ((width 2))))
              (expr
               ((I
                 (filename
                  /petr4/ci-test/type-checking/testdata/p4_16_samples/table-entries-no-arg-actions.p4)
                 (line_start 29) (line_end ()) (col_start 14) (col_end 15))
                ((expr
                  (Int
                   ((I
                     (filename
                      /petr4/ci-test/type-checking/testdata/p4_16_samples/table-entries-no-arg-actions.p4)
                     (line_start 29) (line_end ()) (col_start 14)
                     (col_end 15))
                    ((value 0) (width_signed ())))))
                 (typ Integer) (dir Directionless))))))
            (typ (Bit ((width 2)))) (dir Directionless)))))))
      (typ (List ((types ((Bit ((width 2)))))))) (dir Directionless))))
   (typ (Bit ((width 2)))))

Raised at Base__Error.raise in file "src/error.ml" (inlined), line 8, characters 14-30
Called from Base__Error.raise_s in file "src/error.ml", line 9, characters 19-40
Called from Petr4__Checker.cast_if_needed in file "lib/checker.ml", line 901, characters 37-70
Called from Petr4__Checker.check_match in file "lib/checker.ml", line 2983, characters 22-70
Called from Petr4__Checker.check_match_product in file "lib/checker.ml", line 2992, characters 6-29
Called from Petr4__Checker.type_table_entries.type_table_entry in file "lib/checker.ml", line 3373, characters 24-79
Called from Base__List.count_map in file "src/list.ml", line 399, characters 13-17
Called from Petr4__Checker.type_table' in file "lib/checker.ml", line 3578, characters 31-87
Called from Petr4__Checker.type_table in file "lib/checker.ml", line 3314, characters 2-95
Called from Petr4__Checker.type_declarations.f in file "lib/checker.ml", line 4118, characters 26-55
Called from Stdlib__list.fold_left in file "list.ml", line 121, characters 24-34
Called from Base__List0.fold in file "src/list0.ml" (inlined), line 21, characters 22-52
Called from Petr4__Checker.type_declarations in file "lib/checker.ml", line 4121, characters 19-58
Called from Petr4__Checker.open_control_scope in file "lib/checker.ml", line 3087, characters 26-73
Called from Petr4__Checker.type_control in file "lib/checker.ml", line 3096, characters 6-69
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
