/petr4/ci-test/type-checking/testdata/p4_16_samples/minsize.p4
\n
/*
Copyright 2021 VMware, Inc.

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

typedef bit<32> T;

header H {}

control c(out bit<32> v) {
    apply
    {
        bit<32> b;
        H[0] h;

        v = b.minSizeInBits() + T.minSizeInBits() + b.maxSizeInBits() + T.maxSizeInBits() + h[0].minSizeInBits();
    }
}

const int w = T.maxSizeInBits();

control cproto(out bit<32> v);
package top(cproto _c);

top(c()) main;
************************\n******** petr4 type checking result: ********\n************************\n
Uncaught exception:
  
  (lib/error.ml.Type
   ((I
     (filename
      /petr4/ci-test/type-checking/testdata/p4_16_samples/minsize.p4)
     (line_start 27) (line_end ()) (col_start 12) (col_end 13))
    (UnfoundMember (expected_member minSizeInBits))))

Raised at Petr4__Error.raise_unfound_member in file "lib/error.ml", line 41, characters 2-26
Called from Petr4__Checker.type_expression_member in file "lib/checker.ml", line 2115, characters 12-30
Called from Petr4__Checker.type_expression in file "lib/checker.ml", line 872, characters 7-47
Called from Petr4__Checker.resolve_function_overload_by.resolve_by_type in file "lib/checker.ml", line 2520, characters 20-48
Called from Petr4__Checker.resolve_function_overload_by in file "lib/checker.ml", line 2524, characters 5-41
Called from Petr4__Checker.type_function_call in file "lib/checker.ml", line 2311, characters 19-62
Called from Petr4__Checker.type_expression in file "lib/checker.ml", line 876, characters 7-62
Called from Petr4__Checker.cast_expression in file "lib/checker.ml", line 941, characters 21-60
Called from Petr4__Checker.cast_expression in file "lib/checker.ml", line 1013, characters 22-54
Called from Petr4__Checker.cast_expression in file "lib/checker.ml", line 1013, characters 22-54
Called from Petr4__Checker.cast_expression in file "lib/checker.ml", line 1013, characters 22-54
Called from Petr4__Checker.cast_expression in file "lib/checker.ml", line 1013, characters 22-54
Called from Petr4__Checker.type_assignment in file "lib/checker.ml", line 2708, characters 20-72
Called from Petr4__Checker.type_statement in file "lib/checker.ml", line 2651, characters 7-38
Called from Petr4__Checker.type_statements.fold in file "lib/checker.ml", line 2782, characters 26-58
Called from Stdlib__list.fold_left in file "list.ml", line 121, characters 24-34
Called from Petr4__Checker.type_block in file "lib/checker.ml", line 2794, characters 27-73
Called from Petr4__Checker.type_control in file "lib/checker.ml", line 3098, characters 29-61
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
