/petr4/ci-test/type-checking/testdata/p4_16_samples/tuple4.p4
\n
control c(out bit<16> r) {
    apply {
        tuple<bit<32>, bit<16>> x = { 10, 12 };
        if (x == { 10, 12 })
           r = x[1];
        else
           r = (bit<16>)x[0];
    }
}

control _c(out bit<16> r);
package top(_c c);

top(c()) main;************************\n******** petr4 type checking result: ********\n************************\n
Uncaught exception:
  
  (lib/error.ml.Type
   ((I
     (filename /petr4/ci-test/type-checking/testdata/p4_16_samples/tuple4.p4)
     (line_start 5) (line_end ()) (col_start 15) (col_end 16))
    (Mismatch (expected array)
     (found (Tuple ((types ((Bit ((width 32))) (Bit ((width 16)))))))))))

Raised at Petr4__Error.raise_mismatch in file "lib/error.ml", line 37, characters 2-26
Called from Petr4__Checker.type_array_access in file "lib/checker.ml", line 1441, characters 20-57
Called from Petr4__Checker.type_expression in file "lib/checker.ml", line 854, characters 7-44
Called from Petr4__Checker.cast_expression in file "lib/checker.ml", line 941, characters 21-60
Called from Petr4__Checker.type_assignment in file "lib/checker.ml", line 2708, characters 20-72
Called from Petr4__Checker.type_statement in file "lib/checker.ml", line 2651, characters 7-38
Called from Petr4__Checker.type_conditional.type' in file "lib/checker.ml" (inlined), line 2758, characters 23-52
Called from Petr4__Checker.type_conditional in file "lib/checker.ml", line 2759, characters 18-27
Called from Petr4__Checker.type_statement in file "lib/checker.ml", line 2655, characters 7-44
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
