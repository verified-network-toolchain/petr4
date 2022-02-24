/petr4/ci-test/type-checking/testdata/p4_16_samples/default-switch.p4
\n
control ctrl() {
    action a() {}
    action b() {}

    table t {
        actions = { a; b; }
        default_action = a;
    }

    apply {
        switch (t.apply().action_run) {
            default:
            b: { return; }
        }
    }
}************************\n******** petr4 type checking result: ********\n************************\n
Uncaught exception:
  
  (lib/error.ml.Type
   ((I
     (filename
      /petr4/ci-test/type-checking/testdata/p4_16_samples/default-switch.p4)
     (line_start 13) (line_end ()) (col_start 12) (col_end 13))
    UnreachableBlock))

Raised at Petr4__Checker.type_switch.label_checker in file "lib/checker.ml", line 2854, characters 40-84
Called from Petr4__Checker.type_switch.case_checker in file "lib/checker.ml", line 2867, characters 25-55
Called from Stdlib__list.fold_left in file "list.ml", line 121, characters 24-34
Called from Base__List0.fold in file "src/list0.ml" (inlined), line 21, characters 22-52
Called from Petr4__Checker.type_switch in file "lib/checker.ml", line 2878, characters 14-54
Called from Petr4__Checker.type_statement in file "lib/checker.ml", line 2669, characters 7-47
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
/petr4/ci-test/type-checking/testdata/p4_16_samples/default-switch.p4(13): [--Wwarn=ordering] warning: b: label following 'default' DefaultExpression label.
            b: { return; }
            ^
/petr4/ci-test/type-checking/testdata/p4_16_samples/default-switch.p4(12)
            default:
            ^^^^^^^
[--Wwarn=missing] warning: Program does not contain a `main' module
