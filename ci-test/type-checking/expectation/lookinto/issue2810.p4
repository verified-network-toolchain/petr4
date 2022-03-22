/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2810.p4
\n
#include <core.p4>

control HwControl<H>(inout H hdr);

package Switch<H>(HwControl<H> c);

extern void HwSplFunc<T, R>(in T hdr1, @optional in R hdr2);

header eth_t {
    bit<48> sa;
    bit<48> da;
    bit<16> type;
}

struct parsed_header_t {
    eth_t mac;
}

control match_action_unit(inout parsed_header_t hdr) {
    apply {
        HwSplFunc(hdr.mac);
    }
}

Switch(match_action_unit()) main;
************************\n******** petr4 type checking result: ********\n************************\n
Uncaught exception:
  
  "could not infer valid type for don't care argument"

Raised at Base__Error.raise in file "src/error.ml" (inlined), line 8, characters 14-30
Called from Base__Error.raise_s in file "src/error.ml", line 9, characters 19-40
Called from Base__List.count_map in file "src/list.ml", line 391, characters 13-17
Called from Base__List.map in file "src/list.ml" (inlined), line 418, characters 15-31
Called from Petr4__Checker.type_function_call in file "lib/checker.ml", line 2345, characters 26-85
Called from Petr4__Checker.type_method_call in file "lib/checker.ml", line 2678, characters 19-80
Called from Petr4__Checker.type_statement in file "lib/checker.ml", line 2649, characters 7-61
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
