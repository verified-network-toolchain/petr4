/petr4/ci-test/type-checking/testdata/p4_16_samples/pipe.p4
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

match_kind {
    ternary,
    exact
}

typedef bit<9> BParamType;
struct TArg1 {
    bit<9> field1;
    bool drop;
}

struct TArg2 {
    int<32> field2;
}

struct PArg1 {
    bit<32> f0;
    bool drop;
}

typedef bit<32> PArg2;

struct QArg1 {
    bit<32> f1;
}

struct QArg2 {
    bit<32> f2;
}

extern bs {}
struct Packet_data {}

control T_host(inout TArg1 tArg1, in TArg2 aArg2)(bit<32> t2Size) {
    action B_action(out bit<9> barg, BParamType bData) {
        barg = (bit<9>)bData;
    }

    action C_action(bit<9> cData) {
        tArg1.field1 = cData;
    }

    table T {
        key = {
           tArg1.field1 : ternary;
           aArg2.field2 : exact;
        }
        actions = {
            B_action(tArg1.field1); // invoked binding tArg1.field1 to barg
            C_action;
        }

        size = t2Size;
        const default_action = C_action(9w5);
    }

    apply {
        T.apply();
    }
}

control P_pipe(inout TArg1 pArg1, inout TArg2 pArg2)(bit<32> t2Size) {
    T_host(t2Size) thost;

    action Drop() {
        pArg1.drop = true;
    }

    table Tinner {
        key = { pArg1.field1 : ternary; }
        actions = {
            Drop; NoAction;
        }
        const default_action = NoAction;
    }

    apply {
        thost.apply(pArg1, pArg2);
        thost.apply(pArg1, pArg2);
        Tinner.apply();
    }
}

control Q_pipe(inout TArg1 qArg1, inout TArg2 qArg2) {
    P_pipe(32w5) p1;  // instantiate pipeline p1 with parameter t2Size=5

    apply {
        p1.apply(qArg1, qArg2);            // invoke pipeline
    }
}

parser prs(bs b, out Packet_data p);
control pp(inout TArg1 arg1, inout TArg2 arg2);

package myswitch(prs prser, pp pipe);

parser my_parser(bs b, out Packet_data p) { state start { transition accept; } }

myswitch(my_parser(), Q_pipe()) main;
************************\n******** petr4 type checking result: ********\n************************\n
Uncaught exception:
  
  ("match_kind already declared" (match_kind ternary))

Raised at Base__Error.raise in file "src/error.ml" (inlined), line 8, characters 14-30
Called from Base__Error.raise_s in file "src/error.ml", line 9, characters 19-40
Called from Petr4__Checker.type_match_kind.add_mk in file "lib/checker.ml", line 3764, characters 9-77
Called from Stdlib__list.fold_left in file "list.ml", line 121, characters 24-34
Called from Base__List0.fold in file "src/list0.ml" (inlined), line 21, characters 22-52
Called from Petr4__Checker.type_match_kind in file "lib/checker.ml", line 3769, characters 12-54
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
