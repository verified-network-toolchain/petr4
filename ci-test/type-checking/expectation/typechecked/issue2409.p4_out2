/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2409.p4
\n
#include <core.p4>

parser p(out bit<32> z) {
    state start {
        bool b = true;
        if (b) {
            bit<32> x = 1;
            z = x;
        } else {
            bit<32> w = 2;
            z = w;
        }
        transition accept;
    }
}

parser _p(out bit<32> z);
package top(_p _pa);
top(p()) main;
************************\n******** petr4 type checking result: ********\n************************\n
File /petr4/ci-test/type-checking/testdata/p4_16_samples/issue2409.p4, line 6, characters 8-10: syntax error
************************\n******** p4c type checking result: ********\n************************\n
/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2409.p4(3): [--Wwarn=uninitialized_out_param] warning: out parameter 'z' may be uninitialized when 'p' terminates
parser p(out bit<32> z) {
                     ^
/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2409.p4(3)
parser p(out bit<32> z) {
       ^
[--Wwarn=parser-transition] warning: SelectCase: unreachable case
[--Wwarn=parser-transition] warning: SelectCase: unreachable case
