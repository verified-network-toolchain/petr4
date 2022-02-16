/petr4/ci-test/type-checking/testdata/p4_16_samples/constStruct.p4
\n
struct S {
    bit<8> x;
}

const S s = {
    x = 1024
};
const bit<16> z = (bit<16>)s.x;

control c(out bit<16> result) {
    apply {
        result = z;
    }
}

control ctrl(out bit<16> result);
package top(ctrl _c);
top(c()) main;
************************\n******** petr4 type checking result: ********\n************************\n
