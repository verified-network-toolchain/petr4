/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2627.p4
\n
struct H3<T> {
    tuple<T> t;
}

struct S {
    bit<32> b;
}

const H3<S> h4 = {
    t = { { b = 0 } }
};
************************\n******** petr4 type checking result: ********\n************************\n
************************\n******** p4c type checking result: ********\n************************\n
