/petr4/ci-test/type-checking/testdata/p4_16_samples/generic-struct-tuple.p4
\n
struct S<T> {
    tuple<T, T> t;
}

const S<bit<32>> x = { t = { 0, 0 } };************************\n******** petr4 type checking result: ********\n************************\n
************************\n******** p4c type checking result: ********\n************************\n
