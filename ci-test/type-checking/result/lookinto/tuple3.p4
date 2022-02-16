/petr4/ci-test/type-checking/testdata/p4_16_samples/tuple3.p4
\n
const tuple<bit<32>, bit<32>> t = { 0, 1 };
const bit<32> f = t[0];
************************\n******** petr4 type checking result: ********\n************************\n
