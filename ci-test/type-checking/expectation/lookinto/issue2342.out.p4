/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2342.p4
\n
const bool tmp = 1 != 8w2[7:0];
************************\n******** petr4 type checking result: ********\n************************\n
const bool tmp = 1!=8w2[7:0];

************************\n******** p4c type checking result: ********\n************************\n