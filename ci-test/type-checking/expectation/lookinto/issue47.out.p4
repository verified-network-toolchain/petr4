/petr4/ci-test/type-checking/testdata/p4_16_samples/issue47.p4
\n
const bit<(5 + 3)> b = 10;
const bit<(b)> c = 2;
************************\n******** petr4 type checking result: ********\n************************\n
const bit<(5+3)> b = 10;
const bit<(b)> c = 2;

************************\n******** p4c type checking result: ********\n************************\n