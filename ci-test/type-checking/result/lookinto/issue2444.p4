/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2444.p4
\n
const int a =  1;
const bool b = (bool)a;

const int z = (int)2w1;
const bool w = (bool)z;

const int z1 = 2w1;
const bool w1 = (bool)z1;

const int z2 = 2w3;
const int z3 = 2s3;
************************\n******** petr4 type checking result: ********\n************************\n
