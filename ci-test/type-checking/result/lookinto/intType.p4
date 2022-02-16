/petr4/ci-test/type-checking/testdata/p4_16_samples/intType.p4
\n
const int a = 5;
const int b = 2 * a;
const int c = b - a + 3;
************************\n******** petr4 type checking result: ********\n************************\n
const int a = 5;
const int b = 2*a;
const int c = b-a+3;

