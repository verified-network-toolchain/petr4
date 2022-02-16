/petr4/ci-test/type-checking/testdata/p4_16_samples/cast_noop.p4
\n
const bool x = (bool)1;
const bool y = (bool)1w1;
const bool v = (bool)1w0;
const bool z = (bool)true;
const bool w = (bool)(bool)false;
************************\n******** petr4 type checking result: ********\n************************\n
************************\n******** p4c type checking result: ********\n************************\n
