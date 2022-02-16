/petr4/ci-test/type-checking/testdata/p4_16_samples/issue1160.p4
\n
// single-line comment

/// Triple-line comment
const bit x = 0;

/**
 * Java-doc style comment
 */
const bit y = 1;
************************\n******** petr4 type checking result: ********\n************************\n
const bit<1> x = 0;
const bit<1> y = 1;

************************\n******** p4c type checking result: ********\n************************\n
