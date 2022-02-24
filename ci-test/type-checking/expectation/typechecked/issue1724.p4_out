/petr4/ci-test/type-checking/testdata/p4_16_samples/issue1724.p4
\n

action test(inout bit<16> a, inout bit<2> b) {
    b = (a << 3)[1:0];
}
************************\n******** petr4 type checking result: ********\n************************\n
action test(inout bit<16> a, inout bit<2> b) {
  b = a<<3[1:0];
}

************************\n******** p4c type checking result: ********\n************************\n
[--Wwarn=missing] warning: Program does not contain a `main' module
