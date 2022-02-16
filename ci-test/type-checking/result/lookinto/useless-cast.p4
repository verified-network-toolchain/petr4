/petr4/ci-test/type-checking/testdata/p4_16_samples/useless-cast.p4
\n
control c(out bit<32> y) {
    bit<32> x = 10;

    apply {
        y = (bit<32>)x;
    }
}************************\n******** petr4 type checking result: ********\n************************\n
control c(out bit<32> y) {
  bit<32> x = 10;
  apply {
    y = (bit<32>) x;
  }
}

************************\n******** p4c type checking result: ********\n************************\n
