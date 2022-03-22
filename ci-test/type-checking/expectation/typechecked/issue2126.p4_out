/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2126.p4
\n
parser p() {
    state start {
        {
            bit<16> retval = 0;
        }
        {
            bit<16> retval = 1;
        }
        transition accept;
    }
}
************************\n******** petr4 type checking result: ********\n************************\n
parser p() {
  state start {
    {
      bit<16> retval = 0;
    }
    {
      bit<16> retval = 1;
    }
    transition accept;
  }
}

************************\n******** p4c type checking result: ********\n************************\n
[--Wwarn=missing] warning: Program does not contain a `main' module
