/petr4/ci-test/type-checking/testdata/p4_16_samples/crash-typechecker.p4
\n
//#include <core.p4>

extern bit<16> get<D>(in D data);

header H {
    bit<8>      len;
    @length((bit<32>)len * 8 - 16)
    varbit<304> data;
}

control x() {
    H h;

    apply {
        get({ h });
    }
}
************************\n******** petr4 type checking result: ********\n************************\n
extern bit<16> get<D>(in D data);
header H {
  bit<8> len;
  @length(bit<32> len * 8 - 16)
  varbit <304> data;
}
control x() {
  H h;
  apply {
    get({h});
  }
}

