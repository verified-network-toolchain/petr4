/petr4/ci-test/type-checking/testdata/p4_16_samples/issue940.p4
\n
@deprecated("Please use verify_checksum/update_checksum instead.")
extern Checksum16 {
    Checksum16();
}

@deprecated("Please don't use this function.")
extern bit<6> wrong();

Checksum16() instance;

control c() {
    apply {
        bit<6> x = wrong();
    }
}
************************\n******** petr4 type checking result: ********\n************************\n
@deprecated("Please use verify_checksum/update_checksum instead.")
extern Checksum16 {
  Checksum16();
}

@deprecated("Please don't use this function.")
extern bit<6> wrong();
Checksum16() instance;
control c() {
  apply {
    bit<6> x = wrong();
  }
}

************************\n******** p4c type checking result: ********\n************************\n
