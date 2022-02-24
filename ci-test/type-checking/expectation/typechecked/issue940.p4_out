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
/petr4/ci-test/type-checking/testdata/p4_16_samples/issue940.p4(9): [--Wwarn=deprecated] warning: Checksum16: Using deprecated feature Checksum16. Please use verify_checksum/update_checksum instead.
Checksum16() instance;
^^^^^^^^^^
/petr4/ci-test/type-checking/testdata/p4_16_samples/issue940.p4(2)
extern Checksum16 {
       ^^^^^^^^^^
/petr4/ci-test/type-checking/testdata/p4_16_samples/issue940.p4(13): [--Wwarn=deprecated] warning: wrong: Using deprecated feature wrong. Please don't use this function.
        bit<6> x = wrong();
                   ^^^^^
/petr4/ci-test/type-checking/testdata/p4_16_samples/issue940.p4(7)
extern bit<6> wrong();
              ^^^^^
/petr4/ci-test/type-checking/testdata/p4_16_samples/issue940.p4(9): [--Wwarn=unused] warning: instance: unused instance
Checksum16() instance;
             ^^^^^^^^
[--Wwarn=missing] warning: Program does not contain a `main' module
