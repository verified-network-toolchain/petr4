/petr4/ci-test/type-checking/testdata/p4_16_samples/pragma-pkginfo.p4
\n
@pragma pkginfo name="x", value=0
const bit<32> x = 0;
************************\n******** petr4 type checking result: ********\n************************\n
@pkginfo(name= "x", value=0)
const bit<32> x = 0;

