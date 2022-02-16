/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2019.p4
\n
control V<H>(inout H hdr);

control EmptyV<H>(inout H hdr) {
    apply { }
}

struct E {}

package S<H1>(V<H1> vr = EmptyV<H1>());
S<E>() main;
************************\n******** petr4 type checking result: ********\n************************\n
************************\n******** p4c type checking result: ********\n************************\n
