/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2019-1.p4
\n
control C<H>(inout H hdr);
control V<H>(inout H hdr);

struct E {}

control Some(inout E m) {
    apply {}
}

control EmptyV<H>(inout H hdr) {
    apply {}
}

package S<H1>(C<H1> s, V<H1> vr = EmptyV<H1>());
S<E>(Some()) main;
************************\n******** petr4 type checking result: ********\n************************\n
************************\n******** p4c type checking result: ********\n************************\n
