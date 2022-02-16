/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2630.p4
\n
control C<H>(inout H h);
package Pipeline<H>(C<H> c);
package Switch<H0, H1>(Pipeline<H0> p0, @optional Pipeline<H1> p1);


struct header_t {
}
control MyC(inout header_t h) {
    apply {}
}

Pipeline(MyC()) pipe;
Switch(pipe) main;
************************\n******** petr4 type checking result: ********\n************************\n
