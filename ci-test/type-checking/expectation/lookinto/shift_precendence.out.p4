/petr4/ci-test/type-checking/testdata/p4_16_samples/shift_precendence.p4
\n
control i(out bit<4> a, out bit<16> x) {
    bit<4> tmp_0;
    apply {
        tmp_0 = 4w0;
        a = 4w1 & (4w2 + tmp_0) >> 4w2;
        x = 0xffff >> 3 >> 1;
    }
}

control c(out bit<4> a, out bit<16> x);
package top(c _c);
top(i()) main;

************************\n******** petr4 type checking result: ********\n************************\n
control i(out bit<4> a, out bit<16> x) {
  bit<4> tmp_0;
  apply {
    tmp_0 = 4w0;
    a = 4w1 & 4w2+tmp_0>>4w2;
    x = 65535>>3>>1;
  }
}
control c (out bit<4> a, out bit<16> x);
package top (c _c);
top(i()) main;

************************\n******** p4c type checking result: ********\n************************\n
