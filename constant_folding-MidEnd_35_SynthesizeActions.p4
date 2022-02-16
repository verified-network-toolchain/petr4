control proto(out bit<32> x);
package top(proto _c);
control c(out bit<32> x) {
    @hidden action constant_folding59() {
        x = 32w17;
    }
    apply {
        constant_folding59();
    }
}

top(c()) main;

