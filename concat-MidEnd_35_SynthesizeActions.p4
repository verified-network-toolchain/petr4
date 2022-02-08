control proto(out bit<32> x);
package top(proto _c);
control c(out bit<32> x) {
    @hidden action concat24() {
        x = 32w0xf0f1e1e;
    }
    apply {
        concat24();
    }
}

top(c()) main;

