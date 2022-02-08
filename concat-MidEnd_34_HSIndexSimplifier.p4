control proto(out bit<32> x);
package top(proto _c);
control c(out bit<32> x) {
    apply {
        x = 32w0xf0f1e1e;
    }
}

top(c()) main;

