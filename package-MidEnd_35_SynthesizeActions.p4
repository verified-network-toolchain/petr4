control proto(out bit<32> o);
package top(proto _c, bool parameter);
control c(out bit<32> o) {
    @hidden action package21() {
        o = 32w0;
    }
    apply {
        package21();
    }
}

top(c(), true) main;

