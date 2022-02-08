struct S {
    bit<8> x;
}

control c(out bit<16> result) {
    @hidden action constStruct12() {
        result = 16w0;
    }
    apply {
        constStruct12();
    }
}

control ctrl(out bit<16> result);
package top(ctrl _c);
top(c()) main;

