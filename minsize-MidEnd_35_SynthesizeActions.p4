header H {
}

control c(out bit<32> v) {
    @hidden action minsize27() {
        v = 32w128;
    }
    apply {
        minsize27();
    }
}

control cproto(out bit<32> v);
package top(cproto _c);
top(c()) main;

