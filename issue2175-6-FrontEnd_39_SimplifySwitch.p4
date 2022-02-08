control c(inout bit<32> y) {
    apply {
    }
}

control t(inout bit<32> b) {
    @name("c1") c() c1_0;
    apply {
        c1_0.apply(b);
    }
}

control cs(inout bit<32> arg);
package top(cs _ctrl);
top(t()) main;

