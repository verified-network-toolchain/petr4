control c(inout bit<32> y) {
    apply {
    }
}

control t(inout bit<32> b) {
    @name("c1") c() c1_0;
    apply {
        {
        }
    }
}

control cs(inout bit<32> arg);
package top(cs _ctrl);
top(t()) main;

