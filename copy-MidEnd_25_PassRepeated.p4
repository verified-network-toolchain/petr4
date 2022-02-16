struct S {
    bit<32> x;
}

control c(inout bit<32> b) {
    @name("c.a") action a() {
        {
            ;
        }
        b = 32w0;
    }
    apply {
        a();
    }
}

control proto(inout bit<32> _b);
package top(proto _p);
top(c()) main;

