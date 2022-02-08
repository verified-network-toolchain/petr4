struct S {
    bit<32> x;
}

control c(inout bit<32> b) {
    @name("c.s1") S s1_0;
    @name("c.s2") S s2_0;
    @name("c.a") action a() {
        {
            s2_0.x = 32w0;
        }
        {
            s1_0.x = s2_0.x;
        }
        {
            s2_0.x = s1_0.x;
        }
        b = s2_0.x;
    }
    apply {
        a();
    }
}

control proto(inout bit<32> _b);
package top(proto _p);
top(c()) main;

