struct S {
    bit<32> l;
    bit<32> r;
}

control c(out bool z);
package top(c _c);
struct tuple_0 {
    bit<32> f0;
    bit<32> f1;
}

control test(out bool zout) {
    @name("test.p") tuple_0 p_0;
    @name("test.q") S q_0;
    apply {
        {
            p_0.f0 = 32w4;
            p_0.f1 = 32w5;
        }
        {
            q_0.l = 32w2;
            q_0.r = 32w3;
        }
        zout = p_0.f0 == 32w4 && p_0.f1 == 32w5;
        zout = zout && (q_0.l == 32w2 && q_0.r == 32w3);
    }
}

top(test()) main;

