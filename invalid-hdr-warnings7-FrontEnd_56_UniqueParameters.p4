header H1 {
    bit<32> a;
}

header H2 {
    bit<32> a;
}

header_union U {
    H1 h1;
    H2 h2;
}

control ct(inout bit<32> param);
package top(ct _ct);
control c(inout bit<32> x) {
    @name("u") U u;
    @name("hs") H1[2] hs;
    @name("us") U[2] us;
    @name("i") bit<1> i;
    @name("initialize") action initialize_0(@name("u1") out U u1, @name("hs1") out H1[2] hs1, @name("us1") out U[2] us1) {
        u1.h1.a = 32w1;
        u1.h2.a = 32w1;
        hs1[0].a = 32w1;
        hs1[1].a = 32w1;
        us1[0].h1.a = 32w1;
        us1[0].h2.a = 32w1;
        u1.h1.setValid();
        u1.h2.setValid();
        hs1[0].setValid();
        hs1[1].setValid();
        us1[0].h1.setValid();
        us1[0].h2.setValid();
    }
    @name("inout_action1") action inout_action1_0(@name("u1") inout U u1_4, @name("hs1") inout H1[2] hs1_4, @name("us1") inout U[2] us1_4) {
        u1_4.h1.a = 32w1;
        u1_4.h2.a = 32w1;
        hs1_4[0].a = 32w1;
        hs1_4[1].a = 32w1;
        us1_4[0].h1.a = 32w1;
        us1_4[0].h2.a = 32w1;
        hs1_4[0].setInvalid();
        u1_4.h1.setValid();
        us1_4[0].h1.setValid();
    }
    @name("inout_action2") action inout_action2_0(@name("u1") inout U u1_5, @name("hs1") inout H1[2] hs1_5, @name("us1") inout U[2] us1_5) {
        i = 1w1;
        us1_5[i].h1.setInvalid();
        us1_5[i].h2.setValid();
    }
    @name("xor") action xor_0(@name("u1") in U u1_6, @name("hs1") in H1[2] hs1_6, @name("us1") in U[2] us1_6, @name("result") out bit<32> result) {
        result = u1_6.h1.a ^ u1_6.h2.a ^ hs1_6[0].a ^ hs1_6[1].a ^ us1_6[0].h1.a ^ us1_6[0].h2.a ^ us1_6[1].h1.a ^ us1_6[1].h2.a;
    }
    apply @noWarn("uninitialized_use") {
        u.h1.setInvalid();
        u.h2.setInvalid();
        hs[0].setInvalid();
        hs[1].setInvalid();
        us[0].h1.setInvalid();
        us[0].h2.setInvalid();
        us[1].h1.setInvalid();
        us[1].h2.setInvalid();
        u.h1.setValid();
        hs[0].setValid();
        us[0].h1.setValid();
        initialize_0(u, hs, us);
        u.h1.a = 32w1;
        u.h2.a = 32w1;
        hs[0].a = 32w1;
        hs[1].a = 32w1;
        us[0].h1.a = 32w1;
        us[0].h2.a = 32w1;
        inout_action1_0(u, hs, us);
        u.h1.a = 32w1;
        u.h2.a = 32w1;
        hs[0].a = 32w1;
        hs[1].a = 32w1;
        us[0].h1.a = 32w1;
        us[0].h2.a = 32w1;
        inout_action2_0(u, hs, us);
        xor_0(u, hs, us, x);
    }
}

top(c()) main;

