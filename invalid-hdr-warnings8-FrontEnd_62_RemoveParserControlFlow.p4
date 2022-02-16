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
    @name("u1") U u1_0;
    @name("hs1") H1[2] hs1_0;
    @name("us1") U[2] us1_0;
    @name("u1") U u1_1;
    @name("hs1") H1[2] hs1_1;
    @name("us1") U[2] us1_1;
    @name("u1") U u1;
    @name("hs1") H1[2] hs1;
    @name("us1") U[2] us1;
    @name("inout_action2") action inout_action2_0() {
        u1 = u;
        hs1 = hs;
        us1 = us;
        u1_0 = u1;
        hs1_0 = hs1;
        us1_0 = us1;
        u1_1.h1.a = 32w1;
        u1_1.h2.a = 32w1;
        hs1_1[0].a = 32w1;
        hs1_1[1].a = 32w1;
        us1_1[0].h1.a = 32w1;
        us1_1[0].h2.a = 32w1;
        u1_1.h1.setValid();
        u1_1.h2.setValid();
        hs1_1[0].setValid();
        hs1_1[1].setValid();
        us1_1[0].h1.setValid();
        us1_1[0].h2.setValid();
        u1_0 = u1_1;
        hs1_0 = hs1_1;
        us1_0 = us1_1;
        u1_0.h1.a = 32w1;
        u1_0.h2.a = 32w1;
        hs1_0[0].a = 32w1;
        hs1_0[1].a = 32w1;
        us1_0[0].h1.a = 32w1;
        us1_0[0].h2.a = 32w1;
        hs1_0[0].setInvalid();
        u1_0.h1.setValid();
        us1_0[0].h1.setValid();
        u1 = u1_0;
        hs1 = hs1_0;
        us1 = us1_0;
        u1.h1.a = 32w1;
        u1.h2.a = 32w1;
        hs1[0].a = 32w1;
        hs1[1].a = 32w1;
        us1[0].h1.a = 32w1;
        us1[0].h2.a = 32w1;
        i = 1w1;
        us1[i].h1.setInvalid();
        us1[i].h2.setValid();
        u = u1;
        hs = hs1;
        us = us1;
    }
    @name("u1") U u1_4;
    @name("hs1") H1[2] hs1_4;
    @name("us1") U[2] us1_4;
    @name("result") bit<32> result;
    @name("xor") action xor_0() {
        u1_4 = u;
        hs1_4 = hs;
        us1_4 = us;
        result = u1_4.h1.a ^ u1_4.h2.a ^ hs1_4[0].a ^ hs1_4[1].a ^ us1_4[0].h1.a ^ us1_4[0].h2.a ^ us1_4[1].h1.a ^ us1_4[1].h2.a;
        x = result;
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
        inout_action2_0();
        xor_0();
    }
}

top(c()) main;

