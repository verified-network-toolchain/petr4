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
    @name("u1") U u1;
    @name("hs1") H1[2] hs1;
    @name("us1") U[2] us1;
    @name("initialize") action initialize_0() {
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
        u = u1;
        hs = hs1;
        us = us1;
    }
    @name("u1") U u1_4;
    @name("hs1") H1[2] hs1_4;
    @name("us1") U[2] us1_4;
    @name("inout_action1") action inout_action1_0() {
        u1_4 = u;
        hs1_4 = hs;
        us1_4 = us;
        u1_4.h1.a = 32w1;
        u1_4.h2.a = 32w1;
        hs1_4[0].a = 32w1;
        hs1_4[1].a = 32w1;
        us1_4[0].h1.a = 32w1;
        us1_4[0].h2.a = 32w1;
        hs1_4[0].setInvalid();
        u1_4.h1.setValid();
        us1_4[0].h1.setValid();
        u = u1_4;
        hs = hs1_4;
        us = us1_4;
    }
    @name("u1") U u1_5;
    @name("hs1") H1[2] hs1_5;
    @name("us1") U[2] us1_5;
    @name("inout_action2") action inout_action2_0() {
        u1_5 = u;
        hs1_5 = hs;
        us1_5 = us;
        i = 1w1;
        us1_5[i].h1.setInvalid();
        us1_5[i].h2.setValid();
        u = u1_5;
        hs = hs1_5;
        us = us1_5;
    }
    @name("u1") U u1_6;
    @name("hs1") H1[2] hs1_6;
    @name("us1") U[2] us1_6;
    @name("result") bit<32> result;
    @name("xor") action xor_0() {
        u1_6 = u;
        hs1_6 = hs;
        us1_6 = us;
        result = u1_6.h1.a ^ u1_6.h2.a ^ hs1_6[0].a ^ hs1_6[1].a ^ us1_6[0].h1.a ^ us1_6[0].h2.a ^ us1_6[1].h1.a ^ us1_6[1].h2.a;
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
        initialize_0();
        u.h1.a = 32w1;
        u.h2.a = 32w1;
        hs[0].a = 32w1;
        hs[1].a = 32w1;
        us[0].h1.a = 32w1;
        us[0].h2.a = 32w1;
        inout_action1_0();
        u.h1.a = 32w1;
        u.h2.a = 32w1;
        hs[0].a = 32w1;
        hs[1].a = 32w1;
        us[0].h1.a = 32w1;
        us[0].h2.a = 32w1;
        inout_action2_0();
        xor_0();
    }
}

top(c()) main;

