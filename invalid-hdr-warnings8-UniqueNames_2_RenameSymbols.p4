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
    @name("u") U u_0;
    @name("hs") H1[2] hs_0;
    @name("us") U[2] us_0;
    @name("i") bit<1> i_0;
    @name("u1") U u1_2;
    @name("hs1") H1[2] hs1_2;
    @name("us1") U[2] us1_2;
    @name("u1") U u1_3;
    @name("hs1") H1[2] hs1_3;
    @name("us1") U[2] us1_3;
    @name("u1") U u1_5;
    @name("hs1") H1[2] hs1_5;
    @name("us1") U[2] us1_5;
    @name("inout_action2") action inout_action2() {
        u1_5 = u_0;
        hs1_5 = hs_0;
        us1_5 = us_0;
        u1_2 = u1_5;
        hs1_2 = hs1_5;
        us1_2 = us1_5;
        u1_3.h1.a = 32w1;
        u1_3.h2.a = 32w1;
        hs1_3[0].a = 32w1;
        hs1_3[1].a = 32w1;
        us1_3[0].h1.a = 32w1;
        us1_3[0].h2.a = 32w1;
        u1_3.h1.setValid();
        u1_3.h2.setValid();
        hs1_3[0].setValid();
        hs1_3[1].setValid();
        us1_3[0].h1.setValid();
        us1_3[0].h2.setValid();
        u1_2 = u1_3;
        hs1_2 = hs1_3;
        us1_2 = us1_3;
        u1_2.h1.a = 32w1;
        u1_2.h2.a = 32w1;
        hs1_2[0].a = 32w1;
        hs1_2[1].a = 32w1;
        us1_2[0].h1.a = 32w1;
        us1_2[0].h2.a = 32w1;
        hs1_2[0].setInvalid();
        u1_2.h1.setValid();
        us1_2[0].h1.setValid();
        u1_5 = u1_2;
        hs1_5 = hs1_2;
        us1_5 = us1_2;
        u1_5.h1.a = 32w1;
        u1_5.h2.a = 32w1;
        hs1_5[0].a = 32w1;
        hs1_5[1].a = 32w1;
        us1_5[0].h1.a = 32w1;
        us1_5[0].h2.a = 32w1;
        i_0 = 1w1;
        us1_5[i_0].h1.setInvalid();
        us1_5[i_0].h2.setValid();
        u_0 = u1_5;
        hs_0 = hs1_5;
        us_0 = us1_5;
    }
    @name("u1") U u1_6;
    @name("hs1") H1[2] hs1_6;
    @name("us1") U[2] us1_6;
    @name("result") bit<32> result_0;
    @name("xor") action xor() {
        u1_6 = u_0;
        hs1_6 = hs_0;
        us1_6 = us_0;
        result_0 = u1_6.h1.a ^ u1_6.h2.a ^ hs1_6[0].a ^ hs1_6[1].a ^ us1_6[0].h1.a ^ us1_6[0].h2.a ^ us1_6[1].h1.a ^ us1_6[1].h2.a;
        x = result_0;
    }
    apply @noWarn("uninitialized_use") {
        u_0.h1.setInvalid();
        u_0.h2.setInvalid();
        hs_0[0].setInvalid();
        hs_0[1].setInvalid();
        us_0[0].h1.setInvalid();
        us_0[0].h2.setInvalid();
        us_0[1].h1.setInvalid();
        us_0[1].h2.setInvalid();
        u_0.h1.setValid();
        hs_0[0].setValid();
        us_0[0].h1.setValid();
        inout_action2();
        xor();
    }
}

top(c()) main;

