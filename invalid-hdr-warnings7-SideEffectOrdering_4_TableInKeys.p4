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
    @name("initialize") action initialize_0(out U u1, out H1[2] hs1, out U[2] us1) {
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
    @name("inout_action1") action inout_action1_0(inout U u1, inout H1[2] hs1, inout U[2] us1) {
        u1.h1.a = 32w1;
        u1.h2.a = 32w1;
        hs1[0].a = 32w1;
        hs1[1].a = 32w1;
        us1[0].h1.a = 32w1;
        us1[0].h2.a = 32w1;
        hs1[0].setInvalid();
        u1.h1.setValid();
        us1[0].h1.setValid();
    }
    @name("inout_action2") action inout_action2_0(inout U u1, inout H1[2] hs1, inout U[2] us1) {
        i_0 = 1w1;
        us1[i_0].h1.setInvalid();
        us1[i_0].h2.setValid();
    }
    @name("xor") action xor_0(in U u1, in H1[2] hs1, in U[2] us1, out bit<32> result) {
        result = u1.h1.a ^ u1.h2.a ^ hs1[0].a ^ hs1[1].a ^ us1[0].h1.a ^ us1[0].h2.a ^ us1[1].h1.a ^ us1[1].h2.a;
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
        initialize_0(u_0, hs_0, us_0);
        u_0.h1.a = 32w1;
        u_0.h2.a = 32w1;
        hs_0[0].a = 32w1;
        hs_0[1].a = 32w1;
        us_0[0].h1.a = 32w1;
        us_0[0].h2.a = 32w1;
        inout_action1_0(u_0, hs_0, us_0);
        u_0.h1.a = 32w1;
        u_0.h2.a = 32w1;
        hs_0[0].a = 32w1;
        hs_0[1].a = 32w1;
        us_0[0].h1.a = 32w1;
        us_0[0].h2.a = 32w1;
        inout_action2_0(u_0, hs_0, us_0);
        xor_0(u_0, hs_0, us_0, x);
    }
}

top(c()) main;

