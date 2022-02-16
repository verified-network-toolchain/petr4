header H {
    bit<32> x;
}

struct S {
    H h;
}

control c(out bool b);
package top(c _c);
control e(in H h, out bool valid) {
    apply {
        valid = h.isValid();
    }
}

control d(out bool b) {
    @name("einst") e() einst_0;
    apply {
        @name("h") H h_0;
        h_0.setInvalid();
        @name("h3") H[2] h3_0;
        h3_0[0].setInvalid();
        h3_0[1].setInvalid();
        h_0 = (H){x = 32w0};
        @name("s") S s_0;
        s_0.h.setInvalid();
        @name("s1") S s1_0;
        s1_0.h.setInvalid();
        s_0 = (S){h = (H){x = 32w0}};
        s1_0.h = (H){x = 32w0};
        h3_0[0] = (H){x = 32w0};
        h3_0[1] = (H){x = 32w1};
        @name("eout") bool eout_0;
        einst_0.apply((H){x = 32w0}, eout_0);
        b = h_0.isValid() && eout_0 && h3_0[1].isValid() && s1_0.h.isValid();
    }
}

top(d()) main;

