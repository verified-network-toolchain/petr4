header H {
    bit<32> x;
}

struct S {
    H h;
}

control c(out bool b);
package top(c _c);
control d(out bool b) {
    @name("h") H h_0;
    @name("h3") H[2] h3_0;
    @name("s") S s_0;
    @name("s1") S s1_0;
    @name("eout") bool eout_0;
    H tmp;
    apply {
        h_0.setInvalid();
        h3_0[0].setInvalid();
        h3_0[1].setInvalid();
        h_0 = (H){x = 32w0};
        s_0.h.setInvalid();
        s1_0.h.setInvalid();
        s1_0.h = (H){x = 32w0};
        h3_0[1] = (H){x = 32w1};
        tmp = (H){x = 32w0};
        {
            eout_0 = tmp.isValid();
        }
        b = h_0.isValid() && eout_0 && h3_0[1].isValid() && s1_0.h.isValid();
    }
}

top(d()) main;

