header H {
    bit<32> x;
}

struct S {
    H h;
}

control c(out bool b);
package top(c _c);
control d(out bool b) {
    @name("h") H h_1;
    @name("h3") H[2] h3;
    @name("s") S s;
    @name("s1") S s1;
    @name("eout") bool eout;
    @name("tmp") H tmp_0;
    apply {
        h_1.setInvalid();
        h3[0].setInvalid();
        h3[1].setInvalid();
        h_1.setValid();
        h_1 = (H){x = 32w0};
        s.h.setInvalid();
        s1.h.setInvalid();
        s1.h.setValid();
        s1.h = (H){x = 32w0};
        h3[1].setValid();
        h3[1] = (H){x = 32w1};
        tmp_0.setValid();
        tmp_0 = (H){x = 32w0};
        eout = tmp_0.isValid();
        b = h_1.isValid() && eout && h3[1].isValid() && s1.h.isValid();
    }
}

top(d()) main;

