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
    e() einst;
    apply {
        H h;
        h.setInvalid();
        H[2] h3;
        h3[0].setInvalid();
        h3[1].setInvalid();
        h = (H){x = 32w0};
        S s;
        s.h.setInvalid();
        S s1;
        s1.h.setInvalid();
        s = (S){h = (H){x = 32w0}};
        s1.h = (H){x = 32w0};
        h3[0] = (H){x = 32w0};
        h3[1] = (H){x = 32w1};
        bool eout;
        einst.apply((H){x = 32w0}, eout);
        b = h.isValid() && eout && h3[1].isValid() && s1.h.isValid();
    }
}

top(d()) main;

