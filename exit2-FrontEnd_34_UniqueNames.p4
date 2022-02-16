control ctrl(out bit<32> c) {
    @name("x") bit<32> x_0;
    @name("e") action e_0() {
        exit;
        x_0 = 32w1;
    }
    apply {
        @name("a") bit<32> a_0;
        @name("b") bit<32> b_0;
        a_0 = 32w0;
        b_0 = 32w1;
        c = 32w2;
        if (a_0 == 32w0) {
            b_0 = 32w2;
            e_0();
            c = 32w3;
        } else {
            b_0 = 32w3;
            e_0();
            c = 32w4;
        }
        c = 32w5;
    }
}

control noop(out bit<32> c);
package p(noop _n);
p(ctrl()) main;

