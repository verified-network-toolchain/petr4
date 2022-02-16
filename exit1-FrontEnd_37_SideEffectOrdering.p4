control ctrl() {
    @name("a") bit<32> a_0;
    @name("b") bit<32> b_0;
    @name("c") bit<32> c_0;
    apply {
        a_0 = 32w0;
        b_0 = 32w1;
        c_0 = 32w2;
        if (a_0 == 32w0) {
            b_0 = 32w2;
            exit;
            c_0 = 32w3;
        } else {
            b_0 = 32w3;
            exit;
            c_0 = 32w4;
        }
        c_0 = 32w5;
    }
}

control noop();
package p(noop _n);
p(ctrl()) main;

