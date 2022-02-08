control ctrl(out bit<32> c) {
    @name("e") action e_0() {
        exit;
    }
    @name("t") table t_0 {
        actions = {
            e_0();
        }
        default_action = e_0();
    }
    apply {
        @name("a") bit<32> a_0;
        @name("b") bit<32> b_0;
        a_0 = 32w0;
        b_0 = 32w1;
        c = 32w2;
        if (a_0 == 32w0) {
            b_0 = 32w2;
            t_0.apply();
            c = 32w3;
        } else {
            b_0 = 32w3;
            t_0.apply();
            c = 32w4;
        }
        c = 32w5;
    }
}

control noop(out bit<32> c);
package p(noop _n);
p(ctrl()) main;

