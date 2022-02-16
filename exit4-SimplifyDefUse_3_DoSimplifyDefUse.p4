control ctrl() {
    @name("a") bit<32> a_0;
    @name("b") bit<32> b_0;
    @name("c") bit<32> c_0;
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
        ;
        ;
        ;
        if (t_0.apply().hit) {
            ;
            t_0.apply();
            ;
        } else {
            ;
            t_0.apply();
            ;
        }
        ;
    }
}

control noop();
package p(noop _n);
p(ctrl()) main;

