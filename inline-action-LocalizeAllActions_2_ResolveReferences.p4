control p(inout bit<1> bt) {
    @name("b") action b_0() {
        {
            @name("y0") bit<1> y0 = bt;
            y0 = y0 | 1w1;
            bt = y0;
        }
        {
            @name("y0") bit<1> y0_1 = bt;
            y0_1 = y0_1 | 1w1;
            bt = y0_1;
        }
    }
    @name("t") table t_0 {
        actions = {
            b_0();
        }
        default_action = b_0();
    }
    apply {
        t_0.apply();
    }
}

control simple<T>(inout T arg);
package m<T>(simple<T> pipe);
m<bit<1>>(p()) main;

