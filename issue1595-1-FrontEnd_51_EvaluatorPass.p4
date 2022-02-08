control c(inout bit<32> b) {
    @name("a") action a_0() {
        b = 32w1;
    }
    @name("t") table t_0 {
        actions = {
            a_0();
        }
        default_action = a_0();
    }
    apply {
        switch (t_0.apply().action_run) {
            a_0: {
                b[6:3] = 4w1;
            }
        }
    }
}

control empty(inout bit<32> b);
package top(empty _e);
top(c()) main;

