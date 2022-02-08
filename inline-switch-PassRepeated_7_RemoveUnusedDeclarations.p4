control d(out bit<32> x) {
    @name("cinst.a1") action cinst_a1() {
    }
    @name("cinst.a2") action cinst_a2() {
    }
    @name("cinst.t") table cinst_t {
        actions = {
            cinst_a1();
            cinst_a2();
        }
        default_action = cinst_a1();
    }
    apply {
        {
            @name("cinst.hasReturned") bool cinst_hasReturned = false;
            switch (cinst_t.apply().action_run) {
                cinst_a1: 
                cinst_a2: {
                    {
                        cinst_hasReturned = true;
                    }
                }
                default: {
                    {
                        cinst_hasReturned = true;
                    }
                }
            }
            if (!cinst_hasReturned) {
            }
        }
    }
}

control dproto(out bit<32> x);
package top(dproto _d);
top(d()) main;

