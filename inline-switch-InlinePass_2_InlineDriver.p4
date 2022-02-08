control c(out bit<32> x) {
    @name("a1") action a1_0() {
    }
    @name("a2") action a2_0() {
    }
    @name("t") table t_0 {
        actions = {
            a1_0();
            a2_0();
        }
        default_action = a1_0();
    }
    apply {
        bool hasReturned = false;
        switch (t_0.apply().action_run) {
            a1_0: 
            a2_0: {
                {
                    hasReturned = true;
                }
            }
            default: {
                {
                    hasReturned = true;
                }
            }
        }
        if (!hasReturned) {
        }
    }
}

control d(out bit<32> x) {
    @name("cinst") c() cinst_0;
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

