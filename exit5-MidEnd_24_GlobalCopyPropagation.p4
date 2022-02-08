control ctrl() {
    bool hasExited;
    @name("ctrl.e") action e() {
        hasExited = true;
    }
    @name("ctrl.f") action f() {
    }
    @name("ctrl.t") table t_0 {
        actions = {
            e();
            f();
        }
        default_action = e();
    }
    apply {
        hasExited = false;
        switch (t_0.apply().action_run) {
            e: {
                if (!hasExited) {
                    t_0.apply();
                    if (!hasExited) {
                    }
                }
            }
            f: {
                if (!hasExited) {
                    t_0.apply();
                    if (!hasExited) {
                    }
                }
            }
        }
        if (!hasExited) {
        }
    }
}

control noop();
package p(noop _n);
p(ctrl()) main;

