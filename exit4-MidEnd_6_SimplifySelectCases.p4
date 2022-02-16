control ctrl() {
    bool hasExited;
    @name("ctrl.e") action e() {
        hasExited = true;
    }
    @name("ctrl.t") table t_0 {
        actions = {
            e();
        }
        default_action = e();
    }
    apply {
        hasExited = false;
        if (t_0.apply().hit) {
            if (!hasExited) {
                t_0.apply();
            }
        } else if (!hasExited) {
            t_0.apply();
        }
        if (!hasExited) {
        }
    }
}

control noop();
package p(noop _n);
p(ctrl()) main;

