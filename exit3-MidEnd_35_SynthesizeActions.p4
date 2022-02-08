control ctrl(out bit<32> c) {
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
    @hidden action exit3l33() {
        hasExited = false;
        c = 32w2;
    }
    @hidden action exit3l43() {
        c = 32w5;
    }
    apply {
        exit3l33();
        t_0.apply();
        if (hasExited) {
            ;
        } else {
            exit3l43();
        }
    }
}

control noop(out bit<32> c);
package p(noop _n);
p(ctrl()) main;

