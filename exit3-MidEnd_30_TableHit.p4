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
    apply {
        hasExited = false;
        c = 32w2;
        t_0.apply();
        if (hasExited) {
            ;
        } else {
            c = 32w5;
        }
    }
}

control noop(out bit<32> c);
package p(noop _n);
p(ctrl()) main;

