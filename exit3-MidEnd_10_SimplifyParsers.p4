control ctrl(out bit<32> c) {
    bool hasExited;
    @name("ctrl.a") bit<32> a_0;
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
        a_0 = 32w0;
        c = 32w2;
        if (a_0 == 32w0) {
            t_0.apply();
        } else {
            t_0.apply();
        }
        if (!hasExited) {
            c = 32w5;
        }
    }
}

control noop(out bit<32> c);
package p(noop _n);
p(ctrl()) main;

