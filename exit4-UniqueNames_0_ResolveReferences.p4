control ctrl() {
    @name("e") action e_0() {
        exit;
    }
    @name("t") table t {
        actions = {
            e_0();
        }
        default_action = e_0();
    }
    apply {
        if (t.apply().hit) {
            t.apply();
        } else {
            t.apply();
        }
    }
}

control noop();
package p(noop _n);
p(ctrl()) main;

