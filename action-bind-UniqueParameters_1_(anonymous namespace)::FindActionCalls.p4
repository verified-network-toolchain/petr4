control c(inout bit<32> x) {
    @name("a") action a_0(@name("b") inout bit<32> b_0, @name("d") bit<32> d_0) {
        b_0 = d_0;
    }
    @name("t") table t {
        actions = {
            a_0(x);
        }
        default_action = a_0(x, 32w0);
    }
    apply {
        t.apply();
    }
}

control proto(inout bit<32> x);
package top(proto p);
top(c()) main;

