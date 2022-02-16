control c(inout bit<32> x) {
    @name("a") action a_0(@name("b") inout bit<32> b_0, @name("d") bit<32> d_0) {
        b_0 = d_0;
    }
    @name("a") action a(@name("b") inout bit<32> b_0, @name("d") bit<32> d_0) {
        b_0 = d_0;
    }
    @name("t") table t_0 {
        actions = {
            a(x);
        }
        default_action = a(x, 32w0);
    }
    apply {
        t_0.apply();
    }
}

control proto(inout bit<32> x);
package top(proto p);
top(c()) main;

