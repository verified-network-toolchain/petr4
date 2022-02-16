control c(inout bit<32> x) {
    @name("arg") bit<32> arg_1;
    @name("a") action a_0() {
        arg_1 = 32w10;
        x = arg_1;
    }
    @name("t") table t {
        actions = {
            a_0();
        }
        default_action = a_0();
    }
    apply {
        t.apply();
    }
}

control proto(inout bit<32> arg);
package top(proto p);
top(c()) main;

