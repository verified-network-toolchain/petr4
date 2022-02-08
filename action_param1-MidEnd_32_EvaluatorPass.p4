control c(inout bit<32> x) {
    @name("c.a") action a() {
        x = 32w15;
    }
    apply {
        a();
    }
}

control proto(inout bit<32> arg);
package top(proto p);
top(c()) main;

