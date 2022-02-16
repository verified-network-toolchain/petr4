control c(inout bit<16> y) {
    @name("c.a") action a() {
        y = 16w10;
    }
    apply {
        a();
    }
}

control proto(inout bit<16> y);
package top(proto _p);
top(c()) main;

