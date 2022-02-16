control c() {
    @name("x") bit<32> x_0;
    @name("b") action b_0(out bit<32> arg) {
        arg = 32w2;
    }
    apply {
        b_0(x_0);
    }
}

control proto();
package top(proto p);
top(c()) main;

