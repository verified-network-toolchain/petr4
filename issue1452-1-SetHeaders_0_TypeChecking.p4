control c() {
    @name("x") bit<32> x;
    @name("arg") bit<32> arg;
    @name("b") action b_0() {
        arg = 32w2;
        x = arg;
    }
    apply {
        b_0();
    }
}

control proto();
package top(proto p);
top(c()) main;

