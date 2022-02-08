control c() {
    @name("x") bit<32> x_0;
    @name("arg") bit<32> arg_0;
    @name("b") action b() {
        arg_0 = 32w2;
        x_0 = arg_0;
    }
    apply {
        b();
    }
}

control proto();
package top(proto p);
top(c()) main;

