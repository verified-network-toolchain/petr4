control c() {
    @name("x") bit<32> x_0;
    @name("b") action b_0(@name("arg") out bit<32> arg_0) {
        arg_0 = 32w2;
    }
    @name("b") action b(@name("arg") out bit<32> arg_0) {
        arg_0 = 32w2;
    }
    apply {
        b(x_0);
    }
}

control proto();
package top(proto p);
top(c()) main;

