control c() {
    @name("x") bit<32> x;
    @name("b") action b_0(@name("arg") out bit<32> arg) {
        arg = 32w2;
    }
    apply {
        b_0(x);
    }
}

control proto();
package top(proto p);
top(c()) main;

