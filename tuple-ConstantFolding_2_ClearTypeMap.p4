struct S {
    bit<32> f;
    bool    s;
}

control proto();
package top(proto _p);
control c() {
    @name("x") tuple<bit<32>, bool> x_0;
    @name("y") tuple<bit<32>, bool> y_0;
    apply {
    }
}

top(c()) main;

