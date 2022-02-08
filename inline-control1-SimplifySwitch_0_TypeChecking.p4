extern Y {
    Y(bit<32> b);
    bit<32> get();
}

control c(out bit<32> x)(Y y) {
    apply {
        x = y.get();
    }
}

control d(out bit<32> x) {
    @name("y") bit<32> y_0;
    @name("cinst") c(Y(32w16)) cinst_0;
    apply {
        y_0 = 32w5;
        cinst_0.apply(x);
        cinst_0.apply(y_0);
    }
}

control dproto(out bit<32> x);
package top(dproto _d);
top(d()) main;

