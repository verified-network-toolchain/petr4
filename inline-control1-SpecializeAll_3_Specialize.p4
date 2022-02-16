extern Y {
    Y(bit<32> b);
    bit<32> get();
}

control c(out bit<32> x)(Y y) {
    apply {
        x = y.get();
    }
}

control c_0(out bit<32> x) {
    Y(32w16) y_1;
    apply {
        x = y_1.get();
    }
}

control d(out bit<32> x) {
    @name("y") bit<32> y_0;
    @name("cinst") c_0() cinst_0;
    apply {
        cinst_0.apply(x);
        cinst_0.apply(y_0);
    }
}

control dproto(out bit<32> x);
package top(dproto _d);
top(d()) main;

