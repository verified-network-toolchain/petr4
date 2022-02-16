extern Y {
    Y(bit<32> b);
    bit<32> get();
}

control c_0(out bit<32> x) {
    Y(32w16) y_0;
    apply {
        x = y_0.get();
    }
}

control d(out bit<32> x) {
    @name("cinst") c_0() cinst_0;
    @name("cinst.y") Y(32w16) cinst_y;
    apply {
        {
            x = cinst_y.get();
        }
    }
}

control dproto(out bit<32> x);
package top(dproto _d);
top(d()) main;

