extern Y {
    Y(bit<32> b);
    bit<32> get();
}

control d(out bit<32> x) {
    @name("y") bit<32> y;
    @name("x_0") bit<32> x_1;
    @name("cinst.y") Y(32w16) cinst_y_0;
    apply {
        {
            x_1 = cinst_y_0.get();
            x = x_1;
        }
        {
            x_1 = cinst_y_0.get();
            y = x_1;
        }
    }
}

control dproto(out bit<32> x);
package top(dproto _d);
top(d()) main;

