struct tuple_0 {
    bit<32> f0;
    bit<16> f1;
}

control c(out bit<16> r) {
    @name("c.x") tuple_0 x_0;
    apply {
        {
            x_0.f0 = 32w10;
            x_0.f1 = 16w12;
        }
        if (x_0.f0 == 32w10 && x_0.f1 == 16w12) {
            r = x_0.f1;
        } else {
            r = (bit<16>)x_0.f0;
        }
    }
}

control _c(out bit<16> r);
package top(_c c);
top(c()) main;

