control p(out bit<1> y) {
    @name("x") bit<1> x;
    @name("z") bit<1> z;
    @name("x") bit<1> x_3;
    @name("b") action b_0(@name("x") in bit<1> x_2, @name("y") out bit<1> y_0) {
        {
            @name("x0") bit<1> x0_0 = x_2;
            @name("y0") bit<1> y0_0;
            x = x0_0;
            y0_0 = x0_0 & x;
            z = y0_0;
        }
        {
            @name("x0") bit<1> x0_2 = z;
            @name("y0") bit<1> y0_2;
            x = x0_2;
            y0_2 = x0_2 & x;
            y_0 = y0_2;
        }
    }
    apply {
        x_3 = 1w1;
        b_0(x_3, y);
    }
}

control simple(out bit<1> y);
package m(simple pipe);
m(p()) main;

