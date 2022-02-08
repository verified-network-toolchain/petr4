control p(out bit<1> y) {
    @name("x") bit<1> x_0;
    @name("z") bit<1> z_0;
    @name("x") bit<1> x_1;
    @name("b") action b_0(@name("x") in bit<1> x_2, @name("y") out bit<1> y_0) {
        {
            @name("x0") bit<1> x0 = x_2;
            @name("y0") bit<1> y0;
            x_0 = x0;
            y0 = x0 & x_0;
            z_0 = y0;
        }
        {
            @name("x0") bit<1> x0_1 = z_0;
            @name("y0") bit<1> y0_1;
            x_0 = x0_1;
            y0_1 = x0_1 & x_0;
            y_0 = y0_1;
        }
    }
    @name("b") action b(@name("x") in bit<1> x_2, @name("y") out bit<1> y_0) {
        {
            @name("x0") bit<1> x0 = x_2;
            @name("y0") bit<1> y0;
            x_0 = x0;
            y0 = x0 & x_0;
            z_0 = y0;
        }
        {
            @name("x0") bit<1> x0_1 = z_0;
            @name("y0") bit<1> y0_1;
            x_0 = x0_1;
            y0_1 = x0_1 & x_0;
            y_0 = y0_1;
        }
    }
    apply {
        x_1 = 1w1;
        b(x_1, y);
    }
}

control simple(out bit<1> y);
package m(simple pipe);
m(p()) main;

