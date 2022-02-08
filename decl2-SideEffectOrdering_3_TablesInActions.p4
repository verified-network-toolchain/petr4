control p() {
    @name("z") bit<1> z_0;
    @name("x_0") bit<1> x_2;
    @name("x_1") bit<1> x_3;
    @name("y_0") bit<1> y_1;
    @name("b") action b_0(in bit<1> x, out bit<1> y) {
        {
            x_2 = x;
            z_0 = x & x_2;
            y = z_0;
        }
    }
    apply {
        x_3 = 1w0;
        b_0(x_3, y_1);
    }
}

control simple();
package m(simple pipe);
.m(.p()) main;

