control p() {
    @name("z") bit<1> z_0;
    @name("x_0") bit<1> x_2;
    @name("x_1") bit<1> x_3;
    @name("y_0") bit<1> y_1;
    @name("b") action b_0(@name("x") in bit<1> x_0, @name("y") out bit<1> y_0) {
        x_2 = x_0;
        z_0 = x_0 & x_2;
        y_0 = z_0;
    }
    @name("b") action b(@name("x") in bit<1> x_0, @name("y") out bit<1> y_0) {
        x_2 = x_0;
        z_0 = x_0 & x_2;
        y_0 = z_0;
    }
    apply {
        x_3 = 1w0;
        b(x_3, y_1);
    }
}

control simple();
package m(simple pipe);
.m(.p()) main;

