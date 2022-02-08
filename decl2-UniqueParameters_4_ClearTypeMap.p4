control p() {
    @name("z") bit<1> z;
    @name("x_0") bit<1> x;
    @name("x_1") bit<1> x_1;
    @name("y_0") bit<1> y;
    @name("b") action b_0(@name("x") in bit<1> x_2, @name("y") out bit<1> y_1) {
        x = x_2;
        z = x_2 & x;
        y_1 = z;
    }
    apply {
        x_1 = 1w0;
        b_0(x_1, y);
    }
}

control simple();
package m(simple pipe);
.m(.p()) main;

