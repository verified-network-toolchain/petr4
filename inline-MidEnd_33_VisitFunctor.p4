control p(out bit<1> y) {
    @name("p.b") action b() {
        y = 1w1;
    }
    apply {
        b();
    }
}

control simple(out bit<1> y);
package m(simple pipe);
m(p()) main;

