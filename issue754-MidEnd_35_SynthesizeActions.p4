control ctrl(out bit<3> _x);
package top(ctrl c);
control c_0(out bit<3> x) {
    @hidden action issue754l1() {
        x = 3w1;
    }
    apply {
        issue754l1();
    }
}

top(c_0()) main;

