control c(out bit<32> x);
package top(c _c);
control my(out bit<32> x) {
    @hidden action overwrite24() {
        x = 32w2;
    }
    apply {
        overwrite24();
    }
}

top(my()) main;

