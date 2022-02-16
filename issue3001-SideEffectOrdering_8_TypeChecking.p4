header H {
    bit<8> x;
}

H f() {
    @name("h") H h_0;
    h_0.setInvalid();
    return h_0;
}
control c() {
    H tmp;
    bool tmp_0;
    apply {
        {
            tmp = f();
            tmp_0 = tmp.isValid();
            if (tmp_0) {
                ;
            }
        }
    }
}

control C();
package top(C _c);
top(c()) main;

