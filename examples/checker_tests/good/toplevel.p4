action x(inout bit<8> v) {
    v = 5;
}

control C() {
    action x(inout bool v) {
        v = false;
    }
    apply {
        bit<8> y = 0;
        .x(y);
        bool y = true;
        x(y);
    }
}
