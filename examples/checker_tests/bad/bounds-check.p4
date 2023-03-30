header hdr_t {
    bit<8> x
}
control C(hdr_t[2] h) {
    apply {
        h[2] = {0};
    }
}