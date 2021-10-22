typedef bit<8> PortId;
control c(inout PortId p) {
    apply {
        p = p + 1;
    }
}

control d() {
    typedef bit<4> PortId;
    apply{
        c() ci;
        bit<8> x = 4;
        ci.apply(x);
    }
}
