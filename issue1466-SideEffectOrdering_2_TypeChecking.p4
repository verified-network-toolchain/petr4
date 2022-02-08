header hdr {
    bit<1> g;
}

control B(inout hdr _hdr, bit<1> _x) {
    apply {
        _hdr.g = _x;
    }
}

control A(inout hdr _hdr) {
    @name("b_inst") B() b_inst_0;
    apply {
        b_inst_0.apply(_hdr, 1w1);
        b_inst_0.apply(_hdr, 1w1);
    }
}

control proto(inout hdr _hdr);
package top(proto p);
top(A()) main;

