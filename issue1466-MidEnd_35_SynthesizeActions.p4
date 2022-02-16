header hdr {
    bit<1> g;
}

control A(inout hdr _hdr) {
    @hidden action issue1466l7() {
        _hdr.g = 1w1;
        _hdr.g = 1w1;
    }
    apply {
        issue1466l7();
    }
}

control proto(inout hdr _hdr);
package top(proto p);
top(A()) main;

