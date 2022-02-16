control ingress(inout bit<8> h) {
    @name("a") action a_0(inout bit<8> b) {
    }
    apply {
        @name("tmp") bit<8> tmp_0 = h;
        a_0(tmp_0);
        h = tmp_0;
    }
}

control c<H>(inout H h);
package top<H>(c<H> c);
top<bit<8>>(ingress()) main;

