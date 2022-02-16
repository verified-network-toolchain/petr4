control ingress(inout bit<8> h) {
    @name("tmp") bit<7> tmp_0;
    @name("a") action a_0(inout bit<7> b) {
        h[0:0] = 1w0;
    }
    apply {
        tmp_0 = h[7:1];
        a_0(tmp_0);
        h[7:1] = tmp_0;
    }
}

control c<H>(inout H h);
package top<H>(c<H> c);
top<bit<8>>(ingress()) main;

