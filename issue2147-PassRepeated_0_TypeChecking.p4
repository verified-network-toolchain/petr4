control ingress(inout bit<8> h) {
    @name("tmp") bit<7> tmp;
    @name("b") bit<7> b;
    @name("a") action a_0() {
        b = tmp;
        h[0:0] = 1w0;
        tmp = b;
    }
    apply {
        tmp = h[7:1];
        a_0();
        h[7:1] = tmp;
    }
}

control c<H>(inout H h);
package top<H>(c<H> c);
top<bit<8>>(ingress()) main;

