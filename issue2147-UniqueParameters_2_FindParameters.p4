control ingress(inout bit<8> h) {
    @name("tmp") bit<7> tmp;
    @name("a") action a_0(@name("b") inout bit<7> b_0) {
        h[0:0] = 1w0;
    }
    apply {
        tmp = h[7:1];
        a_0(tmp);
        h[7:1] = tmp;
    }
}

control c<H>(inout H h);
package top<H>(c<H> c);
top<bit<8>>(ingress()) main;

