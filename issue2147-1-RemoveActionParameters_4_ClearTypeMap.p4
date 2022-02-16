control ingress(inout bit<8> h) {
    @name("tmp") bit<8> tmp;
    @name("b") bit<8> b;
    @name("a") action a_0() {
        b = tmp;
        tmp = b;
    }
    apply {
        tmp = h;
        a_0();
        h = tmp;
    }
}

control c<H>(inout H h);
package top<H>(c<H> c);
top<bit<8>>(ingress()) main;

