control ingress(inout bit<8> h) {
    @name("tmp") bit<8> tmp;
    @name("a") action a_0(@name("b") inout bit<8> b_0) {
    }
    apply {
        tmp = h;
        a_0(tmp);
        h = tmp;
    }
}

control c<H>(inout H h);
package top<H>(c<H> c);
top<bit<8>>(ingress()) main;

