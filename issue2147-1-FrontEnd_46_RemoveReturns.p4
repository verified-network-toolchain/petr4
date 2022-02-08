control ingress(inout bit<8> h) {
    @name("tmp") bit<8> tmp_0;
    @name("a") action a_0(@name("b") inout bit<8> b_0) {
    }
    apply {
        tmp_0 = h;
        a_0(tmp_0);
        h = tmp_0;
    }
}

control c<H>(inout H h);
package top<H>(c<H> c);
top<bit<8>>(ingress()) main;

