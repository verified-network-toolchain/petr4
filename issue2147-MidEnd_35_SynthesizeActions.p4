control ingress(inout bit<8> h) {
    @name("ingress.tmp") bit<7> tmp_0;
    @name("ingress.a") action a() {
        h[0:0] = 1w0;
    }
    @hidden action issue2147l6() {
        tmp_0 = h[7:1];
    }
    @hidden action issue2147l8() {
        h[7:1] = tmp_0;
    }
    apply {
        issue2147l6();
        a();
        issue2147l8();
    }
}

control c<H>(inout H h);
package top<H>(c<H> c);
top<bit<8>>(ingress()) main;

