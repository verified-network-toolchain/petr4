control ingress(inout bit<8> h) {
    @name("ingress.a") action a() {
    }
    apply {
        a();
    }
}

control c<H>(inout H h);
package top<H>(c<H> c);
top<bit<8>>(ingress()) main;

