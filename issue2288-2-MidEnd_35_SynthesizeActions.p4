struct Headers {
    bit<8> a;
    bit<8> b;
}

control ingress(inout Headers h) {
    @hidden action act() {
        h.a = 8w3;
        h.a = 8w3;
    }
    apply {
        act();
    }
}

control c<T>(inout T d);
package top<T>(c<T> _c);
top<Headers>(ingress()) main;

