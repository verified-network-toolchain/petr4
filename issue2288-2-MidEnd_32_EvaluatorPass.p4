struct Headers {
    bit<8> a;
    bit<8> b;
}

control ingress(inout Headers h) {
    apply {
        h.a = 8w3;
        h.a = 8w3;
    }
}

control c<T>(inout T d);
package top<T>(c<T> _c);
top<Headers>(ingress()) main;

