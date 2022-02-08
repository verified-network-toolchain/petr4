struct S {
    bit<1> a;
    bit<1> b;
}

control c(out bit<1> b) {
    apply {
        b = 1w1;
    }
}

control e<T>(out T t);
package top<T>(e<T> e);
top<bit<1>>(c()) main;

