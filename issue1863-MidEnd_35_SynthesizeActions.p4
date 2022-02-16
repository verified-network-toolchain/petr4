struct S {
    bit<1> a;
    bit<1> b;
}

control c(out bit<1> b) {
    @hidden action issue1863l10() {
        b = 1w1;
    }
    apply {
        issue1863l10();
    }
}

control e<T>(out T t);
package top<T>(e<T> e);
top<bit<1>>(c()) main;

