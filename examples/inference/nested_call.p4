void foo<A, B, C>(in A a, in B b, in C c) {
}

void bar<A, B>(in A l, in B b, in A r) {
    foo<_, _, _>(l, b, r);
}

void baz<T>(in T a, in T b, in T c) {
    bar<_, _>(a, b, c);
}

void main() {
    baz<_>(true, true, true);
}
