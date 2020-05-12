void foo<A>(in A a) {
    A x = a;
}

void bar<A>(in A l, in A r) {
    foo(l);
}
