void foo<A>(in A a) {
    A x = a;
}

void bar<B>(in B l, in B r) {
    foo(l);
}

