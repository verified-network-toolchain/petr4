T foo<T>(in T x) {
    return x;
}

U bar<U>(in U x) {
    // Does not work because U is parsed as a nonTypeName
    return foo<U>(x);

    // Does work
    // return foo<_>(x);
}
