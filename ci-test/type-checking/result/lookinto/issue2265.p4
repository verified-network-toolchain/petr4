/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2265.p4
\n
T f<T>(T data) {
    T tmp;
    tmp = data;
    return tmp;
}

control c<T>(inout T data) {
    apply {
        T tmp;
        data = tmp;
    }
}
************************\n******** petr4 type checking result: ********\n************************\n
