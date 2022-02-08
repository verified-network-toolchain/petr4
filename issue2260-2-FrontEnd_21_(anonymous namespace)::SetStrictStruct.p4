control C();
package S(C c);
T f<T>(T x) {
    return x;
}
control MyC() {
    apply {
        bit<8> y = f<bit<8>>(8w255);
    }
}

S(MyC()) main;

