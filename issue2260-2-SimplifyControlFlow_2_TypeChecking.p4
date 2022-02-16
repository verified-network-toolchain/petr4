control C();
package S(C c);
bit<8> f_0(bit<8> x) {
    return x;
}
control MyC() {
    @name("y") bit<8> y_0;
    apply {
    }
}

S(MyC()) main;

