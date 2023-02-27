void ignore<T>(in T t) {
    return;
}
control C() {
    const int c = 0;
    int<8> i = 0;
    bit<8> b = 0;
    apply {
	ignore(b ++ c);
    }
}