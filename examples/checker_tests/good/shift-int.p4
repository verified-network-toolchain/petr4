void ignore(in T t) {
}
control C() {
    apply {
	ignore(10 >> 1);
    }
}
