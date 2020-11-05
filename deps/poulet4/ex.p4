void f<T>(in T x = 8w10) {
}
control C() {
  apply {
    f(8s8);
    f();
  }
}
