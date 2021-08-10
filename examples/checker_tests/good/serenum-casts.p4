enum bit<8> E1 {
   e1 = 0, e2 = 1, e3 = 2
}
enum bit<8> E2 {
   e1 = 10, e2 = 11, e3 = 12
}
control C() {
    apply {
        E1 a = (E1) (E2.e1 + E2.e2);
        bool b = (E2.e1 > E2.e2);
        bit<8> x = a << 3;
    }
}