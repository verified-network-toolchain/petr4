control C() {
    apply {
        int<8> x = ~8s1;
        x = 8s1 | 8s0;
        x = 8s1 & 8s0;
        x = 8s1 ^ 8s0;
        x = 8s1 ++ 8s0;
    }
}