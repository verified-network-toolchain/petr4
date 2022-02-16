control c(inout bit<32> x) {
    @hidden action synthaction19() {
        x = 32w10;
        x = 32w12;
        x = 32w6;
    }
    apply {
        synthaction19();
    }
}

control n(inout bit<32> x);
package top(n _n);
top(c()) main;

