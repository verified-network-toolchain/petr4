control c(inout bit<32> x) {
    apply {
        x = 32w10;
        {
            x = 32w12;
            x = 32w6;
        }
    }
}

control n(inout bit<32> x);
package top(n _n);
top(c()) main;

