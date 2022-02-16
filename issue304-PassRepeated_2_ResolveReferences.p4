control c(inout bit<32> y) {
    apply {
        y = y + 32w1;
    }
}

control t(inout bit<32> b) {
    apply {
        {
            b = b + 32w1;
        }
        {
            b = b + 32w1;
        }
    }
}

control cs(inout bit<32> arg);
package top(cs _ctrl);
top(t()) main;

