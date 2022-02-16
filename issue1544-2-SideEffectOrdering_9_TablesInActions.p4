bit<32> min(in bit<32> a, in bit<32> b) {
    bit<32> tmp;
    {
        if (a > b) {
            tmp = b;
        } else {
            tmp = a;
        }
        return tmp;
    }
}
control c(inout bit<32> x) {
    bit<32> tmp_0;
    bit<32> tmp_1;
    apply {
        {
            tmp_0 = min(x, x + 32w1);
            tmp_1 = min(x, x + 32w4294967295);
            x = min(tmp_0, tmp_1);
        }
    }
}

control ctr(inout bit<32> x);
package top(ctr _c);
top(c()) main;

