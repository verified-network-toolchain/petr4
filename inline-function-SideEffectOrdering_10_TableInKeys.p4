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
bit<32> fun(in bit<32> a, in bit<32> b) {
    bit<32> tmp_0;
    bit<32> tmp_1;
    bit<32> tmp_2;
    {
        tmp_0 = a;
        tmp_1 = min(a, b);
        tmp_2 = tmp_0 + tmp_1;
        return tmp_2;
    }
}
control c(inout bit<32> x) {
    apply {
        x = fun(x, x);
    }
}

control ctr(inout bit<32> x);
package top(ctr _c);
top(c()) main;

