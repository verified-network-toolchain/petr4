bit<32> min(in bit<32> a, in bit<32> b) {
    @name("hasReturned") bool hasReturned_0 = false;
    @name("retval") bit<32> retval_0;
    @name("tmp") bit<32> tmp_2;
    if (a > b) {
        tmp_2 = b;
    } else {
        tmp_2 = a;
    }
    {
        hasReturned_0 = true;
        retval_0 = tmp_2;
    }
    return retval_0;
}
control c(inout bit<32> x) {
    @name("tmp_0") bit<32> tmp_3;
    @name("tmp_1") bit<32> tmp_4;
    apply {
        tmp_3 = min(x, x + 32w1);
        tmp_4 = min(x, x + 32w4294967295);
        x = min(tmp_3, tmp_4);
    }
}

control ctr(inout bit<32> x);
package top(ctr _c);
top(c()) main;

