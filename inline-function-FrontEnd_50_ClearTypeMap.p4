bit<32> min(in bit<32> a, in bit<32> b) {
    bool hasReturned = false;
    bit<32> retval;
    bit<32> tmp;
    if (a > b) {
        tmp = b;
    } else {
        tmp = a;
    }
    {
        hasReturned = true;
        retval = tmp;
    }
    return retval;
}
bit<32> fun(in bit<32> a, in bit<32> b) {
    bool hasReturned_0 = false;
    bit<32> retval_0;
    bit<32> tmp_0;
    bit<32> tmp_1;
    bit<32> tmp_2;
    tmp_0 = a;
    tmp_1 = min(a, b);
    tmp_2 = tmp_0 + tmp_1;
    {
        hasReturned_0 = true;
        retval_0 = tmp_2;
    }
    return retval_0;
}
control c(inout bit<32> x) {
    apply {
        x = fun(x, x);
    }
}

control ctr(inout bit<32> x);
package top(ctr _c);
top(c()) main;

