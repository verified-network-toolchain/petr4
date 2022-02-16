bit<16> max(in bit<16> left, in bit<16> right) {
    bool hasReturned = false;
    bit<16> retval;
    if (left > right) {
        hasReturned = true;
        retval = left;
    }
    if (!hasReturned) {
        {
            hasReturned = true;
            retval = right;
        }
    }
    return retval;
}
control c(out bit<16> b) {
    apply {
        b = max(16w10, 16w12);
    }
}

control ctr(out bit<16> b);
package top(ctr _c);
top(c()) main;

