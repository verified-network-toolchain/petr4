control c(out bit<16> b) {
    @name("left_0") bit<16> left;
    @name("right_0") bit<16> right;
    @name("hasReturned") bool hasReturned;
    @name("retval") bit<16> retval;
    apply {
        {
            left = 16w10;
            right = 16w12;
            hasReturned = false;
            if (left > right) {
                hasReturned = true;
                retval = left;
            }
            if (hasReturned) {
                ;
            } else {
                hasReturned = true;
                retval = right;
            }
            b = retval;
        }
    }
}

control ctr(out bit<16> b);
package top(ctr _c);
top(c()) main;

