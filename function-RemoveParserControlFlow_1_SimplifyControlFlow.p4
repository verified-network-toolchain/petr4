control c(out bit<16> b) {
    apply {
        {
            bit<16> left_0 = 16w10;
            bit<16> right_0 = 16w12;
            @name("hasReturned") bool hasReturned_0;
            @name("retval") bit<16> retval_0;
            hasReturned_0 = false;
            if (left_0 > right_0) {
                hasReturned_0 = true;
                retval_0 = left_0;
            }
            if (hasReturned_0) {
                ;
            } else {
                hasReturned_0 = true;
                retval_0 = right_0;
            }
            b = retval_0;
        }
    }
}

control ctr(out bit<16> b);
package top(ctr _c);
top(c()) main;

