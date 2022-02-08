control c(out bit<16> b) {
    apply {
        {
            @name("left_0") bit<16> left = 16w10;
            @name("right_0") bit<16> right = 16w12;
            @name("hasReturned") bool hasReturned;
            @name("retval") bit<16> retval;
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

