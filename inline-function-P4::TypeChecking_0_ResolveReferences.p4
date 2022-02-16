control c(inout bit<32> x) {
    @name("a_1") bit<32> a;
    @name("b_1") bit<32> b;
    @name("hasReturned_0") bool hasReturned;
    @name("retval_0") bit<32> retval;
    @name("tmp_0") bit<32> tmp;
    @name("tmp_1") bit<32> tmp_0;
    @name("tmp_2") bit<32> tmp_1;
    @name("a_0") bit<32> a_2;
    @name("b_0") bit<32> b_2;
    @name("hasReturned") bool hasReturned_0;
    @name("retval") bit<32> retval_0;
    @name("tmp") bit<32> tmp_2;
    apply {
        {
            a = x;
            b = x;
            hasReturned = false;
            tmp = a;
            {
                a_2 = a;
                b_2 = b;
                hasReturned_0 = false;
                if (a_2 > b_2) {
                    tmp_2 = b_2;
                } else {
                    tmp_2 = a_2;
                }
                hasReturned_0 = true;
                retval_0 = tmp_2;
                tmp_0 = retval_0;
            }
            tmp_1 = tmp + tmp_0;
            hasReturned = true;
            retval = tmp_1;
            x = retval;
        }
    }
}

control ctr(inout bit<32> x);
package top(ctr _c);
top(c()) main;

