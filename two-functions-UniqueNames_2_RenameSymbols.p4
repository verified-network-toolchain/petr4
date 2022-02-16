control c(inout bit<8> a) {
    apply {
        {
            @name("x_0") bit<8> x = a;
            @name("hasReturned") bool hasReturned;
            @name("retval") bit<8> retval;
            hasReturned = false;
            hasReturned = true;
            retval = x;
            a = x;
        }
        {
            @name("x_1") bit<8> x_2 = a;
            @name("hasReturned_0") bool hasReturned_0;
            @name("retval_0") bit<8> retval_0;
            hasReturned_0 = false;
            hasReturned_0 = true;
            retval_0 = x_2;
            a = x_2;
        }
    }
}

control E(inout bit<8> t);
package top(E e);
top(c()) main;

