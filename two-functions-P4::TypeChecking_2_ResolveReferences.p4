control c(inout bit<8> a) {
    @name("x_0") bit<8> x;
    @name("hasReturned") bool hasReturned;
    @name("retval") bit<8> retval;
    @name("x_1") bit<8> x_2;
    @name("hasReturned_0") bool hasReturned_0;
    @name("retval_0") bit<8> retval_0;
    apply {
        x = a;
        hasReturned = false;
        hasReturned = true;
        retval = x;
        a = x;
        x_2 = a;
        hasReturned_0 = false;
        hasReturned_0 = true;
        retval_0 = x_2;
        a = x_2;
    }
}

control E(inout bit<8> t);
package top(E e);
top(c()) main;

