bit<8> test1(inout bit<8> x) {
    @name("hasReturned") bool hasReturned_1;
    @name("retval") bit<8> retval_1;
    hasReturned_1 = false;
    {
        hasReturned_1 = true;
        retval_1 = x;
    }
    return retval_1;
}
bit<8> test2(inout bit<8> x) {
    @name("hasReturned_0") bool hasReturned_2;
    @name("retval_0") bit<8> retval_2;
    hasReturned_2 = false;
    {
        hasReturned_2 = true;
        retval_2 = x;
    }
    return retval_2;
}
control c(inout bit<8> a) {
    apply {
        {
            bit<8> x_0 = a;
            @name("hasReturned") bool hasReturned_1;
            @name("retval") bit<8> retval_1;
            hasReturned_1 = false;
            {
                hasReturned_1 = true;
                retval_1 = x_0;
            }
            a = x_0;
        }
        {
            bit<8> x_1 = a;
            @name("hasReturned_0") bool hasReturned_2;
            @name("retval_0") bit<8> retval_2;
            hasReturned_2 = false;
            {
                hasReturned_2 = true;
                retval_2 = x_1;
            }
            a = x_1;
        }
    }
}

control E(inout bit<8> t);
package top(E e);
top(c()) main;

