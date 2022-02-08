bit<8> test1(inout bit<8> x) {
    bool hasReturned = false;
    bit<8> retval;
    {
        hasReturned = true;
        retval = x;
    }
    return retval;
}
bit<8> test2(inout bit<8> x) {
    bool hasReturned_0 = false;
    bit<8> retval_0;
    {
        hasReturned_0 = true;
        retval_0 = x;
    }
    return retval_0;
}
control c(inout bit<8> a) {
    apply {
        test1(a);
        test2(a);
    }
}

control E(inout bit<8> t);
package top(E e);
top(c()) main;

