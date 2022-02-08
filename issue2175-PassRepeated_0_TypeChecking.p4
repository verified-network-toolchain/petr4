void do_something(inout bit<8> val) {
    @name("hasReturned") bool hasReturned_1;
    hasReturned_1 = false;
    if (val == 8w0) {
        val = 8w1;
        {
            hasReturned_1 = true;
        }
    }
    if (!hasReturned_1) {
        val = 8w2;
    }
}
control c(inout bit<8> v) {
    @name("hasReturned_0") bool hasReturned_2;
    apply {
        hasReturned_2 = false;
        do_something(v);
        if (v == 8w0) {
            v = 8w1;
            {
                hasReturned_2 = true;
            }
        }
        if (!hasReturned_2) {
            v = 8w2;
        }
    }
}

control e(inout bit<8> _v);
package top(e _e);
top(c()) main;

