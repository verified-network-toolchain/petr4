void do_something(inout bit<8> val) {
    bool hasReturned = false;
    if (val == 8w0) {
        val = 8w1;
        {
            hasReturned = true;
        }
    }
    if (!hasReturned) {
        val = 8w2;
    }
}
control c(inout bit<8> v) {
    apply {
        bool hasReturned_0 = false;
        do_something(v);
        if (v == 8w0) {
            v = 8w1;
            {
                hasReturned_0 = true;
            }
        }
        if (!hasReturned_0) {
            v = 8w2;
        }
    }
}

control e(inout bit<8> _v);
package top(e _e);
top(c()) main;

