control c(inout bit<8> v) {
    @name("hasReturned_0") bool hasReturned_2;
    apply {
        hasReturned_2 = false;
        {
            bit<8> val_0 = v;
            @name("hasReturned") bool hasReturned_1;
            hasReturned_1 = false;
            if (val_0 == 8w0) {
                val_0 = 8w1;
                hasReturned_1 = true;
            }
            if (hasReturned_1) {
                ;
            } else {
                val_0 = 8w2;
            }
            v = val_0;
        }
        if (v == 8w0) {
            v = 8w1;
            hasReturned_2 = true;
        }
        if (hasReturned_2) {
            ;
        } else {
            v = 8w2;
        }
    }
}

control e(inout bit<8> _v);
package top(e _e);
top(c()) main;

