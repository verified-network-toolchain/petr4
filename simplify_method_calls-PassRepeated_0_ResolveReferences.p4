header hdr {
    bit<32> a;
}

control ct(out bit<32> x, out bit<32> y);
package top(ct _ct);
bit<32> f(out bit<32> a) {
    @name("hasReturned") bool hasReturned_1;
    @name("retval") bit<32> retval_1;
    hasReturned_1 = false;
    a = 32w0;
    {
        hasReturned_1 = true;
        retval_1 = a;
    }
    return retval_1;
}
bit<32> g(in bit<32> a) {
    @name("hasReturned_0") bool hasReturned_2;
    @name("retval_0") bit<32> retval_2;
    hasReturned_2 = false;
    {
        hasReturned_2 = true;
        retval_2 = a;
    }
    return retval_2;
}
control c(out bit<32> x, out bit<32> y) {
    @name("h") hdr h;
    @name("b") bool b;
    @name("simple_action") action simple_action_0() {
        {
            bit<32> a_0 = x;
            @name("hasReturned_0") bool hasReturned_2;
            @name("retval_0") bit<32> retval_2;
            hasReturned_2 = false;
            {
                hasReturned_2 = true;
                retval_2 = a_0;
            }
            y = retval_2;
        }
        {
            bit<32> a_1;
            @name("hasReturned") bool hasReturned_1;
            @name("retval") bit<32> retval_1;
            hasReturned_1 = false;
            a_1 = 32w0;
            {
                hasReturned_1 = true;
                retval_1 = a_1;
            }
            x = a_1;
        }
    }
    apply {
        h = (hdr){a = 32w0};
        b = h.isValid();
        h.setValid();
        if (b) {
            x = h.a;
            {
                bit<32> a_2;
                @name("hasReturned") bool hasReturned_1;
                @name("retval") bit<32> retval_1;
                hasReturned_1 = false;
                a_2 = 32w0;
                {
                    hasReturned_1 = true;
                    retval_1 = a_2;
                }
                h.a = a_2;
            }
            {
                bit<32> a_3;
                @name("hasReturned") bool hasReturned_1;
                @name("retval") bit<32> retval_1;
                hasReturned_1 = false;
                a_3 = 32w0;
                {
                    hasReturned_1 = true;
                    retval_1 = a_3;
                }
                h.a = a_3;
            }
        } else {
            {
                bit<32> a_4;
                @name("hasReturned") bool hasReturned_1;
                @name("retval") bit<32> retval_1;
                hasReturned_1 = false;
                a_4 = 32w0;
                {
                    hasReturned_1 = true;
                    retval_1 = a_4;
                }
                h.a = a_4;
                x = retval_1;
            }
            {
                bit<32> a_5 = h.a;
                @name("hasReturned_0") bool hasReturned_2;
                @name("retval_0") bit<32> retval_2;
                hasReturned_2 = false;
                {
                    hasReturned_2 = true;
                    retval_2 = a_5;
                }
                x = retval_2;
            }
            {
                bit<32> a_6;
                @name("hasReturned") bool hasReturned_1;
                @name("retval") bit<32> retval_1;
                hasReturned_1 = false;
                a_6 = 32w0;
                {
                    hasReturned_1 = true;
                    retval_1 = a_6;
                }
                h.a = a_6;
            }
        }
        simple_action_0();
    }
}

top(c()) main;

