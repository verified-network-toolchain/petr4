control c(inout bit<32> x) {
    @name("c.tmp") bit<32> tmp_2;
    apply {
        if (x > x) {
            tmp_2 = x;
        } else {
            tmp_2 = x;
        }
        x = x + tmp_2;
    }
}

control ctr(inout bit<32> x);
package top(ctr _c);
top(c()) main;

