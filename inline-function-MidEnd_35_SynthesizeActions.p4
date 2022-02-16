control c(inout bit<32> x) {
    @name("c.tmp") bit<32> tmp_2;
    @hidden action inlinefunction2() {
        tmp_2 = x;
    }
    @hidden action inlinefunction2_0() {
        tmp_2 = x;
    }
    @hidden action inlinefunction11() {
        x = x + tmp_2;
    }
    apply {
        if (x > x) {
            inlinefunction2();
        } else {
            inlinefunction2_0();
        }
        inlinefunction11();
    }
}

control ctr(inout bit<32> x);
package top(ctr _c);
top(c()) main;

