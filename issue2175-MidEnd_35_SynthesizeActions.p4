control c(inout bit<8> v) {
    @name("c.hasReturned_0") bool hasReturned;
    @name("c.val_0") bit<8> val;
    @name("c.hasReturned") bool hasReturned_0;
    @hidden action issue2175l3() {
        val = 8w1;
        hasReturned_0 = true;
    }
    @hidden action act() {
        hasReturned = false;
        val = v;
        hasReturned_0 = false;
    }
    @hidden action issue2175l6() {
        val = 8w2;
    }
    @hidden action issue2175l14() {
        v = 8w1;
        hasReturned = true;
    }
    @hidden action act_0() {
        v = val;
    }
    @hidden action issue2175l17() {
        v = 8w2;
    }
    apply {
        act();
        if (v == 8w0) {
            issue2175l3();
        }
        if (hasReturned_0) {
            ;
        } else {
            issue2175l6();
        }
        act_0();
        if (val == 8w0) {
            issue2175l14();
        }
        if (hasReturned) {
            ;
        } else {
            issue2175l17();
        }
    }
}

control e(inout bit<8> _v);
package top(e _e);
top(c()) main;

