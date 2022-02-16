control ctrl(out bit<32> c) {
    bool hasExited;
    @name("ctrl.e") action e() {
        hasExited = true;
    }
    @name("ctrl.e") action e_1() {
        hasExited = true;
    }
    @hidden action exit2l31() {
        hasExited = false;
        c = 32w2;
    }
    @hidden action exit2l41() {
        c = 32w5;
    }
    apply {
        exit2l31();
        e();
        if (hasExited) {
            ;
        } else {
            exit2l41();
        }
    }
}

control noop(out bit<32> c);
package p(noop _n);
p(ctrl()) main;

