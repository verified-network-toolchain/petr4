control ctrl(out bit<32> c) {
    bool hasExited;
    @name("ctrl.e") action e() {
        hasExited = true;
    }
    @name("ctrl.e") action e_1() {
        hasExited = true;
    }
    apply {
        hasExited = false;
        c = 32w2;
        e();
        if (!hasExited) {
            c = 32w5;
        }
    }
}

control noop(out bit<32> c);
package p(noop _n);
p(ctrl()) main;

