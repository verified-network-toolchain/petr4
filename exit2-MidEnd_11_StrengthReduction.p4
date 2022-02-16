control ctrl(out bit<32> c) {
    bool hasExited;
    @name("ctrl.a") bit<32> a_0;
    @name("ctrl.e") action e() {
        hasExited = true;
    }
    @name("ctrl.e") action e_1() {
        hasExited = true;
    }
    apply {
        hasExited = false;
        a_0 = 32w0;
        c = 32w2;
        if (a_0 == 32w0) {
            e();
        } else {
            e_1();
        }
        if (!hasExited) {
            c = 32w5;
        }
    }
}

control noop(out bit<32> c);
package p(noop _n);
p(ctrl()) main;

