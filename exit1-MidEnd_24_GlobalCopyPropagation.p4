control ctrl() {
    bool hasExited;
    @name("ctrl.a") bit<32> a_0;
    apply {
        hasExited = false;
        a_0 = 32w0;
        if (a_0 == 32w0) {
            hasExited = true;
        } else {
            hasExited = true;
        }
    }
}

control noop();
package p(noop _n);
p(ctrl()) main;

