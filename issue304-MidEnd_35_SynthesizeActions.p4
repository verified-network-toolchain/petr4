control t(inout bit<32> b) {
    @hidden action issue304l19() {
        b = b + 32w1;
        b = b + 32w1;
    }
    apply {
        issue304l19();
    }
}

control cs(inout bit<32> arg);
package top(cs _ctrl);
top(t()) main;

