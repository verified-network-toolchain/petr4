control ingress(inout bit<8> a) {
    @hidden action issue23351l3() {
        a = 8w0;
    }
    apply {
        issue23351l3();
    }
}

control i(inout bit<8> a);
package top(i _i);
top(ingress()) main;

