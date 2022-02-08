extern void __semaphore_write(in bit<32> data=0);
control c() {
    @hidden action issue2599l5() {
        __semaphore_write(data = 32w0);
        __semaphore_write(data = 32w0);
    }
    apply {
        issue2599l5();
    }
}

control proto();
package top(proto p);
top(c()) main;

