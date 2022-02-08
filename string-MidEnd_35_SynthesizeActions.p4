extern void log(string s);
control c() {
    @hidden action string5() {
        log("This is a message");
    }
    apply {
        string5();
    }
}

control e();
package top(e _e);
top(c()) main;

