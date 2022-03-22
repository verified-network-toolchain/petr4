/petr4/ci-test/type-checking/testdata/p4_16_samples/string.p4
\n
extern void log(string s);

control c() {
    apply {
        log("This is a message");
    }
}

control e();
package top(e _e);

top(c()) main;
************************\n******** petr4 type checking result: ********\n************************\n
extern void log(string s);
control c() {
  apply {
    log("This is a message");
  }
}
control e ();
package top (e _e);
top(c()) main;

************************\n******** p4c type checking result: ********\n************************\n
