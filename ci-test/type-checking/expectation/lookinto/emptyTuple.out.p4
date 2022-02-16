/petr4/ci-test/type-checking/testdata/p4_16_samples/emptyTuple.p4
\n
typedef tuple<> emptyTuple;

control c(out bool b) {
    apply {
        emptyTuple t = {};
        if (t == {})
           b = true;
        else
           b = false;
    }
}

control e(out bool b);
package top(e _e);

top(c()) main;
************************\n******** petr4 type checking result: ********\n************************\n
typedef tuple<> emptyTuple;
control c(out bool b) {
  apply {
    emptyTuple t = {};
    if (t=={}) 
      b = true;
      else
        b = false;
  }
}
control e (out bool b);
package top (e _e);
top(c()) main;

************************\n******** p4c type checking result: ********\n************************\n
