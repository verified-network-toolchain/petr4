struct tuple_0 {
}

typedef tuple_0 emptyTuple;
control c(out bool b) {
    @name("c.t") emptyTuple t_0;
    apply {
        t_0 = (tuple_0){};
        if (t_0 == {  }) {
            b = true;
        } else {
            b = false;
        }
    }
}

control e(out bool b);
package top(e _e);
top(c()) main;

