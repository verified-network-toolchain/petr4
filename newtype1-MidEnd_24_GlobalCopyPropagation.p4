typedef bit<9> Narrow_t;
typedef Narrow_t Narrow;
typedef bit<32> Wide_t;
typedef Wide_t Wide;
control c(out bool b) {
    @name("c.x") Wide x_0;
    @name("c.y") Narrow y_0;
    apply {
        x_0 = 32w3;
        y_0 = (Narrow_t)(Wide_t)x_0;
        b = y_0 == 9w10;
    }
}

control ctrl(out bool b);
package top(ctrl _c);
top(c()) main;

