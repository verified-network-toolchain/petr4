control c() {
    @name("x") bit<32> x_0;
    @name("a") action a_0(@name("arg") inout bit<32> arg_0) {
        bool hasReturned = false;
        arg_0 = 32w1;
        {
            hasReturned = true;
        }
    }
    apply {
        a_0(x_0);
    }
}

control proto();
package top(proto p);
top(c()) main;

