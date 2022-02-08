control c() {
    @name("x") bit<32> x;
    @name("hasReturned") bool hasReturned_0;
    @name("arg") bit<32> arg;
    @name("a") action a_0() {
        arg = x;
        hasReturned_0 = false;
        arg = 32w1;
        {
            hasReturned_0 = true;
        }
        x = arg;
    }
    apply {
        a_0();
    }
}

control proto();
package top(proto p);
top(c()) main;

