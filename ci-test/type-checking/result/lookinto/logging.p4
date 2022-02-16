/petr4/ci-test/type-checking/testdata/p4_16_samples/logging.p4
\n
#include <v1model.p4>

control c(inout bit<32> x, inout bit<32> y) {
    action a(inout bit<32> b, inout bit<32> d) {
    	log_msg("Logging message.");
        log_msg("Logging values {} and {}", {b, d});
    }
    table t {
        actions = { a(x,y); }
    }
    apply {
        t.apply();
    }
}

control e(inout bit<32> x, inout bit<32> y);
package top(e _e);

top(c()) main;
************************\n******** petr4 type checking result: ********\n************************\n
