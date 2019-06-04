/*
An example of type inference with function calls.
*/

#include <core.p4>
#include <v1model.p4>

parser Prs<T>(packet_in b, out T result);
control Pipe<T>(out T data);
package Switch<T>(Prs<T> p, Pipe<T> map);

parser P(packet_in b, out bit<32> index) {
     state start
    {
        transition accept;
    }
}
control Pipe1(out bit<32> data) {
    apply {
        data = 1;
    }
}
control Pipe2(out bit<8> data) {
    apply {
        data = 1;
    }
}

Switch(P(), Pipe2()) m;
