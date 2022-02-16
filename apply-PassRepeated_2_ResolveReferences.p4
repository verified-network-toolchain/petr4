control noargs();
control p() {
    apply {
    }
}

control q() {
    apply {
        {
        }
    }
}

package m(noargs n);
m(q()) main;

