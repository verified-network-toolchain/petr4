extern counter {
}

parser p() {
    bit<16> counter;
    state start {
        counter = (bit<16>)16w0;
        transition accept;
    }
}

