parser p() {
    state start {
        {
            bit<16> retval = (bit<16>)16w0;
        }
        {
            bit<16> retval = (bit<16>)16w1;
        }
        transition accept;
    }
}

