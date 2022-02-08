control c(out bit<32> y) {
    bit<32> x = (bit<32>)32w10;
    apply {
        y = (bit<32>)x;
    }
}

