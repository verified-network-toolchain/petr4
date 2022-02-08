extern bit<16> get<D>(in D data);
header H {
    bit<8>      len;
    @length((bit<32>)len * 32w8 - 32w16) 
    varbit<304> data;
}

control x() {
    H h;
    apply {
        get<tuple<H>>({ h });
    }
}

