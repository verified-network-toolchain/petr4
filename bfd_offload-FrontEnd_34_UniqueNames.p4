extern BFD_Offload {
    BFD_Offload(bit<16> size);
    void setTx(in bit<16> index, in bit<8> data);
    bit<8> getTx(in bit<16> index);
    abstract void on_rx(in bit<16> index);
    abstract bool on_tx(in bit<16> index);
}

BFD_Offload(16w32768) bfd_session_liveness_tracker = {
    void on_rx(in bit<16> index) {
        this.setTx(index, 8w0);
    }
    bool on_tx(in bit<16> index) {
        @name("c") bit<8> c_0 = this.getTx(index) + 8w1;
        if (c_0 >= 8w4) {
            return true;
        } else {
            this.setTx(index, c_0);
            return false;
        }
    }
};

