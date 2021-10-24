
/// Register
extern Register<T, I> {
    /// Instantiate an array of <size> registers. The initial value is
    /// undefined.
    Register(bit<32> size);

    /// Initialize an array of <size> registers and set their value to
    /// initial_value.
    Register(bit<32> size, T initial_value);

    /// Return the value of register at specified index.
    T read(in I index);

    /// Write value to register at specified index.
    void write(in I index, in T value);
}

// This is implemented using an experimental feature in p4c and subject to
// change. See https://github.com/p4lang/p4-spec/issues/561
extern RegisterAction<T, I, U> {
    RegisterAction(Register<T, I> reg);

    U execute(in I index); /* {
        U rv;
        T value = reg.read(index);
        apply(value, rv);
        reg.write(index, value);
        return rv;
    } */
    // Apply the implemented abstract method using an index that increments each
    // time. This method is useful for stateful logging.
    U execute_log();

    // Abstract method that needs to be implemented when RegisterAction is
    // instantiated.
    // @param value : register value.
    // @param rv : return value.
    @synchronous(execute, execute_log)
    abstract void apply(inout T value, @optional out U rv);

    U predicate(@optional in bool cmplo,
                @optional in bool cmphi); /* return the 4-bit predicate value */
}


control c(inout bit<16> index) {
    //Register<bit<32>,_>(32w65536, 0) reg;

    Register<bit<32>,bit<16>>(32w65536, 0) reg;

    //RegisterAction<bit<32>, _, bit<32>>(reg) regact = {
    RegisterAction<bit<32>, bit<16>, bit<32>>(reg) regact = {
        void apply(inout bit<32> value, out bit<32> rv) {
            rv = value;
            value = value + 1;
        }
    };

    apply {
        regact.execute(index);
    }
}

control ctr(inout bit<16> x);
package top(ctr ctrl);

top(c()) main;
