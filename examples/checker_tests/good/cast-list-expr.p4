struct S {
    bit<4> a;
}

void f() {
    S z = {a=6};            // Valid
    S z = (S) {a=6};        // Valid
    S z = {6};              // Valid
    S z =  (S) {6};         // Invalid

    // Valid comparison of the equality of two structs; b = true
    bool b = (S) {a=0xF6} == {a=0x26};
    // Invalid in Petr4 and BMV2
    bool b = (S) {6} == {6};
    // Valid comparison of the equality of two lists; b = false
    bool b = {0xF6} == {0x26};
}