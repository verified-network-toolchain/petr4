// Program with type declarations Headers,
// Enums, Header Unions, Structs, and Errors

header my_header {
    bit    g1;
    bit<2> g2;
    bit<3> g3;
}

header hdr {
    bit<32> a;
    bit<32> b;
    bit<32> c;
}

enum Choice {
    First,
    Second
}

header_union my_union
{
    my_header h1;
    my_header h2;
    hdr       h3;
}

struct str
{
     my_header hdr;
     my_union  unn;
     bit<32>     dt;
     Choice  choice;
}
