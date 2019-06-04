// Comment out each line of the below function to
// see the chekcer reject each binary operation.
void fun(in int<32> ix,  in int<32> iy, in bool bx, in bool by,
         out int<32> io, out bool bo){
    io = ix + by;
    io = bx || iy;
    bo = ix + iy;
    io = bx && by;
    bo = bx || iy;
}
