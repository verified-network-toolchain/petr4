/*
An example of type inference with function calls.
*/

// #include <core.p4>
// #include <v1model.p4>

T fun<T>(in T x){
    return x;
}


int<8> f(in int<8> y){
    return y;
}




void stuff(){
    int<8> a = f(6);
    f(6);
    /* Needs type argument for function call. */
    fun(true);
    // int<32> b = fun<int<32>>(5);

}

