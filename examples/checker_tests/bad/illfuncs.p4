// Comment out this whole function to
// examine the rest of the program
bool addr(in int<32> x, in int<32> y) {
  return x + y;
}

// Comment out this whole function to
// examine the rest of the program
// When this function fails to type check it will give:
//             (Failure Unimplemented)
// This is due to our need to implement better exceptions
// for binary operations that cannot cast the types of operands.
void add_bool(in int<32> x, in bool y, out int<32> ans){
    ans = x + y;
}

// Comment out this whole function to
// examine the rest of the program
void bad_return(in int<32> x, in int<32> y) {
  return x + y;
}

int<32> bool_fun(in bool cond, in int<32> a, in int<32> b, out int<32> ans){
    if (cond) {
        ans = a;
        return a;
    } else {
        ans = b;
        return b;
    }
}

// Comment out each line of this function to see each
// the checker reject each ill-typed function call.
function call the type checker rejects.
void caller(in bool pred1, in bool pred2, in int<32> x, in int<32> y, out int<32> res1, out int<32> res2){
    bool_fun(x,pred1,y,res1);
    bool_fun(a=x,ans=res1,b=y,cond=pred1);
    bool_fun(pred1 && y,x,y,res1);
    bool_fun(a=x,ans=res2,b=y,cond=x || pred2);
}
