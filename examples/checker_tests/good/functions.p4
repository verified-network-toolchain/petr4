// Program with function declarations and function calls.

int<32> addr(in int<32> x, in int<32> y) {
  return x + y;
}

void addout(in int<32> x, in int<32> y, out int<32> z){
    z = addr(x,y);
}

void name_addr(in int<32> a, in int<32> b, out int<32> c){
    c = addr(y=a,x=b);
}

void name_out(in int<32> a, in int<32> b, out int<32> c){
    addout(y=a,z=c,x=b);
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

void caller(in bool pred1, in bool pred2, in int<32> x, in int<32> y, out int<32> res1, out int<32> res2){
    bool_fun(pred1,x,y,res1);
    bool_fun(a=x,ans=res2,b=y,cond=pred1);
    bool_fun(pred1 && pred2,x,y,res1);
    bool_fun(a=x,ans=res2,b=y,cond=pred1 || pred2);
}

// Should type check but arbitray
// width int types are rejected by petr4.ml
// bit<32> caster(in int x, in bit<32> y){
//     return x + y;
// }
