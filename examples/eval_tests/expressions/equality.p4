#include <core.p4>

error { MyError };

struct my_struct {
    bit first;
    bool second;
}

struct my_other_struct {
    my_struct first;
    my_struct second;
}

my_other_struct f(in my_other_struct s) {
    s.first = {1, true};
    s.second = {0, false};
    s.first.first = 0;
    s.first.second = false;
    s.second.first = 1;
    s.second.second = true;
    return s;
}

const my_struct s1 = {0,false};
const my_struct s2 = {1, true};
const bool test1 = s1.first;
const bit test2 = s1.second;
const bool test3 = s2.first;
const bit test4 = s2.second;
const my_other_struct s3 = {s1, s2};
const my_other_struct s4 = f(s3);
const my_other_struct s5 = {{0,false}, {1,true}};

const bool a = error.NoError != error.MyError;
const bool b = s3.first != s3.second;
const bool c = s3 == s4;
const bool d = s4 == s5;

package EmptyPackage();
EmptyPackage() main;
