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

const my_struct s1 = {0,false};
const my_struct s2 = {1, true};
const my_other_struct s3 = {s1, s2};
const my_other_struct s4 = {{0,false},{1,true}};

const bool a = error.NoError != error.MyError;
const bool b = s3.first != s3.second;
const bool c = s3 == s4;

package EmptyPackage();
EmptyPackage() main;
